// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity =0.8.18;

import "solmate/tokens/ERC20.sol";
import "solmate/utils/SafeTransferLib.sol";
import "solmate/utils/FixedPointMathLib.sol";
import "./interfaces/IUniswapV2.sol";
import "./interfaces/IUniswapV3.sol";
import "./interfaces/IUniswapV4.sol";
import "./interfaces/IPancakeInfinity.sol";

/// @notice Result codes reported to off-chain callers.
/// @dev    INDICES ARE PART OF THE PUBLIC ABI. Members are never reordered and removed
///         members leave their slot reserved, so every code below keeps the index it has
///         always had. New codes may only be appended.
enum ErrorCode {
    NoError,
    /// @dev Reserved. Was `SameToken`, which cannot occur now that the caller names the
    ///      pool instead of a token pair.
    Deprecated_SameToken,
    /// @dev The pool cannot be measured against: a zero or non-pool address, a pool that
    ///      does not list the token, or a pool id that is unknown or never initialized
    ///      (typically a stale id from the indexer). Occupies the slot formerly called
    ///      `PairLookupFailed`, which meant the same thing.
    PoolInvalid,
    InsufficientOutputAmount,
    InsufficientLiquidity,
    TransferFailed1, // token -> this contract, i.e. the flash loan itself failed
    TransferFailed2, // this contract -> pool
    TransferFailed3, // this contract -> the sell fee reference recipient
    Others
}

/// @notice Fee measurement for a single token.
/// @dev    Field names and order are part of the public ABI and are unchanged.
///         `sellFeeBpsForFactory` is the sell fee measured against
///         `TokenValidator.sellFeeReferenceRecipient()`.
struct TokenFees {
    uint256 buyFeeBpsForPair;
    uint256 sellFeeBpsForPair;
    uint256 sellFeeBpsForFactory;
    ErrorCode[] errCode;
}

/// @notice A Uniswap V4 `PoolKey`: five words, hashed to give the pool id.
struct V4PoolKey {
    address currency0;
    address currency1;
    uint24 fee;
    int24 tickSpacing;
    address hooks;
}

/// @notice A PancakeSwap Infinity `PoolKey`: six words, in Infinity's own field order.
/// @dev    `parameters` packs the pool-type specific data - for CL, the hook registration
///         bitmap in bits [0,16) and the tick spacing in bits [16,40).
struct InfinityPoolKey {
    address currency0;
    address currency1;
    address hooks;
    address poolManager;
    uint24 fee;
    bytes32 parameters;
}

/// @notice Everything that differs per chain.
/// @dev    V2 and V3 need nothing here: those pools are named directly and expose their own
///         `token0`/`token1`, so the same bytecode measures any V2/V3 style pool on any
///         chain and any fork. Only the singleton designs need addresses, because the
///         contract that custodies the tokens is not the pool.
struct ValidatorConfig {
    /// @dev The neutral, non-pool address the sell fee is measured against. Must be set:
    ///      `address(0)` is a burn address that many tokens reject, which would show up as
    ///      a token defect rather than a configuration mistake.
    address sellFeeReferenceRecipient;
    /// @dev Uniswap V4: the singleton that custodies currencies and answers `extsload`.
    address poolManagerV4;
    /// @dev Uniswap V4: the position manager, used only as a pool id -> key registry.
    address positionManagerV4;
    /// @dev Storage slot of `pools` inside the V4 `PoolManager` (6 in Uniswap V4).
    uint256 v4PoolsSlot;
    /// @dev PancakeSwap Infinity: the Vault, which custodies every currency.
    address infinityVault;
    /// @dev PancakeSwap Infinity: the CL pool manager, the registry for CL pools.
    address infinityCLPoolManager;
}

/// @title  TokenValidator
/// @notice Measures the buy/sell fee-on-transfer tax of an ERC20 by flash-borrowing it from
///         a pool, immediately transferring it back, and reverting so nothing is settled.
/// @dev    The caller names the pool. This contract does no discovery, which is deliberate:
///         a fee tier table cannot enumerate Uniswap V4 or PancakeSwap Infinity, whose LP
///         fee is a free 24-bit value - the live BNB/CAKE Infinity pool charges 335 - so any
///         guessed table produces false "no pool" answers. The off-chain indexer already
///         knows the pools; it passes them in.
///
///         Four pool shapes are supported, and the measurement is identical in all four -
///         only the way the loan is opened differs:
///         - V2: `pair.swap(...)` with a payload.
///         - V3: `pool.flash(...)`.
///         - V4: `poolManager.unlock(...)` then `take(...)` on the singleton.
///         - Infinity CL: `vault.lock(...)` then `vault.take(...)`.
contract TokenValidator {
    using SafeTransferLib for ERC20;
    using FixedPointMathLib for uint256;

    /*//////////////////////////////////////////////////////////////
                                  ERRORS
    //////////////////////////////////////////////////////////////*/

    error PoolInvalid();
    error InsufficientLiquidity();
    error NativeCurrencyNotSupported();
    error ArrayLengthMismatch();
    error SelfCallOnly();
    error UnexpectedCallback();
    error MissingSellFeeReferenceRecipient();

    /*//////////////////////////////////////////////////////////////
                                CONSTANTS
    //////////////////////////////////////////////////////////////*/

    uint256 internal constant BPS = 10_000;

    /// @dev `bytes4(keccak256("Error(string)"))`.
    bytes4 internal constant ERROR_STRING_SELECTOR = 0x08c379a0;

    /// @dev `abi.encode(TokenFees)` sizes: 32 (outer offset) + 128 (4 head words)
    ///      + 32 (array length) + 32 * errCode.length. `errCode` is always 1 or 2 long.
    uint256 internal constant ENCODED_TOKEN_FEES_ONE_ERROR = 224;
    uint256 internal constant ENCODED_TOKEN_FEES_TWO_ERRORS = 256;

    /*//////////////////////////////////////////////////////////////
                             CHAIN CONFIGURATION
    //////////////////////////////////////////////////////////////*/

    address public immutable sellFeeReferenceRecipient;
    address public immutable poolManagerV4;
    address public immutable positionManagerV4;
    uint256 public immutable v4PoolsSlot;
    address public immutable infinityVault;
    address public immutable infinityCLPoolManager;

    constructor(ValidatorConfig memory config) {
        if (config.sellFeeReferenceRecipient == address(0)) revert MissingSellFeeReferenceRecipient();

        sellFeeReferenceRecipient = config.sellFeeReferenceRecipient;
        poolManagerV4 = config.poolManagerV4;
        positionManagerV4 = config.positionManagerV4;
        v4PoolsSlot = config.v4PoolsSlot;
        infinityVault = config.infinityVault;
        infinityCLPoolManager = config.infinityCLPoolManager;
    }

    /*//////////////////////////////////////////////////////////////
                        V2 / V3 - POOL NAMED DIRECTLY
    //////////////////////////////////////////////////////////////*/

    /// @notice Measure `token` using a Uniswap V2 style pair.
    /// @dev    Needs no factory and no configuration: the pair itself says which side the
    ///         token is on. A pair no factory lists - a fork, a custom deployment - works.
    function validateV2ByPool(address token, address pair, uint256 amountToBorrow) public returns (TokenFees memory) {
        _requireMeasurableToken(token);
        return _normalize(_probeUniswapV2Pool(token, pair, amountToBorrow));
    }

    /// @notice Measure `token` using a Uniswap V3 style pool.
    function validateV3ByPool(address token, address pool, uint256 amountToBorrow) public returns (TokenFees memory) {
        _requireMeasurableToken(token);
        return _normalize(_probeUniswapV3Pool(token, pool, amountToBorrow));
    }

    /*//////////////////////////////////////////////////////////////
                       UNISWAP V4 - POOL NAMED BY ID
    //////////////////////////////////////////////////////////////*/

    /// @notice Measure `token` using the Uniswap V4 pool with this id.
    /// @dev    The key is read back from the position manager's registry. That registry only
    ///         covers pools that have had a position minted through it; when it misses, use
    ///         `validateV4ByPoolKey`, which needs no registry at all.
    function validateV4ByPoolId(address token, bytes32 poolId, uint256 amountToBorrow)
        public
        returns (TokenFees memory)
    {
        _requireMeasurableToken(token);

        (address currency0, address currency1,,,) = v4PoolKey(poolId);
        if (token != currency0 && token != currency1) revert PoolInvalid();

        return _normalize(_probeUniswapV4(token, poolId, amountToBorrow));
    }

    /// @notice Measure `token` using a Uniswap V4 pool named by its full key.
    /// @dev    The pool id is derived from the key, so membership is guaranteed by
    ///         construction and no registry is consulted.
    function validateV4ByPoolKey(address token, V4PoolKey calldata key, uint256 amountToBorrow)
        public
        returns (TokenFees memory)
    {
        _requireMeasurableToken(token);
        if (token != key.currency0 && token != key.currency1) revert PoolInvalid();

        return _normalize(_probeUniswapV4(token, v4PoolId(key), amountToBorrow));
    }

    /*//////////////////////////////////////////////////////////////
                     INFINITY CL - POOL NAMED BY ID
    //////////////////////////////////////////////////////////////*/

    /// @notice Measure `token` using the PancakeSwap Infinity CL pool with this id.
    /// @dev    Infinity records the reverse mapping in the pool manager itself, so the key
    ///         is recoverable for every initialized pool.
    function validateInfinityCLByPoolId(address token, bytes32 poolId, uint256 amountToBorrow)
        public
        returns (TokenFees memory)
    {
        _requireMeasurableToken(token);

        (address currency0, address currency1,,,,) = infinityCLPoolKey(poolId);
        if (token != currency0 && token != currency1) revert PoolInvalid();

        return _normalize(_probeInfinityCL(token, poolId, amountToBorrow));
    }

    /// @notice Measure `token` using an Infinity CL pool named by its full key.
    function validateInfinityCLByPoolKey(address token, InfinityPoolKey calldata key, uint256 amountToBorrow)
        public
        returns (TokenFees memory)
    {
        _requireMeasurableToken(token);
        if (token != key.currency0 && token != key.currency1) revert PoolInvalid();

        return _normalize(_probeInfinityCL(token, infinityPoolId(key), amountToBorrow));
    }

    /*//////////////////////////////////////////////////////////////
                                  BATCH
    //////////////////////////////////////////////////////////////*/

    /// @notice One result per token; `pools[i]` is the pool used for `tokens[i]`.
    /// @dev    A failure is reported as an `ErrorCode` rather than reverting, so one bad
    ///         token never fails the batch.
    function batchValidateV2ByPools(
        address[] calldata tokens,
        address[] calldata pools,
        uint256 amountToBorrow,
        uint256 gasLimit
    ) public returns (TokenFees[] memory results) {
        if (tokens.length != pools.length) revert ArrayLengthMismatch();

        results = new TokenFees[](tokens.length);
        for (uint256 i; i < tokens.length; ++i) {
            try this.validateV2ByPool{gas: gasLimit}(tokens[i], pools[i], amountToBorrow) returns (
                TokenFees memory measuredFees
            ) {
                results[i] = measuredFees;
            } catch (bytes memory reason) {
                results[i] = _failure(reason);
            }
        }
    }

    /// @notice One result per token; `pools[i]` is the pool used for `tokens[i]`.
    function batchValidateV3ByPools(
        address[] calldata tokens,
        address[] calldata pools,
        uint256 amountToBorrow,
        uint256 gasLimit
    ) public returns (TokenFees[] memory results) {
        if (tokens.length != pools.length) revert ArrayLengthMismatch();

        results = new TokenFees[](tokens.length);
        for (uint256 i; i < tokens.length; ++i) {
            try this.validateV3ByPool{gas: gasLimit}(tokens[i], pools[i], amountToBorrow) returns (
                TokenFees memory measuredFees
            ) {
                results[i] = measuredFees;
            } catch (bytes memory reason) {
                results[i] = _failure(reason);
            }
        }
    }

    /// @notice One result per token; `poolIds[i]` is the pool used for `tokens[i]`.
    function batchValidateV4ByPoolIds(
        address[] calldata tokens,
        bytes32[] calldata poolIds,
        uint256 amountToBorrow,
        uint256 gasLimit
    ) public returns (TokenFees[] memory results) {
        if (tokens.length != poolIds.length) revert ArrayLengthMismatch();

        results = new TokenFees[](tokens.length);
        for (uint256 i; i < tokens.length; ++i) {
            try this.validateV4ByPoolId{gas: gasLimit}(tokens[i], poolIds[i], amountToBorrow) returns (
                TokenFees memory measuredFees
            ) {
                results[i] = measuredFees;
            } catch (bytes memory reason) {
                results[i] = _failure(reason);
            }
        }
    }

    /// @notice One result per token; `poolIds[i]` is the pool used for `tokens[i]`.
    function batchValidateInfinityCLByPoolIds(
        address[] calldata tokens,
        bytes32[] calldata poolIds,
        uint256 amountToBorrow,
        uint256 gasLimit
    ) public returns (TokenFees[] memory results) {
        if (tokens.length != poolIds.length) revert ArrayLengthMismatch();

        results = new TokenFees[](tokens.length);
        for (uint256 i; i < tokens.length; ++i) {
            try this.validateInfinityCLByPoolId{gas: gasLimit}(tokens[i], poolIds[i], amountToBorrow) returns (
                TokenFees memory measuredFees
            ) {
                results[i] = measuredFees;
            } catch (bytes memory reason) {
                results[i] = _failure(reason);
            }
        }
    }

    /*//////////////////////////////////////////////////////////////
                              POOL KEY LOOKUP
    //////////////////////////////////////////////////////////////*/

    /// @notice Reads a Uniswap V4 pool key back from the position manager's registry.
    /// @dev    Keyed by the first 25 bytes of the pool id, which is how V4 stores it.
    function v4PoolKey(bytes32 poolId)
        public
        view
        returns (address currency0, address currency1, uint24 fee, int24 tickSpacing, address hooks)
    {
        if (positionManagerV4 == address(0)) revert PoolInvalid();

        (bool ok, bytes memory data) = positionManagerV4.staticcall(
            abi.encodeWithSelector(IUniswapV4PositionManager.poolKeys.selector, bytes25(poolId))
        );
        if (!ok || data.length < 160) revert PoolInvalid();

        (currency0, currency1, fee, tickSpacing, hooks) = abi.decode(data, (address, address, uint24, int24, address));

        // currency0 may legitimately be address(0) - that is the native currency. An unknown
        // id yields an all-zero record, which currency1 detects.
        if (currency1 == address(0)) revert PoolInvalid();
    }

    /// @notice Reads an Infinity CL pool key back from the pool manager.
    function infinityCLPoolKey(bytes32 poolId)
        public
        view
        returns (
            address currency0,
            address currency1,
            address hooks,
            address poolManager,
            uint24 fee,
            bytes32 parameters
        )
    {
        if (infinityCLPoolManager == address(0)) revert PoolInvalid();

        (bool ok, bytes memory data) = infinityCLPoolManager.staticcall(
            abi.encodeWithSelector(IInfinityCLPoolManager.poolIdToPoolKey.selector, poolId)
        );
        if (!ok || data.length < 192) revert PoolInvalid();

        (currency0, currency1, hooks, poolManager, fee, parameters) =
            abi.decode(data, (address, address, address, address, uint24, bytes32));

        // An unknown id yields an all-zero record; a real one always names its pool manager.
        if (poolManager == address(0)) revert PoolInvalid();
    }

    /// @notice `PoolId.toId()`: keccak of the five `PoolKey` words.
    function v4PoolId(V4PoolKey calldata key) public pure returns (bytes32) {
        return keccak256(abi.encode(key.currency0, key.currency1, key.fee, key.tickSpacing, key.hooks));
    }

    /// @notice `PoolIdLibrary.toId()`: keccak of the six Infinity `PoolKey` words.
    function infinityPoolId(InfinityPoolKey calldata key) public pure returns (bytes32) {
        return keccak256(abi.encode(key.currency0, key.currency1, key.hooks, key.poolManager, key.fee, key.parameters));
    }

    /*//////////////////////////////////////////////////////////////
                                  PROBES
    //////////////////////////////////////////////////////////////*/

    /// @dev V2: a `swap` with a non-empty payload is a flash swap. The pair sends the tokens
    ///      first and calls us back before checking repayment.
    function _probeUniswapV2Pool(address token, address pair, uint256 amountToBorrow)
        internal
        returns (TokenFees memory measured)
    {
        (uint256 amount0Out, uint256 amount1Out) = _borrowAmounts(token, pair, amountToBorrow);
        bytes memory payload = _encodeProbe(pair, token, amountToBorrow);

        // The measurement always arrives as revert data; a swap that returns normally means
        // the callback never ran, and `measured` is left at its zero value.
        try IUniswapV2Pair(pair).swap(amount0Out, amount1Out, address(this), payload) {}
        catch (bytes memory reason) {
            return _parseRevertReason(reason);
        }
    }

    /// @dev V3: `flash` lends the requested amounts and calls us back before requiring
    ///      repayment plus the flash fee.
    function _probeUniswapV3Pool(address token, address pool, uint256 amountToBorrow)
        internal
        returns (TokenFees memory measured)
    {
        (uint256 amount0, uint256 amount1) = _borrowAmounts(token, pool, amountToBorrow);
        bytes memory payload = _encodeProbe(pool, token, amountToBorrow);

        try IUniswapV3Pool(pool).flash(address(this), amount0, amount1, payload) {}
        catch (bytes memory reason) {
            return _parseRevertReason(reason);
        }
    }

    /// @dev V4: there is no pair contract. Every currency sits in the singleton, so the
    ///      amount that can be borrowed is bounded by the singleton's balance rather than by
    ///      one pool's reserves.
    function _probeUniswapV4(address token, bytes32 poolId, uint256 amountToBorrow)
        internal
        returns (TokenFees memory measured)
    {
        address manager = poolManagerV4;
        if (manager == address(0)) revert PoolInvalid();
        if (!_isV4PoolInitialized(poolId)) revert PoolInvalid();
        if (ERC20(token).balanceOf(manager) < amountToBorrow) revert InsufficientLiquidity();

        bytes memory payload = _encodeProbe(manager, token, amountToBorrow);

        // The result is carried by the revert, which also unwinds the flash accounting so no
        // currency delta is ever left to settle.
        try IUniswapV4PoolManager(manager).unlock(payload) returns (bytes memory) {}
        catch (bytes memory reason) {
            return _parseRevertReason(reason);
        }
    }

    /// @dev Infinity CL: same shape as V4, but the Vault is what custodies the currencies
    ///      and what has to be locked, while the pool registry lives in the CL pool manager.
    function _probeInfinityCL(address token, bytes32 poolId, uint256 amountToBorrow)
        internal
        returns (TokenFees memory measured)
    {
        address vault = infinityVault;
        if (vault == address(0)) revert PoolInvalid();
        if (!_isInfinityCLPoolInitialized(poolId)) revert PoolInvalid();
        if (ERC20(token).balanceOf(vault) < amountToBorrow) revert InsufficientLiquidity();

        bytes memory payload = _encodeProbe(vault, token, amountToBorrow);

        try IInfinityVault(vault).lock(payload) returns (bytes memory) {}
        catch (bytes memory reason) {
            return _parseRevertReason(reason);
        }
    }

    /*//////////////////////////////////////////////////////////////
                             POOL INSPECTION
    //////////////////////////////////////////////////////////////*/

    /// @dev Resolves which side of `pool` holds `token` and turns that into the pool's
    ///      (amount0, amount1) borrow arguments. Reverts unless `pool` really is a pool that
    ///      lists `token`, which is what makes a caller-supplied pool address safe to use.
    function _borrowAmounts(address token, address pool, uint256 amountToBorrow)
        internal
        view
        returns (uint256 amount0, uint256 amount1)
    {
        if (pool == address(0)) revert PoolInvalid();

        if (token == _readPoolToken(pool, IUniswapV2Pair.token0.selector)) return (amountToBorrow, 0);
        if (token != _readPoolToken(pool, IUniswapV2Pair.token1.selector)) revert PoolInvalid();
        return (0, amountToBorrow);
    }

    function _readPoolToken(address pool, bytes4 selector) internal view returns (address poolToken) {
        (bool ok, bytes memory returnData) = pool.staticcall(abi.encodeWithSelector(selector));
        if (!ok || returnData.length < 32) revert PoolInvalid();

        poolToken = abi.decode(returnData, (address));
    }

    /// @dev A V4 pool is initialized iff the `sqrtPriceX96` in its `slot0` is non-zero.
    ///      `slot0` is the first word of `pools[poolId]`.
    function _isV4PoolInitialized(bytes32 poolId) internal view returns (bool) {
        bytes32 stateSlot = keccak256(abi.encodePacked(poolId, v4PoolsSlot));

        (bool ok, bytes memory returnData) =
            poolManagerV4.staticcall(abi.encodeWithSelector(IUniswapV4PoolManager.extsload.selector, stateSlot));
        if (!ok || returnData.length < 32) return false;

        return uint160(uint256(abi.decode(returnData, (bytes32)))) != 0;
    }

    /// @dev Infinity exposes a real getter, so no storage slot has to be guessed.
    function _isInfinityCLPoolInitialized(bytes32 poolId) internal view returns (bool) {
        if (infinityCLPoolManager == address(0)) return false;

        (bool ok, bytes memory returnData) =
            infinityCLPoolManager.staticcall(abi.encodeWithSelector(IInfinityCLPoolManager.getSlot0.selector, poolId));
        if (!ok || returnData.length < 32) return false;

        return abi.decode(returnData, (uint160)) != 0;
    }

    /// @dev The payload carries the pool address so every callback can authenticate its
    ///      caller, and the borrowed token so no callback has to guess it from amounts.
    function _encodeProbe(address pool, address token, uint256 amountToBorrow) internal view returns (bytes memory) {
        return abi.encode(pool, token, ERC20(token).balanceOf(address(this)), amountToBorrow);
    }

    /*//////////////////////////////////////////////////////////////
                                CALLBACKS
    //////////////////////////////////////////////////////////////*/

    /// @notice PancakeSwap V2 flash swap callback.
    function pancakeCall(address, uint256, uint256, bytes calldata data) external {
        _onFlashLoanReceived(data);
    }

    /// @notice Uniswap V2 flash swap callback.
    function uniswapV2Call(address, uint256, uint256, bytes calldata data) external {
        _onFlashLoanReceived(data);
    }

    /// @notice PancakeSwap V3 flash callback.
    function pancakeV3FlashCallback(uint256, uint256, bytes calldata data) external {
        _onFlashLoanReceived(data);
    }

    /// @notice Uniswap V3 flash callback.
    function uniswapV3FlashCallback(uint256, uint256, bytes calldata data) external {
        _onFlashLoanReceived(data);
    }

    /// @notice Uniswap V4 unlock callback. Unlike V2/V3 the tokens are not pushed to us, we
    ///         pull them with `take` while the manager is unlocked.
    function unlockCallback(bytes calldata data) external returns (bytes memory) {
        (address manager, address token,, uint256 amountToBorrow) = _decodeProbe(data);
        if (msg.sender != manager || manager != poolManagerV4) revert UnexpectedCallback();

        IUniswapV4PoolManager(manager).take(token, address(this), amountToBorrow);
        _onFlashLoanReceived(data);
    }

    /// @notice PancakeSwap Infinity lock callback. Like V4 the tokens are pulled, but the
    ///         lock and the `take` both belong to the Vault.
    function lockAcquired(bytes calldata data) external returns (bytes memory) {
        (address vault, address token,, uint256 amountToBorrow) = _decodeProbe(data);
        if (msg.sender != vault || vault != infinityVault) revert UnexpectedCallback();

        IInfinityVault(vault).take(token, address(this), amountToBorrow);
        _onFlashLoanReceived(data);
    }

    /// @dev Shared body of every callback: the tokens are already here, so measure and throw
    ///      the result. Always reverts.
    function _onFlashLoanReceived(bytes calldata data) internal {
        (address pool, address token, uint256 balanceBeforeLoan, uint256 amountToBorrow) = _decodeProbe(data);
        if (msg.sender != pool) revert UnexpectedCallback();

        _revertWithMeasuredFees(ERC20(token), pool, balanceBeforeLoan, amountToBorrow);
    }

    function _decodeProbe(bytes calldata data)
        internal
        pure
        returns (address pool, address token, uint256 balanceBeforeLoan, uint256 amountToBorrow)
    {
        return abi.decode(data, (address, address, uint256, uint256));
    }

    /*//////////////////////////////////////////////////////////////
                              MEASUREMENT
    //////////////////////////////////////////////////////////////*/

    /// @dev Measures the buy fee (what actually arrived vs. what was requested) and the
    ///      sell fee against two different recipients, then reverts with the ABI encoded
    ///      `TokenFees`. Reverting is what unwinds the loan: nothing is ever repaid, and
    ///      `_parseRevertReason` turns the revert data back into a return value.
    function _revertWithMeasuredFees(
        ERC20 tokenBorrowed,
        address pool,
        uint256 balanceBeforeLoan,
        uint256 amountRequestedToBorrow
    ) internal {
        uint256 amountBorrowed = tokenBorrowed.balanceOf(address(this)) - balanceBeforeLoan;

        uint256 buyFeeBpsForPair = _calculateBuyFee(amountRequestedToBorrow, amountBorrowed);

        // Sell into a plain address first, undone by the inner revert, so that the second
        // measurement still starts from the full borrowed balance.
        (uint256 sellFeeBpsForReference, bool transferFailedForReference) =
            _calculateSellFee(tokenBorrowed, sellFeeReferenceRecipient, amountBorrowed, true);

        // Then sell into the pool itself: many taxing tokens exempt or specially treat pairs.
        (uint256 sellFeeBpsForPair, bool transferFailedForPair) =
            _calculateSellFee(tokenBorrowed, pool, amountBorrowed, false);

        bytes memory tokenFees = abi.encode(
            TokenFees({
                buyFeeBpsForPair: buyFeeBpsForPair,
                sellFeeBpsForPair: sellFeeBpsForPair,
                sellFeeBpsForFactory: sellFeeBpsForReference,
                errCode: _transferErrorCodes(transferFailedForPair, transferFailedForReference)
            })
        );

        assembly {
            revert(add(tokenFees, 0x20), mload(tokenFees))
        }
    }

    function _transferErrorCodes(bool failedForPair, bool failedForReference)
        internal
        pure
        returns (ErrorCode[] memory errCode)
    {
        if (failedForReference && failedForPair) {
            errCode = new ErrorCode[](2);
            errCode[0] = ErrorCode.TransferFailed2;
            errCode[1] = ErrorCode.TransferFailed3;
        } else if (failedForReference) {
            errCode = _singleErrCode(ErrorCode.TransferFailed3);
        } else if (failedForPair) {
            errCode = _singleErrCode(ErrorCode.TransferFailed2);
        } else {
            errCode = _singleErrCode(ErrorCode.NoError);
        }
    }

    function _calculateBuyFee(uint256 amountRequestedToBorrow, uint256 amountBorrowed)
        internal
        pure
        returns (uint256 buyFeeBps)
    {
        if (amountRequestedToBorrow == 0) return 0;
        buyFeeBps = (amountRequestedToBorrow - amountBorrowed).mulDivUp(BPS, amountRequestedToBorrow);
    }

    /// @dev `isRevert == true` performs the transfer and then rolls it back, so the caller
    ///      keeps its balance; the measurement is smuggled out through the revert data.
    function _calculateSellFee(ERC20 tokenBorrowed, address to, uint256 amountBorrowed, bool isRevert)
        internal
        returns (uint256 sellFeeBps, bool transferFailed)
    {
        // A token that taxed the whole loan away leaves nothing to sell. Report a full
        // tax instead of dividing by zero, which would otherwise surface as a bare revert.
        if (amountBorrowed == 0) return (BPS, false);

        try this.callTransfer(tokenBorrowed, to, amountBorrowed, isRevert) returns (
            uint256 _sellFeeBps, bool _transferFailed
        ) {
            (sellFeeBps, transferFailed) = (_sellFeeBps, _transferFailed);
        } catch (bytes memory revertData) {
            (sellFeeBps, transferFailed) = abi.decode(revertData, (uint256, bool));
        }
    }

    function callTransfer(ERC20 tokenBorrowed, address to, uint256 amountBorrowed, bool isRevert)
        external
        returns (uint256 sellFeeBps, bool transferFailed)
    {
        uint256 toBalanceBeforeSell = tokenBorrowed.balanceOf(to);

        try this.callTransfer(tokenBorrowed, to, amountBorrowed) {
            uint256 amountSold = tokenBorrowed.balanceOf(to) - toBalanceBeforeSell;
            sellFeeBps = (amountBorrowed - amountSold).mulDivUp(BPS, amountBorrowed);
        } catch {
            transferFailed = true;
        }

        if (isRevert) {
            bytes memory result = abi.encode(sellFeeBps, transferFailed);
            assembly {
                revert(add(result, 0x20), mload(result))
            }
        }
    }

    function callTransfer(ERC20 token, address to, uint256 amount) external {
        token.safeTransfer(to, amount);
    }

    /*//////////////////////////////////////////////////////////////
                            REVERT DATA HANDLING
    //////////////////////////////////////////////////////////////*/

    /// @dev Revert data of exactly the size of an encoded `TokenFees` is a successful
    ///      measurement; anything else is a genuine failure and is re-thrown untouched.
    function _parseRevertReason(bytes memory reason) internal pure returns (TokenFees memory) {
        if (reason.length == ENCODED_TOKEN_FEES_ONE_ERROR || reason.length == ENCODED_TOKEN_FEES_TWO_ERRORS) {
            return abi.decode(reason, (TokenFees));
        }
        _bubbleUp(reason);
    }

    function _bubbleUp(bytes memory reason) internal pure {
        if (reason.length == 0) revert();
        assembly {
            revert(add(reason, 0x20), mload(reason))
        }
    }

    /*//////////////////////////////////////////////////////////////
                            ERROR CLASSIFICATION
    //////////////////////////////////////////////////////////////*/

    /// @dev Translates raw revert data into a public `ErrorCode`.
    function _errorCodeFromReason(bytes memory reason) internal pure returns (ErrorCode) {
        if (reason.length < 4) return ErrorCode.Others; // empty revert, e.g. out of gas

        // Truncating to 4 bytes is exactly what reading a revert selector means.
        // forge-lint: disable-next-line(unsafe-typecast)
        bytes4 selector = bytes4(reason);

        if (selector == PoolInvalid.selector) return ErrorCode.PoolInvalid;
        if (selector == InsufficientLiquidity.selector) return ErrorCode.InsufficientLiquidity;
        if (selector == ERROR_STRING_SELECTOR) return _errorCodeFromMessage(_revertMessage(reason));

        return ErrorCode.Others;
    }

    /// @dev Matches on the message suffix so the same table works for every V2/V3 fork
    ///      ("UniswapV2: INSUFFICIENT_LIQUIDITY", "Pancake: INSUFFICIENT_LIQUIDITY", ...).
    function _errorCodeFromMessage(bytes memory message) internal pure returns (ErrorCode) {
        // Uniswap V3 style short codes.
        if (_equals(message, "L")) return ErrorCode.InsufficientLiquidity;
        if (_equals(message, "TF")) return ErrorCode.TransferFailed1;

        // Uniswap V2 style prefixed codes.
        if (_endsWith(message, "INSUFFICIENT_OUTPUT_AMOUNT")) return ErrorCode.InsufficientOutputAmount;
        if (_endsWith(message, "INSUFFICIENT_LIQUIDITY")) return ErrorCode.InsufficientLiquidity;
        if (_endsWith(message, "TRANSFER_FAILED")) return ErrorCode.TransferFailed1;

        return ErrorCode.Others;
    }

    /// @dev Extracts the string out of `Error(string)` revert data without `abi.decode`,
    ///      which would revert on malformed input while we are inside a catch block.
    function _revertMessage(bytes memory reason) internal pure returns (bytes memory message) {
        // 4 selector + 32 offset + 32 length
        if (reason.length < 68) return "";

        uint256 length;
        assembly {
            length := mload(add(reason, 0x44))
        }
        if (length > reason.length - 68) return "";

        message = new bytes(length);
        for (uint256 i; i < length; ++i) {
            message[i] = reason[68 + i];
        }
    }

    function _equals(bytes memory value, bytes memory expected) internal pure returns (bool) {
        return keccak256(value) == keccak256(expected);
    }

    function _endsWith(bytes memory value, bytes memory suffix) internal pure returns (bool) {
        if (value.length < suffix.length) return false;

        uint256 offset = value.length - suffix.length;
        for (uint256 i; i < suffix.length; ++i) {
            if (value[offset + i] != suffix[i]) return false;
        }
        return true;
    }

    /*//////////////////////////////////////////////////////////////
                                 HELPERS
    //////////////////////////////////////////////////////////////*/

    function _normalize(TokenFees memory measuredFees) internal pure returns (TokenFees memory) {
        if (measuredFees.errCode.length == 0) measuredFees.errCode = _singleErrCode(ErrorCode.NoError);
        return measuredFees;
    }

    function _failure(bytes memory reason) internal pure returns (TokenFees memory) {
        return TokenFees(0, 0, 0, _singleErrCode(_errorCodeFromReason(reason)));
    }

    /// @dev The token under test is always flash-borrowed and transferred, so it has to be a
    ///      real ERC20. Native currency has no transfer fee to measure in the first place;
    ///      as the OTHER side of a pool it is fine, and is spelled `address(0)` there.
    function _requireMeasurableToken(address token) internal pure {
        if (token == address(0)) revert NativeCurrencyNotSupported();
    }

    function _singleErrCode(ErrorCode code) internal pure returns (ErrorCode[] memory codes) {
        codes = new ErrorCode[](1);
        codes[0] = code;
    }
}
