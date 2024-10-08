// Sources flattened with hardhat v2.6.8 https://hardhat.org

// File @openzeppelin/contracts/token/ERC20/IERC20.sol@v3.4.2-solc-0.7

// SPDX-License-Identifier: MIT

pragma solidity ^0.7.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}


// File @uniswap/v2-core/contracts/interfaces/IV2Pair.sol@v1.0.1

pragma solidity >=0.5.0;

interface IV2Pair {
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function name() external pure returns (string memory);
    function symbol() external pure returns (string memory);
    function decimals() external pure returns (uint8);
    function totalSupply() external view returns (uint);
    function balanceOf(address owner) external view returns (uint);
    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint value) external returns (bool);
    function transfer(address to, uint value) external returns (bool);
    function transferFrom(address from, address to, uint value) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);
    function PERMIT_TYPEHASH() external pure returns (bytes32);
    function nonces(address owner) external view returns (uint);

    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external;

    event Mint(address indexed sender, uint amount0, uint amount1);
    event Burn(address indexed sender, uint amount0, uint amount1, address indexed to);
    event Swap(
        address indexed sender,
        uint amount0In,
        uint amount1In,
        uint amount0Out,
        uint amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint);
    function factory() external view returns (address);
    function token0() external view returns (address);
    function token1() external view returns (address);
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);
    function price0CumulativeLast() external view returns (uint);
    function price1CumulativeLast() external view returns (uint);
    function kLast() external view returns (uint);

    function mint(address to) external returns (uint liquidity);
    function burn(address to) external returns (uint amount0, uint amount1);
    function swap(uint amount0Out, uint amount1Out, address to, bytes calldata data) external;
    function skim(address to) external;
    function sync() external;

    function initialize(address, address) external;
}


// File @uniswap/v3-core/contracts/libraries/LowGasSafeMath.sol@v1.0.1

pragma solidity >=0.7.0;

/// @title Optimized overflow and underflow safe math operations
/// @notice Contains methods for doing math operations that revert on overflow or underflow for minimal gas cost
library LowGasSafeMath {
    /// @notice Returns x + y, reverts if sum overflows uint256
    /// @param x The augend
    /// @param y The addend
    /// @return z The sum of x and y
    function add(uint256 x, uint256 y) internal pure returns (uint256 z) {
        require((z = x + y) >= x);
    }

    /// @notice Returns x - y, reverts if underflows
    /// @param x The minuend
    /// @param y The subtrahend
    /// @return z The difference of x and y
    function sub(uint256 x, uint256 y) internal pure returns (uint256 z) {
        require((z = x - y) <= x);
    }

    /// @notice Returns x * y, reverts if overflows
    /// @param x The multiplicand
    /// @param y The multiplier
    /// @return z The product of x and y
    function mul(uint256 x, uint256 y) internal pure returns (uint256 z) {
        require(x == 0 || (z = x * y) / x == y);
    }

    /// @notice Returns x + y, reverts if overflows or underflows
    /// @param x The augend
    /// @param y The addend
    /// @return z The sum of x and y
    function add(int256 x, int256 y) internal pure returns (int256 z) {
        require((z = x + y) >= x == (y >= 0));
    }

    /// @notice Returns x - y, reverts if overflows or underflows
    /// @param x The minuend
    /// @param y The subtrahend
    /// @return z The difference of x and y
    function sub(int256 x, int256 y) internal pure returns (int256 z) {
        require((z = x - y) <= x == (y >= 0));
    }
}


// File contracts/libraries/V2Library.sol

pragma solidity >=0.5.0;


library V2Library {
    using LowGasSafeMath for uint256;

    // returns sorted token addresses, used to handle return values from pairs sorted in this order
    function sortTokens(address tokenA, address tokenB) internal pure returns (address token0, address token1) {
        require(tokenA != tokenB);
        (token0, token1) = tokenA < tokenB ? (tokenA, tokenB) : (tokenB, tokenA);
        require(token0 != address(0));
    }

    // calculates the CREATE2 address for a pair without making any external calls
    function pairFor(
        address factory,
        address tokenA,
        address tokenB
    ) internal pure returns (address pair) {
        (address token0, address token1) = sortTokens(tokenA, tokenB);
        pair = address(
            uint256(
                keccak256(
                    abi.encodePacked(
                        hex'ff',
                        factory,
                        keccak256(abi.encodePacked(token0, token1)),
                        hex'00fb7f630766e6a796048ea87d01acd3068e8ff67d078148a3fa3f4a84f69bd5' // init code hash
                    )
                )
            )
        );
    }

    // fetches and sorts the reserves for a pair
    function getReserves(
        address factory,
        address tokenA,
        address tokenB
    ) internal view returns (uint256 reserveA, uint256 reserveB) {
        (address token0, ) = sortTokens(tokenA, tokenB);
        (uint256 reserve0, uint256 reserve1, ) = IV2Pair(pairFor(factory, tokenA, tokenB)).getReserves();
        (reserveA, reserveB) = tokenA == token0 ? (reserve0, reserve1) : (reserve1, reserve0);
    }

    // given an input amount of an asset and pair reserves, returns the maximum output amount of the other asset
    function getAmountOut(
        uint256 amountIn,
        uint256 reserveIn,
        uint256 reserveOut
    ) internal pure returns (uint256 amountOut) {
        require(amountIn > 0, 'INSUFFICIENT_INPUT_AMOUNT');
        require(reserveIn > 0 && reserveOut > 0);
        uint256 amountInWithFee = amountIn.mul(997);
        uint256 numerator = amountInWithFee.mul(reserveOut);
        uint256 denominator = reserveIn.mul(1000).add(amountInWithFee);
        amountOut = numerator / denominator;
    }

    // given an output amount of an asset and pair reserves, returns a required input amount of the other asset
    function getAmountIn(
        uint256 amountOut,
        uint256 reserveIn,
        uint256 reserveOut
    ) internal pure returns (uint256 amountIn) {
        require(amountOut > 0, 'INSUFFICIENT_OUTPUT_AMOUNT');
        require(reserveIn > 0 && reserveOut > 0);
        uint256 numerator = reserveIn.mul(amountOut).mul(1000);
        uint256 denominator = reserveOut.sub(amountOut).mul(997);
        amountIn = (numerator / denominator).add(1);
    }

    // performs chained getAmountIn calculations on any number of pairs
    function getAmountsIn(
        address factory,
        uint256 amountOut,
        address[] memory path
    ) internal view returns (uint256[] memory amounts) {
        require(path.length >= 2);
        amounts = new uint256[](path.length);
        amounts[amounts.length - 1] = amountOut;
        for (uint256 i = path.length - 1; i > 0; i--) {
            (uint256 reserveIn, uint256 reserveOut) = getReserves(factory, path[i - 1], path[i]);
            amounts[i - 1] = getAmountIn(amounts[i], reserveIn, reserveOut);
        }
    }
}


// File contracts/interfaces/ITokenValidator.sol

pragma solidity >=0.7.5;
pragma abicoder v2;

/// @notice Validates tokens by flash borrowing from the token/<base token> pool on V2.
/// @notice Returns
///     Status.FOT if we detected a fee is taken on transfer.
///     Status.STF if transfer failed for the token.
///     Status.UNKN if we did not detect any issues with the token.
/// @notice A return value of Status.UNKN does not mean the token is definitely not a fee on transfer token
///     or definitely has no problems with its transfer. It just means we cant say for sure that it has any
///     issues.
/// @dev We can not guarantee the result of this lens is correct for a few reasons:
/// @dev 1/ Some tokens take fees or allow transfers under specific conditions, for example some have an allowlist
/// @dev    of addresses that do/dont require fees. Therefore the result is not guaranteed to be correct
/// @dev    in all circumstances.
/// @dev 2/ It is possible that the token does not have any pools on V2 therefore we are not able to perform
/// @dev    a flashloan to test the token.
/// @dev These functions are not marked view because they rely on calling non-view functions and reverting
/// to compute the result.
interface ITokenValidator {
    // Status.FOT: detected a fee is taken on transfer.
    // Status.STF: transfer failed for the token.
    // Status.UNKN: no issues found with the token.
    enum Status {UNKN, FOT, STF}

    /// @notice Validates a token by detecting if its transferable or takes a fee on transfer
    /// @param token The address of the token to check for fee on transfer
    /// @param baseTokens The addresses of the tokens to try pairing with
    /// token when looking for a pool to flash loan from.
    /// @param amountToBorrow The amount to try flash borrowing from the pools
    /// @return The status of the token
    function validate(
        address token,
        address[] calldata baseTokens,
        uint256 amountToBorrow
    ) external returns (Status);

    /// @notice Validates each token by detecting if its transferable or takes a fee on transfer
    /// @param tokens The addresses of the tokens to check for fee on transfer
    /// @param baseTokens The addresses of the tokens to try pairing with
    /// token when looking for a pool to flash loan from.
    /// @param amountToBorrow The amount to try flash borrowing from the pools
    /// @return The status of the token
    function batchValidate(
        address[] calldata tokens,
        address[] calldata baseTokens,
        uint256 amountToBorrow
    ) external returns (Status[] memory);
}


// File contracts/lens/TokenValidator.sol

pragma solidity =0.7.6;

/// @notice Validates tokens by flash borrowing from the token/<base token> pool on V2.
/// @notice Returns
///     Status.FOT if we detected a fee is taken on transfer.
///     Status.STF if transfer failed for the token.
///     Status.UNKN if we did not detect any issues with the token.
/// @notice A return value of Status.UNKN does not mean the token is definitely not a fee on transfer token
///     or definitely has no problems with its transfer. It just means we cant say for sure that it has any
///     issues.
/// @dev We can not guarantee the result of this lens is correct for a few reasons:
/// @dev 1/ Some tokens take fees or allow transfers under specific conditions, for example some have an allowlist
/// @dev    of addresses that do/dont require fees. Therefore the result is not guaranteed to be correct
/// @dev    in all circumstances.
/// @dev 2/ It is possible that the token does not have any pools on V2 therefore we are not able to perform
/// @dev    a flashloan to test the token.
contract TokenValidator is ITokenValidator {
    string internal constant FOT_REVERT_STRING = 'FOT';
    // https://github.com/Uniswap/v2-core/blob/1136544ac842ff48ae0b1b939701436598d74075/contracts/V2Pair.sol#L46
    string internal constant STF_REVERT_STRING_SUFFIX = 'TRANSFER_FAILED';
    uint256 public gasLimit;
    address public factoryV2;
    address public owner;

    constructor(address _factoryV2, uint256 _gasLimit) {
        factoryV2 = _factoryV2;
        gasLimit = _gasLimit;
        owner = msg.sender;
    }

    modifier onlyOwner() {
        require(msg.sender == owner, "Sender is not owner");
        _;
    }

    function batchValidate(
        address[] calldata tokens,
        address[] calldata baseTokens,
        uint256 amountToBorrow
    ) public override returns (Status[] memory isFotResults) {
        isFotResults = new Status[](tokens.length);
        for (uint256 i = 0; i < tokens.length; i++) {
            try this.validate{gas: gasLimit}(tokens[i], baseTokens, amountToBorrow) returns (Status status) {
                isFotResults[i] = status;
            }
            catch {
                isFotResults[i] = Status.STF;
            }
        }
    }

    function validate(
        address token,
        address[] calldata baseTokens,
        uint256 amountToBorrow
    ) public override returns (Status) {
        for (uint256 i = 0; i < baseTokens.length; i++) {
            Status result = _validate(token, baseTokens[i], amountToBorrow);
            if (result == Status.FOT || result == Status.STF) {
                return result;
            }
        }
        return Status.UNKN;
    }

    function _validate(
        address token,
        address baseToken,
        uint256 amountToBorrow
    ) internal returns (Status) {
        if (token == baseToken) {
            return Status.UNKN;
        }

        address pairAddress = V2Library.pairFor(this.factoryV2(), token, baseToken);

        // If the token/baseToken pair exists, get token0.
        // Must do low level call as try/catch does not support case where contract does not exist.
        (, bytes memory returnData) = address(pairAddress).call(abi.encodeWithSelector(IV2Pair.token0.selector));

        if (returnData.length == 0) {
            return Status.STF;
        }

        address token0Address = abi.decode(returnData, (address));

        // Flash loan {amountToBorrow}
        (uint256 amount0Out, uint256 amount1Out) =
            token == token0Address ? (amountToBorrow, uint256(0)) : (uint256(0), amountToBorrow);

        uint256 balanceBeforeLoan = IERC20(token).balanceOf(address(this));

        IV2Pair pair = IV2Pair(pairAddress);

        try
            pair.swap(amount0Out, amount1Out, address(this), abi.encode(balanceBeforeLoan, amountToBorrow))
        {} catch Error(string memory reason) {
            if (isFotFailed(reason)) {
                return Status.FOT;
            }

            if (isTransferFailed(reason)) {
                return Status.STF;
            }

            return Status.UNKN;
        }

        // Swap always reverts so should never reach.
        revert('Unexpected error');
    }

    function setGasLimit(uint256 _gasLimit) public onlyOwner {
        gasLimit = _gasLimit;
    }

    function isFotFailed(string memory reason) internal pure returns (bool) {
        return keccak256(bytes(reason)) == keccak256(bytes(FOT_REVERT_STRING));
    }

    function isTransferFailed(string memory reason) internal pure returns (bool) {
        // We check the suffix of the revert string so we can support forks that
        // may have modified the prefix.
        string memory stf = STF_REVERT_STRING_SUFFIX;

        uint256 reasonLength = bytes(reason).length;
        uint256 suffixLength = bytes(stf).length;
        if (reasonLength < suffixLength) {
            return false;
        }

        uint256 ptr;
        uint256 offset = 32 + reasonLength - suffixLength;
        bool transferFailed;
        assembly {
            ptr := add(reason, offset)
            let suffixPtr := add(stf, 32)
            transferFailed := eq(keccak256(ptr, suffixLength), keccak256(suffixPtr, suffixLength))
        }

        return transferFailed;
    }

    function pancakeCall(
        address,
        uint256 amount0,
        uint256,
        bytes calldata data
    ) external view {
        IV2Pair pair = IV2Pair(msg.sender);
        (address token0, address token1) = (pair.token0(), pair.token1());

        IERC20 tokenBorrowed = IERC20(amount0 > 0 ? token0 : token1);

        (uint256 balanceBeforeLoan, uint256 amountRequestedToBorrow) = abi.decode(data, (uint256, uint256));
        uint256 amountBorrowed = tokenBorrowed.balanceOf(address(this)) - balanceBeforeLoan;

        // If we received less token than we requested when we called swap, then a fee must have been taken
        // by the token during transfer.
        if (amountBorrowed != amountRequestedToBorrow) {
            revert(FOT_REVERT_STRING);
        }

        // Note: If we do not revert here, we would end up reverting in the pair's swap method anyway
        // since for a flash borrow we need to transfer back the amount we borrowed + 0.3% fee, and we don't
        // have funds to cover the fee. Revert early here to save gas/time.
        revert('Unknown');
    }
}
