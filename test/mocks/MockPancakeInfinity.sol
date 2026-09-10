// SPDX-License-Identifier: MIT
pragma solidity =0.8.18;

interface ILockCallbackReceiver {
    function lockAcquired(bytes calldata data) external returns (bytes memory);
}

/// @notice Minimal PancakeSwap Infinity `Vault`: custodies the currencies and hands control
///         to the locker, exactly like the real one (`lock` is permissionless, `take` only
///         needs an open lock).
contract MockInfinityVault {
    address public locker;

    error AlreadyLocked();
    error NotLocked();

    function lock(bytes calldata data) external returns (bytes memory result) {
        if (locker != address(0)) revert AlreadyLocked();
        locker = msg.sender;
        result = ILockCallbackReceiver(msg.sender).lockAcquired(data);
        locker = address(0);
    }

    function take(address currency, address to, uint256 amount) external {
        if (locker == address(0)) revert NotLocked();
        (bool success,) = currency.call(abi.encodeWithSelector(0xa9059cbb, to, amount));
        require(success, "TAKE_FAILED");
    }
}

/// @notice Minimal Infinity CL pool manager: the pool registry.
/// @dev    The pool id is derived here with the canonical Infinity formulas
///         (`PoolIdLibrary.toId` over the six-word `PoolKey`, and
///         `CLPoolParametersHelper` for the packed `parameters`), independently of the
///         validator, so the tests exercise the derivation rather than assume it.
contract MockInfinityCLPoolManager {
    struct Key {
        address currency0;
        address currency1;
        address hooks;
        address poolManager;
        uint24 fee;
        bytes32 parameters;
    }

    mapping(bytes32 => uint160) internal sqrtPriceX96Of;
    /// @dev The real pool manager records this at initialize, which is what makes an
    ///      arbitrary 24-bit fee recoverable instead of guessable.
    mapping(bytes32 => Key) internal keyOf;

    function initializePool(
        address currencyA,
        address currencyB,
        address hooks,
        uint24 fee,
        int24 tickSpacing,
        uint16 hooksRegistration,
        uint160 sqrtPriceX96
    ) external {
        (address currency0, address currency1) = currencyA < currencyB ? (currencyA, currencyB) : (currencyB, currencyA);
        bytes32 parameters = bytes32((uint256(uint24(tickSpacing)) << 16) | uint256(hooksRegistration));
        bytes32 poolId = keccak256(abi.encode(currency0, currency1, hooks, address(this), fee, parameters));
        sqrtPriceX96Of[poolId] = sqrtPriceX96;
        keyOf[poolId] = Key(currency0, currency1, hooks, address(this), fee, parameters);
    }

    function poolIdToPoolKey(bytes32 poolId)
        external
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
        Key memory k = keyOf[poolId];
        return (k.currency0, k.currency1, k.hooks, k.poolManager, k.fee, k.parameters);
    }

    function getSlot0(bytes32 poolId)
        external
        view
        returns (uint160 sqrtPriceX96, int24 tick, uint24 protocolFee, uint24 lpFee)
    {
        return (sqrtPriceX96Of[poolId], 0, 0, 0);
    }
}
