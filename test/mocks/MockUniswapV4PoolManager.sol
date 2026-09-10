// SPDX-License-Identifier: MIT
pragma solidity =0.8.18;

interface IUnlockCallbackReceiver {
    function unlockCallback(bytes calldata data) external returns (bytes memory);
}

/// @notice Minimal Uniswap V4 singleton: flash accounting through `unlock`/`take`, plus
///         the `extsload` view the validator uses to discover initialized pools.
/// @dev    The pool id and storage slot are derived here with the canonical Uniswap V4
///         formulas (`PoolId.toId` and `StateLibrary._getPoolStateSlot`), independently of
///         the validator, so the tests exercise the derivation rather than assume it.
contract MockUniswapV4PoolManager {
    uint256 internal constant POOLS_SLOT = 6;

    mapping(bytes32 => bytes32) internal slots;
    bool public unlocked;

    error AlreadyUnlocked();
    error ManagerLocked();

    function initializePool(
        address currencyA,
        address currencyB,
        uint24 fee,
        int24 tickSpacing,
        address hooks,
        uint160 sqrtPriceX96
    ) external {
        (address currency0, address currency1) = currencyA < currencyB ? (currencyA, currencyB) : (currencyB, currencyA);
        bytes32 poolId = keccak256(abi.encode(currency0, currency1, fee, tickSpacing, hooks));
        slots[keccak256(abi.encodePacked(poolId, POOLS_SLOT))] = bytes32(uint256(sqrtPriceX96));
    }

    function extsload(bytes32 slot) external view returns (bytes32) {
        return slots[slot];
    }

    function unlock(bytes calldata data) external returns (bytes memory result) {
        if (unlocked) revert AlreadyUnlocked();
        unlocked = true;
        result = IUnlockCallbackReceiver(msg.sender).unlockCallback(data);
        unlocked = false;
    }

    function take(address currency, address to, uint256 amount) external {
        if (!unlocked) revert ManagerLocked();
        (bool success,) = currency.call(abi.encodeWithSelector(0xa9059cbb, to, amount));
        require(success, "TAKE_FAILED");
    }
}

/// @notice Minimal Uniswap V4 `PositionManager`, used only as a pool-key registry.
contract MockUniswapV4PositionManager {
    struct Key {
        address currency0;
        address currency1;
        uint24 fee;
        int24 tickSpacing;
        address hooks;
    }

    mapping(bytes25 => Key) internal keys;

    function register(address currencyA, address currencyB, uint24 fee, int24 tickSpacing, address hooks) external {
        (address currency0, address currency1) = currencyA < currencyB ? (currencyA, currencyB) : (currencyB, currencyA);
        bytes32 poolId = keccak256(abi.encode(currency0, currency1, fee, tickSpacing, hooks));
        keys[bytes25(poolId)] = Key(currency0, currency1, fee, tickSpacing, hooks);
    }

    function poolKeys(bytes25 poolId)
        external
        view
        returns (address currency0, address currency1, uint24 fee, int24 tickSpacing, address hooks)
    {
        Key memory k = keys[poolId];
        return (k.currency0, k.currency1, k.fee, k.tickSpacing, k.hooks);
    }
}
