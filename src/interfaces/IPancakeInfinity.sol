// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity >=0.5.0;

/// @notice The PancakeSwap Infinity `Vault`: the single contract that custodies every
///         currency, independent of which pool manager the pool belongs to.
/// @dev    This is the piece that differs most from Uniswap V4, where the `PoolManager`
///         is both the registry and the custodian. Here `lock` is permissionless and
///         `take` only requires an open lock, so a flash loan is `lock` -> `take` -> revert.
interface IInfinityVault {
    function lock(bytes calldata data) external returns (bytes memory);
    function take(address currency, address to, uint256 amount) external;
}

/// @notice Callback the `Vault` invokes from `lock`. Named `lockAcquired`, not
///         `unlockCallback` as in Uniswap V4.
interface IInfinityLockCallback {
    function lockAcquired(bytes calldata data) external returns (bytes memory);
}

/// @notice The concentrated-liquidity pool manager: the pool registry for CL pools.
/// @dev    Unlike Uniswap V4 there is a real getter, so no storage slot has to be guessed.
///         `sqrtPriceX96 == 0` means the pool id was never initialized.
interface IInfinityCLPoolManager {
    function getSlot0(bytes32 poolId)
        external
        view
        returns (uint160 sqrtPriceX96, int24 tick, uint24 protocolFee, uint24 lpFee);

    /// @notice Reverse lookup recorded at initialize: pool id -> the full `PoolKey`.
    /// @dev    This is what makes Infinity's free-form 24-bit fee tractable - the key does
    ///         not have to be guessed, it can be read back. An unknown id returns all zeros.
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
        );
}
