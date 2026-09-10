// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity >=0.5.0;

/// @notice Minimal view of the Uniswap V4 singleton `PoolManager`.
/// @dev    V4 has no per-pair contract. All currencies live in the singleton and are
///         borrowed through flash accounting: `unlock` hands control back to the caller
///         via `unlockCallback`, during which `take` moves currency out without payment.
///         The debt only has to be settled when `unlockCallback` returns, so a probe that
///         reverts inside the callback never needs to repay.
interface IUniswapV4PoolManager {
    function unlock(bytes calldata data) external returns (bytes memory);
    function take(address currency, address to, uint256 amount) external;
    /// @notice Raw storage read, used here to check whether a pool id has been initialized.
    function extsload(bytes32 slot) external view returns (bytes32);
}

/// @notice Callback interface the `PoolManager` invokes from `unlock`.
interface IUniswapV4UnlockCallback {
    function unlockCallback(bytes calldata data) external returns (bytes memory);
}

/// @notice The Uniswap V4 `PositionManager`, used purely as a pool-key registry.
/// @dev    V4 core keeps no reverse mapping, but the canonical position manager records one
///         keyed by the first 25 bytes of the pool id. It only covers pools that have had a
///         position minted through it, so a miss is not proof that a pool does not exist.
interface IUniswapV4PositionManager {
    function poolKeys(bytes25 poolId)
        external
        view
        returns (address currency0, address currency1, uint24 fee, int24 tickSpacing, address hooks);
}
