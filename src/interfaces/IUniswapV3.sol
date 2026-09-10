// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity >=0.5.0;

/// @notice Minimal view of a Uniswap V3 style factory (Uniswap V3, PancakeSwap V3, ...).
interface IUniswapV3Factory {
    function getPool(address tokenA, address tokenB, uint24 fee) external view returns (address pool);
}

/// @notice Minimal view of a Uniswap V3 style pool. `flash` lends `amount0`/`amount1`
///         and calls back into the recipient before requiring repayment.
interface IUniswapV3Pool {
    function token0() external view returns (address);
    function token1() external view returns (address);
    function flash(address recipient, uint256 amount0, uint256 amount1, bytes calldata data) external;
}
