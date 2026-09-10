// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity >=0.5.0;

/// @notice Minimal view of a Uniswap V2 style factory (Uniswap V2, PancakeSwap V2, SushiSwap, ...).
interface IUniswapV2Factory {
    function getPair(address tokenA, address tokenB) external view returns (address pair);
}

/// @notice Minimal view of a Uniswap V2 style pair. `swap` with a non-empty `data`
///         payload performs a flash swap and calls back into the recipient.
interface IUniswapV2Pair {
    function token0() external view returns (address);
    function token1() external view returns (address);
    function swap(uint256 amount0Out, uint256 amount1Out, address to, bytes calldata data) external;
}
