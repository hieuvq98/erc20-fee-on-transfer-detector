// SPDX-License-Identifier: MIT
pragma solidity =0.8.18;

/// @notice Which flash-swap callback the pair invokes, so both the Uniswap V2 and the
///         PancakeSwap V2 naming can be exercised.
enum V2CallbackStyle {
    Pancake,
    Uniswap
}

interface IV2Callee {
    function pancakeCall(address sender, uint256 amount0, uint256 amount1, bytes calldata data) external;
    function uniswapV2Call(address sender, uint256 amount0, uint256 amount1, bytes calldata data) external;
}

/// @notice Minimal Uniswap V2 pair: enough of `swap` to serve a flash loan and to
///         reproduce the exact revert strings the validator classifies.
contract MockUniswapV2Pair {
    address public token0;
    address public token1;
    V2CallbackStyle public callbackStyle;

    constructor(address tokenA, address tokenB, V2CallbackStyle style) {
        (token0, token1) = tokenA < tokenB ? (tokenA, tokenB) : (tokenB, tokenA);
        callbackStyle = style;
    }

    function swap(uint256 amount0Out, uint256 amount1Out, address to, bytes calldata data) external {
        require(amount0Out > 0 || amount1Out > 0, "Pancake: INSUFFICIENT_OUTPUT_AMOUNT");
        require(amount0Out < _balanceOf(token0) && amount1Out < _balanceOf(token1), "Pancake: INSUFFICIENT_LIQUIDITY");

        uint256 balance0Before = _balanceOf(token0);
        uint256 balance1Before = _balanceOf(token1);

        if (amount0Out > 0) _safeTransfer(token0, to, amount0Out);
        if (amount1Out > 0) _safeTransfer(token1, to, amount1Out);

        if (data.length > 0) {
            if (callbackStyle == V2CallbackStyle.Pancake) {
                IV2Callee(to).pancakeCall(msg.sender, amount0Out, amount1Out, data);
            } else {
                IV2Callee(to).uniswapV2Call(msg.sender, amount0Out, amount1Out, data);
            }
        }

        require(_balanceOf(token0) >= balance0Before && _balanceOf(token1) >= balance1Before, "Pancake: K");
    }

    function _balanceOf(address token) internal view returns (uint256) {
        (bool ok, bytes memory data) = token.staticcall(abi.encodeWithSignature("balanceOf(address)", address(this)));
        require(ok, "BALANCE_OF_FAILED");
        return abi.decode(data, (uint256));
    }

    /// @dev Same shape as the real pair: a failing token transfer surfaces as TRANSFER_FAILED.
    function _safeTransfer(address token, address to, uint256 value) private {
        (bool success, bytes memory data) = token.call(abi.encodeWithSelector(0xa9059cbb, to, value));
        require(success && (data.length == 0 || abi.decode(data, (bool))), "Pancake: TRANSFER_FAILED");
    }
}
