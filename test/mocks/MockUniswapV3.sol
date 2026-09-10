// SPDX-License-Identifier: MIT
pragma solidity =0.8.18;

/// @notice Which flash callback the pool invokes.
enum V3CallbackStyle {
    Pancake,
    Uniswap
}

interface IV3FlashCallback {
    function pancakeV3FlashCallback(uint256 fee0, uint256 fee1, bytes calldata data) external;
    function uniswapV3FlashCallback(uint256 fee0, uint256 fee1, bytes calldata data) external;
}

/// @notice Minimal Uniswap V3 pool: `flash` plus the short revert strings ("L", "TF")
///         that the validator maps to error codes.
contract MockUniswapV3Pool {
    address public token0;
    address public token1;
    uint24 public fee;
    V3CallbackStyle public callbackStyle;

    constructor(address tokenA, address tokenB, uint24 fee_, V3CallbackStyle style) {
        (token0, token1) = tokenA < tokenB ? (tokenA, tokenB) : (tokenB, tokenA);
        fee = fee_;
        callbackStyle = style;
    }

    function flash(address recipient, uint256 amount0, uint256 amount1, bytes calldata data) external {
        require(amount0 <= _balanceOf(token0) && amount1 <= _balanceOf(token1), "L");

        uint256 balance0Before = _balanceOf(token0);
        uint256 balance1Before = _balanceOf(token1);

        if (amount0 > 0) _safeTransfer(token0, recipient, amount0);
        if (amount1 > 0) _safeTransfer(token1, recipient, amount1);

        uint256 fee0 = _flashFee(amount0);
        uint256 fee1 = _flashFee(amount1);

        if (callbackStyle == V3CallbackStyle.Pancake) {
            IV3FlashCallback(recipient).pancakeV3FlashCallback(fee0, fee1, data);
        } else {
            IV3FlashCallback(recipient).uniswapV3FlashCallback(fee0, fee1, data);
        }

        require(_balanceOf(token0) >= balance0Before + fee0 && _balanceOf(token1) >= balance1Before + fee1, "F0");
    }

    function _flashFee(uint256 amount) internal view returns (uint256) {
        return amount == 0 ? 0 : (amount * fee + 1e6 - 1) / 1e6;
    }

    function _balanceOf(address token) internal view returns (uint256) {
        (bool ok, bytes memory data) = token.staticcall(abi.encodeWithSignature("balanceOf(address)", address(this)));
        require(ok, "BALANCE_OF_FAILED");
        return abi.decode(data, (uint256));
    }

    function _safeTransfer(address token, address to, uint256 value) private {
        (bool success, bytes memory data) = token.call(abi.encodeWithSelector(0xa9059cbb, to, value));
        require(success && (data.length == 0 || abi.decode(data, (bool))), "TF");
    }
}
