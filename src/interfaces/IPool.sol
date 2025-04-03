pragma solidity >=0.5.0;

interface IPool {
    function token0() external view returns (address);
    function token1() external view returns (address);
    
    // v2
    function swap(uint256 amount0Out, uint256 amount1Out, address to, bytes calldata data) external;
    
    // v3
    function flash(
        address recipient,
        uint256 amount0,
        uint256 amount1,
        bytes calldata data
    ) external;
}
