pragma solidity >=0.5.0;

interface IFactory {
    // v2
    function getPair(address tokenA, address tokenB) external view returns (address pair);
    // v3
    function getPool(address tokenA, address tokenB, uint24 fee) external view returns (address pool);
}
