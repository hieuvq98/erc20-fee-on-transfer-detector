// SPDX-License-Identifier: MIT
pragma solidity =0.8.18;

import "forge-std/Test.sol";
import "../src/TokenValidator.sol";
import "../src/config/ChainConfigs.sol";
import "./mocks/MockFeeOnTransferToken.sol";
import "./mocks/MockUniswapV2.sol";
import "./mocks/MockUniswapV3.sol";
import "./mocks/MockUniswapV4PoolManager.sol";
import "./mocks/MockPancakeInfinity.sol";

/// @notice Exposes the validator's internal helpers so they can be asserted on directly.
contract TokenValidatorHarness is TokenValidator {
    constructor(ValidatorConfig memory config) TokenValidator(config) {}

    function exposedErrorCodeFromReason(bytes memory reason) external pure returns (ErrorCode) {
        return _errorCodeFromReason(reason);
    }

    function exposedRevertMessage(bytes memory reason) external pure returns (bytes memory) {
        return _revertMessage(reason);
    }

    function exposedEndsWith(bytes memory value, bytes memory suffix) external pure returns (bool) {
        return _endsWith(value, suffix);
    }
}

/// @notice Shared fixtures for the mock-backed tests: one V2 factory, one V3 factory and
///         one V4 pool manager, all wired into a single validator.
abstract contract TokenValidatorBaseTest is Test {
    uint256 internal constant AMOUNT_TO_BORROW = 10_000;
    uint256 internal constant GAS_LIMIT = 5_000_000;
    uint256 internal constant POOL_LIQUIDITY = 1_000_000 ether;

    /// @dev Neutral, non-pool address used to measure `sellFeeBpsForFactory`.
    address internal constant REFERENCE_RECIPIENT = address(0xFEE);

    MockUniswapV4PoolManager internal poolManagerV4;
    MockUniswapV4PositionManager internal positionManagerV4Registry;
    MockInfinityVault internal infinityVault;
    MockInfinityCLPoolManager internal infinityCLPoolManager;

    MockFeeOnTransferToken internal baseToken;
    MockFeeOnTransferToken internal otherBaseToken;

    TokenValidatorHarness internal validator;

    function setUp() public virtual {
        poolManagerV4 = new MockUniswapV4PoolManager();
        positionManagerV4Registry = new MockUniswapV4PositionManager();
        infinityVault = new MockInfinityVault();
        infinityCLPoolManager = new MockInfinityCLPoolManager();

        baseToken = new MockFeeOnTransferToken("Base", "BASE", 0, 0, 0);
        otherBaseToken = new MockFeeOnTransferToken("Other Base", "OBASE", 0, 0, 0);

        validator = new TokenValidatorHarness(defaultConfig());
    }

    function defaultConfig() internal view returns (ValidatorConfig memory) {
        return ValidatorConfig({
            sellFeeReferenceRecipient: REFERENCE_RECIPIENT,
            poolManagerV4: address(poolManagerV4),
            positionManagerV4: address(positionManagerV4Registry),
            v4PoolsSlot: ChainConfigs.UNISWAP_V4_POOLS_SLOT,
            infinityVault: address(infinityVault),
            infinityCLPoolManager: address(infinityCLPoolManager)
        });
    }

    /*//////////////////////////////////////////////////////////////
                              POOL FIXTURES
    //////////////////////////////////////////////////////////////*/

    function newToken(uint256 buyBps, uint256 sellBps, uint256 transferBps)
        internal
        returns (MockFeeOnTransferToken token)
    {
        token = new MockFeeOnTransferToken("Taxed", "TAX", buyBps, sellBps, transferBps);
    }

    function createV2Pair(MockFeeOnTransferToken token, MockFeeOnTransferToken base, V2CallbackStyle style)
        internal
        returns (address pair)
    {
        pair = address(new MockUniswapV2Pair(address(token), address(base), style));
        token.setPool(pair, true);
        token.mint(pair, POOL_LIQUIDITY);
        base.mint(pair, POOL_LIQUIDITY);
    }

    function createV3Pool(MockFeeOnTransferToken token, MockFeeOnTransferToken base, uint24 fee, V3CallbackStyle style)
        internal
        returns (address pool)
    {
        pool = address(new MockUniswapV3Pool(address(token), address(base), fee, style));
        token.setPool(pool, true);
        token.mint(pool, POOL_LIQUIDITY);
        base.mint(pool, POOL_LIQUIDITY);
    }

    function createV4Pool(MockFeeOnTransferToken token, MockFeeOnTransferToken base, uint24 fee, int24 tickSpacing)
        internal
        returns (bytes32 poolId)
    {
        poolId = v4Id(address(token), address(base), fee, tickSpacing);
        poolManagerV4.initializePool(address(token), address(base), fee, tickSpacing, address(0), 1 << 96);
        positionManagerV4Registry.register(address(token), address(base), fee, tickSpacing, address(0));
        token.setPool(address(poolManagerV4), true);
        token.mint(address(poolManagerV4), POOL_LIQUIDITY);
        base.mint(address(poolManagerV4), POOL_LIQUIDITY);
    }

    /// @dev Infinity keeps the currencies in the Vault and the pool record in the CL pool
    ///      manager, so a fixture has to touch both.
    function createInfinityCLPool(
        MockFeeOnTransferToken token,
        MockFeeOnTransferToken base,
        uint24 fee,
        int24 tickSpacing
    ) internal returns (bytes32 poolId) {
        poolId = infinityId(address(token), address(base), fee, tickSpacing);
        infinityCLPoolManager.initializePool(address(token), address(base), address(0), fee, tickSpacing, 0, 1 << 96);
        token.setPool(address(infinityVault), true);
        token.mint(address(infinityVault), POOL_LIQUIDITY);
        base.mint(address(infinityVault), POOL_LIQUIDITY);
    }

    /*//////////////////////////////////////////////////////////////
                                HELPERS
    //////////////////////////////////////////////////////////////*/

    /// @dev Mirrors `PoolId.toId()` for Uniswap V4.
    function v4Id(address tokenA, address tokenB, uint24 fee, int24 tickSpacing) internal pure returns (bytes32) {
        (address c0, address c1) = tokenA < tokenB ? (tokenA, tokenB) : (tokenB, tokenA);
        return keccak256(abi.encode(c0, c1, fee, tickSpacing, address(0)));
    }

    /// @dev Mirrors `PoolIdLibrary.toId()` for Infinity, including the packed parameters.
    function infinityId(address tokenA, address tokenB, uint24 fee, int24 tickSpacing) internal view returns (bytes32) {
        (address c0, address c1) = tokenA < tokenB ? (tokenA, tokenB) : (tokenB, tokenA);
        return keccak256(
            abi.encode(
                c0, c1, address(0), address(infinityCLPoolManager), fee, bytes32(uint256(uint24(tickSpacing)) << 16)
            )
        );
    }

    function asArray(bytes32 item) internal pure returns (bytes32[] memory list) {
        list = new bytes32[](1);
        list[0] = item;
    }

    function asArray(address item) internal pure returns (address[] memory list) {
        list = new address[](1);
        list[0] = item;
    }

    function asArray(address a, address b) internal pure returns (address[] memory list) {
        list = new address[](2);
        list[0] = a;
        list[1] = b;
    }

    function assertFees(
        TokenFees memory actual,
        uint256 expectedBuy,
        uint256 expectedSellForPair,
        uint256 expectedSellForReference,
        ErrorCode expectedCode
    ) internal {
        assertEq(actual.buyFeeBpsForPair, expectedBuy, "buyFeeBpsForPair");
        assertEq(actual.sellFeeBpsForPair, expectedSellForPair, "sellFeeBpsForPair");
        assertEq(actual.sellFeeBpsForFactory, expectedSellForReference, "sellFeeBpsForFactory");
        assertEq(actual.errCode.length, 1, "errCode length");
        assertEq(uint256(actual.errCode[0]), uint256(expectedCode), "errCode[0]");
    }

    function assertErrorCode(TokenFees memory actual, ErrorCode expectedCode) internal {
        assertEq(actual.buyFeeBpsForPair, 0, "buyFeeBpsForPair");
        assertEq(actual.sellFeeBpsForPair, 0, "sellFeeBpsForPair");
        assertEq(actual.sellFeeBpsForFactory, 0, "sellFeeBpsForFactory");
        assertEq(actual.errCode.length, 1, "errCode length");
        assertEq(uint256(actual.errCode[0]), uint256(expectedCode), "errCode[0]");
    }
}
