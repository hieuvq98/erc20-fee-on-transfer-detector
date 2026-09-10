// SPDX-License-Identifier: MIT
pragma solidity =0.8.18;

import "forge-std/Test.sol";
import "../src/TokenValidator.sol";
import "../src/config/ChainConfigs.sol";

/// @notice Fork tests against real pools on BNB Smart Chain.
contract TokenValidatorBscForkTest is Test {
    uint256 internal constant AMOUNT_TO_BORROW = 10_000;

    address internal constant WBNB = 0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c;
    address internal constant USDT = 0x55d398326f99059fF775485246999027B3197955;
    address internal constant USDC = 0x8AC76a51cc950d9822D68b83fE1Ad97B32Cd580d;
    address internal constant CAKE = 0x0E09FaBB73Bd3Ade0a17ECC321fD13a19e81cE82;
    address internal constant TAXED_TOKEN = 0x3CB20d96E866D128BC469a6e66505d46D7F9BaBa;
    address internal constant TAXED_V3_TOKEN = 0x3ADE350e05F631f946B6d2B1a2deAAF95DCB243a;

    /// @dev PancakeSwap V2 pairs for TAXED_TOKEN. It taxes 200 bps against USDT and nothing
    ///      against WBNB, which is why naming the pool matters.
    address internal constant TAXED_USDT_PAIR = 0x1eb23C1f06856D57BC769520cF12e9a21cB65140;
    address internal constant TAXED_WBNB_PAIR = 0x1e6063857722F81FD8967F119881F7bE3475A428;
    /// @dev PancakeSwap V3 pool, TAXED_TOKEN/USDT at fee 10000. Exists but is thin.
    address internal constant TAXED_USDT_V3_POOL = 0x50819e10F3Ca401b742A9aD9F984A84Db2261Ead;
    /// @dev PancakeSwap V3 pool, TAXED_V3_TOKEN/WBNB at fee 2500.
    address internal constant TAXED_V3_WBNB_POOL = 0x18B9a211b6bB1Ed6b0F1da36D0cBe2a2201B9a25;

    /// @dev Live hookless, native-paired BNB/CAKE Infinity CL pool: fee 335, tick spacing 1.
    bytes32 internal constant CAKE_BNB_POOL_ID = 0xd1fab6f2f0547468575ecf8b24d70014b4091218cd5c9983853771bad9a0190b;

    TokenValidator internal validator;

    function setUp() public {
        vm.selectFork(vm.createFork(vm.envOr("BSC_RPC_URL", string("https://bsc.blockrazor.xyz"))));
        validator = new TokenValidator(ChainConfigs.bsc());
    }

    function _one(address item) internal pure returns (address[] memory list) {
        list = new address[](1);
        list[0] = item;
    }

    function _one(bytes32 item) internal pure returns (bytes32[] memory list) {
        list = new bytes32[](1);
        list[0] = item;
    }

    function _assertFees(TokenFees memory fees, uint256 buy, uint256 sellPool, uint256 sellReference, ErrorCode code)
        internal
    {
        assertEq(fees.buyFeeBpsForPair, buy, "buyFeeBpsForPair");
        assertEq(fees.sellFeeBpsForPair, sellPool, "sellFeeBpsForPair");
        assertEq(fees.sellFeeBpsForFactory, sellReference, "sellFeeBpsForFactory");
        assertEq(uint256(fees.errCode[0]), uint256(code), "errCode[0]");
    }

    /*//////////////////////////////////////////////////////////////
                             CONFIGURATION
    //////////////////////////////////////////////////////////////*/

    function test_BscConfig() public {
        assertEq(validator.poolManagerV4(), 0x28e2Ea090877bF75740558f6BFB36A5ffeE9e9dF, "uniswap v4");
        assertEq(validator.positionManagerV4(), 0x7A4a5c919aE2541AeD11041A1AEeE68f1287f95b, "v4 registry");
        assertEq(validator.infinityVault(), 0x238a358808379702088667322f80aC48bAd5e6c4, "infinity vault");
        assertEq(validator.infinityCLPoolManager(), 0xa0FfB9c1CE1Fe56963B0321B32E7A0302114058b, "infinity CL");
        assertEq(validator.v4PoolsSlot(), 6, "StateLibrary.POOLS_SLOT");
    }

    /*//////////////////////////////////////////////////////////////
                                   V2
    //////////////////////////////////////////////////////////////*/

    function test_V2_MeasuresATaxedToken() public {
        _assertFees(
            validator.validateV2ByPool(TAXED_TOKEN, TAXED_USDT_PAIR, AMOUNT_TO_BORROW), 200, 200, 0, ErrorCode.NoError
        );
    }

    /// @notice The same token is taxed differently per pool. Naming the pool is the whole
    ///         point: a single "the fee of this token" answer would be wrong.
    function test_V2_EachPoolIsMeasuredSeparately() public {
        _assertFees(
            validator.validateV2ByPool(TAXED_TOKEN, TAXED_USDT_PAIR, AMOUNT_TO_BORROW), 200, 200, 0, ErrorCode.NoError
        );
        _assertFees(
            validator.validateV2ByPool(TAXED_TOKEN, TAXED_WBNB_PAIR, AMOUNT_TO_BORROW), 0, 0, 0, ErrorCode.NoError
        );
    }

    function test_V2_BatchReportsPerTokenErrors() public {
        TokenFees[] memory fees =
            validator.batchValidateV2ByPools(_one(TAXED_TOKEN), _one(TAXED_USDT_PAIR), AMOUNT_TO_BORROW, 10_000_000);
        _assertFees(fees[0], 200, 200, 0, ErrorCode.NoError);

        TokenFees[] memory bad =
            validator.batchValidateV2ByPools(_one(USDC), _one(TAXED_USDT_PAIR), AMOUNT_TO_BORROW, 10_000_000);
        _assertFees(bad[0], 0, 0, 0, ErrorCode.PoolInvalid);
    }

    function test_V2_PoolThatDoesNotListTheTokenIsRejected() public {
        vm.expectRevert(TokenValidator.PoolInvalid.selector);
        validator.validateV2ByPool(USDC, TAXED_USDT_PAIR, AMOUNT_TO_BORROW);
    }

    /*//////////////////////////////////////////////////////////////
                                   V3
    //////////////////////////////////////////////////////////////*/

    function test_V3_MeasuresATaxedToken() public {
        _assertFees(
            validator.validateV3ByPool(TAXED_V3_TOKEN, TAXED_V3_WBNB_POOL, AMOUNT_TO_BORROW),
            100,
            100,
            100,
            ErrorCode.NoError
        );
    }

    function test_V3_PoolThatDoesNotListTheTokenIsRejected() public {
        vm.expectRevert(TokenValidator.PoolInvalid.selector);
        validator.validateV3ByPool(USDC, TAXED_V3_WBNB_POOL, AMOUNT_TO_BORROW);
    }

    function test_V3_ThinPoolIsInsufficientLiquidity() public {
        TokenFees[] memory fees =
            validator.batchValidateV3ByPools(_one(TAXED_TOKEN), _one(TAXED_USDT_V3_POOL), AMOUNT_TO_BORROW, 10_000_000);
        _assertFees(fees[0], 0, 0, 0, ErrorCode.InsufficientLiquidity);
    }

    /*//////////////////////////////////////////////////////////////
                                UNISWAP V4
    //////////////////////////////////////////////////////////////*/

    function test_V4_MeasuresByPoolId() public {
        bytes32 poolId = keccak256(abi.encode(USDT, WBNB, uint24(500), int24(10), address(0)));

        (address currency0, address currency1, uint24 fee, int24 tickSpacing, address hooks) =
            validator.v4PoolKey(poolId);
        assertEq(currency0, USDT);
        assertEq(currency1, WBNB);
        assertEq(fee, 500);
        assertEq(tickSpacing, 10);
        assertEq(hooks, address(0));

        _assertFees(validator.validateV4ByPoolId(USDT, poolId, AMOUNT_TO_BORROW), 0, 0, 0, ErrorCode.NoError);
    }

    function test_V4_MeasuresByPoolKeyWithoutTheRegistry() public {
        V4PoolKey memory key =
            V4PoolKey({currency0: USDT, currency1: WBNB, fee: 500, tickSpacing: 10, hooks: address(0)});

        _assertFees(validator.validateV4ByPoolKey(USDT, key, AMOUNT_TO_BORROW), 0, 0, 0, ErrorCode.NoError);
    }

    /*//////////////////////////////////////////////////////////////
                            PANCAKESWAP INFINITY
    //////////////////////////////////////////////////////////////*/

    /// @notice The pool that made the tier-table approach untenable: hookless, native-paired,
    ///         tick spacing 1, and an LP fee of 335 that no table would ever guess.
    function test_Infinity_ReadsTheKeyBackFromThePoolManager() public {
        (address currency0, address currency1, address hooks, address poolManager, uint24 fee, bytes32 parameters) =
            validator.infinityCLPoolKey(CAKE_BNB_POOL_ID);

        assertEq(currency0, address(0), "native BNB");
        assertEq(currency1, CAKE, "CAKE");
        assertEq(hooks, address(0), "hookless");
        assertEq(poolManager, 0xa0FfB9c1CE1Fe56963B0321B32E7A0302114058b);
        assertEq(fee, 335, "arbitrary 24-bit fee, not a tier");
        assertEq(uint256(parameters), uint256(1) << 16, "tick spacing 1, packed at bit 16");
    }

    function test_Infinity_MeasuresByPoolId() public {
        _assertFees(
            validator.validateInfinityCLByPoolId(CAKE, CAKE_BNB_POOL_ID, AMOUNT_TO_BORROW), 0, 0, 0, ErrorCode.NoError
        );
    }

    /// @notice Deriving the id from the key must reproduce the id observed on chain,
    ///         `poolManager` word included - dropping it would not.
    function test_Infinity_PoolIdDerivationMatchesTheChain() public {
        InfinityPoolKey memory key = InfinityPoolKey({
            currency0: address(0),
            currency1: CAKE,
            hooks: address(0),
            poolManager: 0xa0FfB9c1CE1Fe56963B0321B32E7A0302114058b,
            fee: 335,
            parameters: bytes32(uint256(1) << 16)
        });

        assertEq(validator.infinityPoolId(key), CAKE_BNB_POOL_ID);
        _assertFees(validator.validateInfinityCLByPoolKey(CAKE, key, AMOUNT_TO_BORROW), 0, 0, 0, ErrorCode.NoError);
    }

    function test_Infinity_RejectsAnUnrelatedToken() public {
        vm.expectRevert(TokenValidator.PoolInvalid.selector);
        validator.validateInfinityCLByPoolId(USDT, CAKE_BNB_POOL_ID, AMOUNT_TO_BORROW);
    }

    function test_Infinity_BatchByPoolIds() public {
        TokenFees[] memory fees = validator.batchValidateInfinityCLByPoolIds(
            _one(CAKE), _one(CAKE_BNB_POOL_ID), AMOUNT_TO_BORROW, 10_000_000
        );
        _assertFees(fees[0], 0, 0, 0, ErrorCode.NoError);
    }

    function test_Infinity_StalePoolIdIsPoolInvalid() public {
        TokenFees[] memory fees = validator.batchValidateInfinityCLByPoolIds(
            _one(CAKE), _one(bytes32(uint256(0xdead))), AMOUNT_TO_BORROW, 10_000_000
        );
        _assertFees(fees[0], 0, 0, 0, ErrorCode.PoolInvalid);
    }

    /*//////////////////////////////////////////////////////////////
                        UNISWAP V4 AND INFINITY COEXIST
    //////////////////////////////////////////////////////////////*/

    function test_BothSingletonsAreReachableOnBsc() public {
        bytes32 v4Id = keccak256(abi.encode(USDT, WBNB, uint24(500), int24(10), address(0)));

        _assertFees(validator.validateV4ByPoolId(USDT, v4Id, AMOUNT_TO_BORROW), 0, 0, 0, ErrorCode.NoError);
        _assertFees(
            validator.validateInfinityCLByPoolId(CAKE, CAKE_BNB_POOL_ID, AMOUNT_TO_BORROW), 0, 0, 0, ErrorCode.NoError
        );
    }
}

/// @notice Fork tests against the real Uniswap V4 deployment on Ethereum.
contract TokenValidatorEthereumForkTest is Test {
    uint256 internal constant AMOUNT_TO_BORROW = 10_000; // 0.01 USDC

    address internal constant USDC = 0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48;
    address internal constant WETH = 0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2;

    TokenValidator internal validator;

    function setUp() public {
        vm.selectFork(vm.createFork(vm.envOr("ETH_RPC_URL", string("https://ethereum-rpc.publicnode.com"))));
        validator = new TokenValidator(ChainConfigs.ethereum());
    }

    function test_EthereumConfig() public view {
        assertEq(validator.poolManagerV4(), 0x000000000004444c5dc75cB358380D2e3dE08A90);
        assertEq(validator.positionManagerV4(), 0xbD216513d74C8cf14cf4747E6AaA6420FF64ee9e);
        assertEq(validator.infinityVault(), address(0), "no Infinity on mainnet");
    }

    /// @notice The largest V4 pools are paired against native ETH, spelled `address(0)`.
    function test_V4_NativeEthPool() public {
        bytes32 poolId = keccak256(abi.encode(address(0), USDC, uint24(500), int24(10), address(0)));

        (address currency0, address currency1,,,) = validator.v4PoolKey(poolId);
        assertEq(currency0, address(0), "native ETH");
        assertEq(currency1, USDC);

        TokenFees memory fees = validator.validateV4ByPoolId(USDC, poolId, AMOUNT_TO_BORROW);
        assertEq(fees.buyFeeBpsForPair, 0, "USDC has no buy tax");
        assertEq(fees.sellFeeBpsForPair, 0, "USDC has no sell tax");
        assertEq(uint256(fees.errCode[0]), uint256(ErrorCode.NoError));
    }

    function test_V4_ByPoolKeyNeedsNoRegistry() public {
        V4PoolKey memory key =
            V4PoolKey({currency0: address(0), currency1: USDC, fee: 500, tickSpacing: 10, hooks: address(0)});

        TokenFees memory fees = validator.validateV4ByPoolKey(USDC, key, AMOUNT_TO_BORROW);
        assertEq(uint256(fees.errCode[0]), uint256(ErrorCode.NoError));
    }

    function test_V4_ErcToErcPool() public {
        bytes32 poolId = keccak256(abi.encode(USDC, WETH, uint24(500), int24(10), address(0)));

        TokenFees memory fees = validator.validateV4ByPoolId(USDC, poolId, AMOUNT_TO_BORROW);
        assertEq(uint256(fees.errCode[0]), uint256(ErrorCode.NoError));
    }
}

/// @notice Fork tests against real pools on Base.
contract TokenValidatorBaseForkTest is Test {
    uint256 internal constant AMOUNT_TO_BORROW = 10_000;

    address internal constant WETH = 0x4200000000000000000000000000000000000006;
    address internal constant VIRTUAL = 0x0b3e328455c4059EEb9e3f84b5543F74E24e7E1b;
    /// @dev A token that taxes DEX trades but not plain transfers.
    address internal constant VPAY = 0x98aC5B33A4Ef1151f138941c979211599c2fF953;
    /// @dev Uniswap V2 style VPAY/VIRTUAL pair. Note it is NOT the token's WETH pair, so a
    ///      WETH-based discovery would never have found it - naming the pool does.
    address internal constant VPAY_VIRTUAL_PAIR = 0xDEb75B16307E4c3Ddb6f6731C303E15CC16A8E82;

    TokenValidator internal validator;

    function setUp() public {
        vm.selectFork(vm.createFork(vm.envOr("BASE_RPC_URL", string("https://mainnet.base.org"))));
        validator = new TokenValidator(ChainConfigs.base());
    }

    function test_V2_MeasuresATaxedTokenOnItsNonWethPair() public {
        TokenFees memory fees = validator.validateV2ByPool(VPAY, VPAY_VIRTUAL_PAIR, AMOUNT_TO_BORROW);

        assertEq(fees.buyFeeBpsForPair, 100, "1% out of the pool");
        assertEq(fees.sellFeeBpsForPair, 100, "1% back into the pool");
        assertEq(fees.sellFeeBpsForFactory, 0, "plain transfers are untaxed");
        assertEq(uint256(fees.errCode[0]), uint256(ErrorCode.NoError));
    }

    /// @notice The pair holds VPAY as token1, so the token1 branch is exercised on a real pool.
    function test_V2_TokenIsToken1OfTheRealPair() public {
        (, address token1) = (address(0), _token1(VPAY_VIRTUAL_PAIR));
        assertEq(token1, VPAY, "VPAY sorts second");
    }

    function test_V2_PairThatDoesNotListTheTokenIsRejected() public {
        vm.expectRevert(TokenValidator.PoolInvalid.selector);
        validator.validateV2ByPool(WETH, VPAY_VIRTUAL_PAIR, AMOUNT_TO_BORROW);
    }

    function test_BaseConfig() public view {
        assertEq(validator.poolManagerV4(), 0x498581fF718922c3f8e6A244956aF099B2652b2b);
        assertEq(validator.positionManagerV4(), 0x7C5f5A4bBd8fD63184577525326123B519429bDc);
    }

    function _token1(address pair) internal view returns (address) {
        (, bytes memory data) = pair.staticcall(abi.encodeWithSignature("token1()"));
        return abi.decode(data, (address));
    }
}
