// SPDX-License-Identifier: MIT
pragma solidity =0.8.18;

import "./TokenValidatorBase.t.sol";

/// @notice Deterministic, fork-free tests for the whole validator surface.
contract TokenValidatorTest is TokenValidatorBaseTest {
    /*//////////////////////////////////////////////////////////////
                             CONFIGURATION
    //////////////////////////////////////////////////////////////*/

    function test_ConstructorStoresChainConfiguration() public {
        assertEq(validator.sellFeeReferenceRecipient(), REFERENCE_RECIPIENT);
        assertEq(validator.poolManagerV4(), address(poolManagerV4));
        assertEq(validator.positionManagerV4(), address(positionManagerV4Registry));
        assertEq(validator.v4PoolsSlot(), ChainConfigs.UNISWAP_V4_POOLS_SLOT);
        assertEq(validator.infinityVault(), address(infinityVault));
        assertEq(validator.infinityCLPoolManager(), address(infinityCLPoolManager));
    }

    /// @notice `address(0)` as the sell fee reference would look like a token defect, since
    ///         many tokens reject transfers to the zero address. Fail at construction.
    function test_ConstructorRejectsAMissingSellFeeReference() public {
        ValidatorConfig memory config = defaultConfig();
        config.sellFeeReferenceRecipient = address(0);

        vm.expectRevert(TokenValidator.MissingSellFeeReferenceRecipient.selector);
        new TokenValidator(config);
    }

    /// @notice V2 and V3 need no configuration at all: the pool is named and answers
    ///         token0/token1 itself.
    function test_V2AndV3NeedNoConfiguration() public {
        ValidatorConfig memory bare = ValidatorConfig({
            sellFeeReferenceRecipient: REFERENCE_RECIPIENT,
            poolManagerV4: address(0),
            positionManagerV4: address(0),
            v4PoolsSlot: 0,
            infinityVault: address(0),
            infinityCLPoolManager: address(0)
        });
        TokenValidator unconfigured = new TokenValidator(bare);

        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address pair = createV2Pair(token, baseToken, V2CallbackStyle.Pancake);
        address pool = createV3Pool(token, baseToken, 500, V3CallbackStyle.Uniswap);

        assertFees(
            unconfigured.validateV2ByPool(address(token), pair, AMOUNT_TO_BORROW), 200, 300, 100, ErrorCode.NoError
        );
        assertFees(
            unconfigured.validateV3ByPool(address(token), pool, AMOUNT_TO_BORROW), 200, 300, 100, ErrorCode.NoError
        );
    }

    function test_UnconfiguredSingletonsReportPoolInvalid() public {
        ValidatorConfig memory bare = defaultConfig();
        bare.poolManagerV4 = address(0);
        bare.positionManagerV4 = address(0);
        bare.infinityVault = address(0);
        bare.infinityCLPoolManager = address(0);
        TokenValidator unconfigured = new TokenValidator(bare);

        vm.expectRevert(TokenValidator.PoolInvalid.selector);
        unconfigured.validateV4ByPoolId(address(baseToken), bytes32(uint256(1)), AMOUNT_TO_BORROW);

        vm.expectRevert(TokenValidator.PoolInvalid.selector);
        unconfigured.validateInfinityCLByPoolId(address(baseToken), bytes32(uint256(1)), AMOUNT_TO_BORROW);
    }

    /*//////////////////////////////////////////////////////////////
                                UNISWAP V2
    //////////////////////////////////////////////////////////////*/

    function test_V2_MeasuresBuyAndSellFees() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address pair = createV2Pair(token, baseToken, V2CallbackStyle.Pancake);

        assertFees(validator.validateV2ByPool(address(token), pair, AMOUNT_TO_BORROW), 200, 300, 100, ErrorCode.NoError);
    }

    function test_V2_WorksWithUniswapCallbackName() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address pair = createV2Pair(token, baseToken, V2CallbackStyle.Uniswap);

        assertFees(validator.validateV2ByPool(address(token), pair, AMOUNT_TO_BORROW), 200, 300, 100, ErrorCode.NoError);
    }

    function test_V2_UntaxedTokenReportsZeroFees() public {
        MockFeeOnTransferToken token = newToken(0, 0, 0);
        address pair = createV2Pair(token, baseToken, V2CallbackStyle.Pancake);

        assertFees(validator.validateV2ByPool(address(token), pair, AMOUNT_TO_BORROW), 0, 0, 0, ErrorCode.NoError);
    }

    function test_V2_WorksWhenTokenIsToken1OfThePair() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        while (address(token) < address(baseToken)) {
            token = newToken(200, 300, 100);
        }
        address pair = createV2Pair(token, baseToken, V2CallbackStyle.Pancake);

        assertFees(validator.validateV2ByPool(address(token), pair, AMOUNT_TO_BORROW), 200, 300, 100, ErrorCode.NoError);
    }

    function test_V2_TransferToValidatorFailsIsTransferFailed1() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address pair = createV2Pair(token, baseToken, V2CallbackStyle.Pancake);
        token.setBlocked(address(validator), true);

        TokenFees[] memory results =
            validator.batchValidateV2ByPools(asArray(address(token)), asArray(pair), AMOUNT_TO_BORROW, GAS_LIMIT);
        assertErrorCode(results[0], ErrorCode.TransferFailed1);
    }

    function test_V2_TransferToPairFailsIsTransferFailed2() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address pair = createV2Pair(token, baseToken, V2CallbackStyle.Pancake);
        token.setBlocked(pair, true);

        TokenFees memory result = validator.validateV2ByPool(address(token), pair, AMOUNT_TO_BORROW);
        assertEq(result.buyFeeBpsForPair, 200, "buy fee still measured");
        assertEq(result.sellFeeBpsForPair, 0, "no sell fee measurable for the pool");
        assertEq(result.sellFeeBpsForFactory, 100, "reference sell fee still measured");
        assertEq(uint256(result.errCode[0]), uint256(ErrorCode.TransferFailed2));
    }

    function test_V2_TransferToReferenceFailsIsTransferFailed3() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address pair = createV2Pair(token, baseToken, V2CallbackStyle.Pancake);
        token.setBlocked(REFERENCE_RECIPIENT, true);

        TokenFees memory result = validator.validateV2ByPool(address(token), pair, AMOUNT_TO_BORROW);
        assertEq(result.sellFeeBpsForPair, 300, "pool sell fee still measured");
        assertEq(result.sellFeeBpsForFactory, 0, "no reference sell fee measurable");
        assertEq(uint256(result.errCode[0]), uint256(ErrorCode.TransferFailed3));
    }

    function test_V2_BothTransfersFailReportsBothCodes() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address pair = createV2Pair(token, baseToken, V2CallbackStyle.Pancake);
        token.setBlocked(pair, true);
        token.setBlocked(REFERENCE_RECIPIENT, true);

        TokenFees memory result = validator.validateV2ByPool(address(token), pair, AMOUNT_TO_BORROW);
        assertEq(result.errCode.length, 2, "two error codes");
        assertEq(uint256(result.errCode[0]), uint256(ErrorCode.TransferFailed2));
        assertEq(uint256(result.errCode[1]), uint256(ErrorCode.TransferFailed3));
    }

    function test_V2_InsufficientLiquidity() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address pair = createV2Pair(token, baseToken, V2CallbackStyle.Pancake);

        TokenFees[] memory results =
            validator.batchValidateV2ByPools(asArray(address(token)), asArray(pair), POOL_LIQUIDITY * 2, GAS_LIMIT);
        assertErrorCode(results[0], ErrorCode.InsufficientLiquidity);
    }

    function test_V2_InsufficientOutputAmount() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address pair = createV2Pair(token, baseToken, V2CallbackStyle.Pancake);

        TokenFees[] memory results =
            validator.batchValidateV2ByPools(asArray(address(token)), asArray(pair), 0, GAS_LIMIT);
        assertErrorCode(results[0], ErrorCode.InsufficientOutputAmount);
    }

    function test_V2_FullyTaxedTokenIsReportedInsteadOfRevertingBlind() public {
        MockFeeOnTransferToken token = newToken(10_000, 300, 100);
        address pair = createV2Pair(token, baseToken, V2CallbackStyle.Pancake);

        assertFees(
            validator.validateV2ByPool(address(token), pair, AMOUNT_TO_BORROW),
            10_000,
            10_000,
            10_000,
            ErrorCode.NoError
        );
    }

    /*//////////////////////////////////////////////////////////////
                                UNISWAP V3
    //////////////////////////////////////////////////////////////*/

    function test_V3_MeasuresBuyAndSellFees() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address pool = createV3Pool(token, baseToken, 500, V3CallbackStyle.Pancake);

        assertFees(validator.validateV3ByPool(address(token), pool, AMOUNT_TO_BORROW), 200, 300, 100, ErrorCode.NoError);
    }

    function test_V3_WorksWithUniswapCallbackName() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address pool = createV3Pool(token, baseToken, 3000, V3CallbackStyle.Uniswap);

        assertFees(validator.validateV3ByPool(address(token), pool, AMOUNT_TO_BORROW), 200, 300, 100, ErrorCode.NoError);
    }

    /// @notice Each pool is measured on its own terms: a token may tax one pool and not another.
    function test_V3_EachPoolIsMeasuredSeparately() public {
        MockFeeOnTransferToken token = newToken(0, 0, 100);
        address mild = createV3Pool(token, baseToken, 500, V3CallbackStyle.Uniswap);
        address harsh = createV3Pool(token, baseToken, 3000, V3CallbackStyle.Uniswap);

        token.setPoolWithFees(mild, 100, 100);
        token.setPoolWithFees(harsh, 400, 500);

        assertFees(validator.validateV3ByPool(address(token), mild, AMOUNT_TO_BORROW), 100, 100, 100, ErrorCode.NoError);
        assertFees(
            validator.validateV3ByPool(address(token), harsh, AMOUNT_TO_BORROW), 400, 500, 100, ErrorCode.NoError
        );
    }

    function test_V3_InsufficientLiquidity() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address pool = createV3Pool(token, baseToken, 500, V3CallbackStyle.Uniswap);

        TokenFees[] memory results =
            validator.batchValidateV3ByPools(asArray(address(token)), asArray(pool), POOL_LIQUIDITY * 2, GAS_LIMIT);
        assertErrorCode(results[0], ErrorCode.InsufficientLiquidity);
    }

    /*//////////////////////////////////////////////////////////////
                          POOL VALIDITY CHECKS
    //////////////////////////////////////////////////////////////*/

    function test_PoolInvalid_ZeroAddress() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);

        vm.expectRevert(TokenValidator.PoolInvalid.selector);
        validator.validateV2ByPool(address(token), address(0), AMOUNT_TO_BORROW);
    }

    function test_PoolInvalid_NotAPool() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);

        vm.expectRevert(TokenValidator.PoolInvalid.selector);
        validator.validateV2ByPool(address(token), address(0xdead), AMOUNT_TO_BORROW);
    }

    /// @notice A pool that does not list the token must fail loudly, not return a number.
    function test_PoolInvalid_PoolDoesNotListTheToken() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address unrelated = createV2Pair(baseToken, otherBaseToken, V2CallbackStyle.Pancake);

        vm.expectRevert(TokenValidator.PoolInvalid.selector);
        validator.validateV2ByPool(address(token), unrelated, AMOUNT_TO_BORROW);
    }

    function test_PoolInvalid_StalePoolId() public {
        vm.expectRevert(TokenValidator.PoolInvalid.selector);
        validator.validateV4ByPoolId(address(baseToken), bytes32(uint256(0xdead)), AMOUNT_TO_BORROW);

        vm.expectRevert(TokenValidator.PoolInvalid.selector);
        validator.validateInfinityCLByPoolId(address(baseToken), bytes32(uint256(0xdead)), AMOUNT_TO_BORROW);
    }

    function test_PoolInvalid_PoolIdForAnotherPair() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        bytes32 poolId = createV4Pool(baseToken, otherBaseToken, 500, 10);

        vm.expectRevert(TokenValidator.PoolInvalid.selector);
        validator.validateV4ByPoolId(address(token), poolId, AMOUNT_TO_BORROW);
    }

    function test_PoolInvalid_IsIndexTwoForBackwardCompatibility() public {
        // The slot formerly called PairLookupFailed, kept so off-chain decoding by index
        // keeps working; index 1 stays reserved where SameToken used to be.
        assertEq(uint256(ErrorCode.PoolInvalid), 2);
        assertEq(uint256(ErrorCode.Deprecated_SameToken), 1);
        assertEq(uint256(ErrorCode.InsufficientOutputAmount), 3);
        assertEq(uint256(ErrorCode.InsufficientLiquidity), 4);
        assertEq(uint256(ErrorCode.TransferFailed1), 5);
        assertEq(uint256(ErrorCode.TransferFailed2), 6);
        assertEq(uint256(ErrorCode.TransferFailed3), 7);
        assertEq(uint256(ErrorCode.Others), 8);
    }

    /*//////////////////////////////////////////////////////////////
                                UNISWAP V4
    //////////////////////////////////////////////////////////////*/

    function test_V4_MeasuresByPoolId() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        bytes32 poolId = createV4Pool(token, baseToken, 500, 10);

        assertFees(
            validator.validateV4ByPoolId(address(token), poolId, AMOUNT_TO_BORROW), 200, 300, 100, ErrorCode.NoError
        );
    }

    function test_V4_MeasuresByPoolKeyWithoutTheRegistry() public {
        ValidatorConfig memory config = defaultConfig();
        config.positionManagerV4 = address(0); // no registry at all
        TokenValidator noRegistry = new TokenValidator(config);

        MockFeeOnTransferToken token = newToken(200, 300, 100);
        createV4Pool(token, baseToken, 500, 10);

        (address c0, address c1) = address(token) < address(baseToken)
            ? (address(token), address(baseToken))
            : (address(baseToken), address(token));
        V4PoolKey memory key = V4PoolKey({currency0: c0, currency1: c1, fee: 500, tickSpacing: 10, hooks: address(0)});

        // The id path needs the registry; the key path does not.
        vm.expectRevert(TokenValidator.PoolInvalid.selector);
        noRegistry.validateV4ByPoolId(
            address(token), v4Id(address(token), address(baseToken), 500, 10), AMOUNT_TO_BORROW
        );

        assertFees(
            noRegistry.validateV4ByPoolKey(address(token), key, AMOUNT_TO_BORROW), 200, 300, 100, ErrorCode.NoError
        );
    }

    /// @notice An arbitrary fee no tier table would guess is reached without trouble.
    function test_V4_ArbitraryFee() public {
        MockFeeOnTransferToken token = newToken(150, 250, 50);
        bytes32 poolId = createV4Pool(token, baseToken, 777, 3);

        assertFees(
            validator.validateV4ByPoolId(address(token), poolId, AMOUNT_TO_BORROW), 150, 250, 50, ErrorCode.NoError
        );
    }

    function test_V4_SingletonWithoutEnoughBalanceIsInsufficientLiquidity() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        bytes32 poolId = v4Id(address(token), address(baseToken), 500, 10);
        poolManagerV4.initializePool(address(token), address(baseToken), 500, 10, address(0), 1 << 96);
        positionManagerV4Registry.register(address(token), address(baseToken), 500, 10, address(0));
        token.setPool(address(poolManagerV4), true);
        token.mint(address(poolManagerV4), AMOUNT_TO_BORROW - 1);

        vm.expectRevert(TokenValidator.InsufficientLiquidity.selector);
        validator.validateV4ByPoolId(address(token), poolId, AMOUNT_TO_BORROW);
    }

    function test_V4_PoolKeyLookupMatchesTheDerivation() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        bytes32 poolId = createV4Pool(token, baseToken, 3000, 60);

        (address c0, address c1, uint24 fee, int24 tickSpacing, address hooks) = validator.v4PoolKey(poolId);
        assertEq(fee, 3000);
        assertEq(tickSpacing, 60);
        assertEq(hooks, address(0));
        assertEq(validator.v4PoolId(V4PoolKey(c0, c1, fee, tickSpacing, hooks)), poolId);
    }

    /*//////////////////////////////////////////////////////////////
                            PANCAKESWAP INFINITY
    //////////////////////////////////////////////////////////////*/

    function test_Infinity_MeasuresByPoolId() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        bytes32 poolId = createInfinityCLPool(token, baseToken, 500, 10);

        assertFees(
            validator.validateInfinityCLByPoolId(address(token), poolId, AMOUNT_TO_BORROW),
            200,
            300,
            100,
            ErrorCode.NoError
        );
    }

    /// @notice The BNB/CAKE shape: an arbitrary 24-bit fee that no table can guess.
    function test_Infinity_ArbitraryFee() public {
        MockFeeOnTransferToken token = newToken(150, 250, 50);
        bytes32 poolId = createInfinityCLPool(token, baseToken, 335, 1);

        assertFees(
            validator.validateInfinityCLByPoolId(address(token), poolId, AMOUNT_TO_BORROW),
            150,
            250,
            50,
            ErrorCode.NoError
        );
    }

    function test_Infinity_MeasuresByPoolKey() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        createInfinityCLPool(token, baseToken, 335, 1);

        (address c0, address c1) = address(token) < address(baseToken)
            ? (address(token), address(baseToken))
            : (address(baseToken), address(token));
        InfinityPoolKey memory key = InfinityPoolKey({
            currency0: c0,
            currency1: c1,
            hooks: address(0),
            poolManager: address(infinityCLPoolManager),
            fee: 335,
            parameters: bytes32(uint256(1) << 16)
        });

        assertEq(validator.infinityPoolId(key), infinityId(address(token), address(baseToken), 335, 1));
        assertFees(
            validator.validateInfinityCLByPoolKey(address(token), key, AMOUNT_TO_BORROW),
            200,
            300,
            100,
            ErrorCode.NoError
        );
    }

    /// @notice A hooked pool is just another key; nothing special is needed.
    function test_Infinity_HookedPool() public {
        address hook = address(0xC0FFEE);
        uint16 registration = 0x0041;

        MockFeeOnTransferToken token = newToken(200, 300, 100);
        infinityCLPoolManager.initializePool(address(token), address(baseToken), hook, 500, 10, registration, 1 << 96);
        token.setPool(address(infinityVault), true);
        token.mint(address(infinityVault), POOL_LIQUIDITY);

        (address c0, address c1) = address(token) < address(baseToken)
            ? (address(token), address(baseToken))
            : (address(baseToken), address(token));
        InfinityPoolKey memory key = InfinityPoolKey({
            currency0: c0,
            currency1: c1,
            hooks: hook,
            poolManager: address(infinityCLPoolManager),
            fee: 500,
            parameters: bytes32((uint256(10) << 16) | uint256(registration))
        });

        assertFees(
            validator.validateInfinityCLByPoolKey(address(token), key, AMOUNT_TO_BORROW),
            200,
            300,
            100,
            ErrorCode.NoError
        );
    }

    function test_Infinity_VaultWithoutEnoughBalanceIsInsufficientLiquidity() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        bytes32 poolId = infinityId(address(token), address(baseToken), 500, 10);
        infinityCLPoolManager.initializePool(address(token), address(baseToken), address(0), 500, 10, 0, 1 << 96);
        token.setPool(address(infinityVault), true);
        token.mint(address(infinityVault), AMOUNT_TO_BORROW - 1);

        vm.expectRevert(TokenValidator.InsufficientLiquidity.selector);
        validator.validateInfinityCLByPoolId(address(token), poolId, AMOUNT_TO_BORROW);
    }

    function test_Infinity_PoolKeyLookupReturnsTheFullKey() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        bytes32 poolId = createInfinityCLPool(token, baseToken, 335, 1);

        (,, address hooks, address poolManager, uint24 fee, bytes32 parameters) = validator.infinityCLPoolKey(poolId);
        assertEq(hooks, address(0));
        assertEq(poolManager, address(infinityCLPoolManager));
        assertEq(fee, 335);
        assertEq(uint256(parameters), uint256(1) << 16, "tick spacing packed at bit 16");
    }

    /*//////////////////////////////////////////////////////////////
                            NATIVE CURRENCY
    //////////////////////////////////////////////////////////////*/

    /// @notice V4 and Infinity spell the native currency `address(0)`, and their deepest
    ///         pools are native-paired. It is only ever the other side of a pool.
    function test_Native_IsUsableAsTheOtherSideOfAV4Pool() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        bytes32 poolId = v4Id(address(token), address(0), 3000, 60);
        poolManagerV4.initializePool(address(token), address(0), 3000, 60, address(0), 1 << 96);
        positionManagerV4Registry.register(address(token), address(0), 3000, 60, address(0));
        token.setPool(address(poolManagerV4), true);
        token.mint(address(poolManagerV4), POOL_LIQUIDITY);

        assertFees(
            validator.validateV4ByPoolId(address(token), poolId, AMOUNT_TO_BORROW), 200, 300, 100, ErrorCode.NoError
        );
    }

    function test_Native_IsUsableAsTheOtherSideOfAnInfinityPool() public {
        MockFeeOnTransferToken token = newToken(150, 250, 50);
        bytes32 poolId = infinityId(address(token), address(0), 335, 1);
        infinityCLPoolManager.initializePool(address(token), address(0), address(0), 335, 1, 0, 1 << 96);
        token.setPool(address(infinityVault), true);
        token.mint(address(infinityVault), POOL_LIQUIDITY);

        assertFees(
            validator.validateInfinityCLByPoolId(address(token), poolId, AMOUNT_TO_BORROW),
            150,
            250,
            50,
            ErrorCode.NoError
        );
    }

    /// @notice The token under test has to be a real ERC20 - native currency has no transfer
    ///         fee to measure, and cannot be flash-borrowed as one.
    function test_Native_CannotBeTheTokenUnderTest() public {
        vm.expectRevert(TokenValidator.NativeCurrencyNotSupported.selector);
        validator.validateV2ByPool(address(0), address(0xdead), AMOUNT_TO_BORROW);

        vm.expectRevert(TokenValidator.NativeCurrencyNotSupported.selector);
        validator.validateV4ByPoolId(address(0), bytes32(0), AMOUNT_TO_BORROW);

        vm.expectRevert(TokenValidator.NativeCurrencyNotSupported.selector);
        validator.validateInfinityCLByPoolId(address(0), bytes32(0), AMOUNT_TO_BORROW);
    }

    /*//////////////////////////////////////////////////////////////
                                  BATCH
    //////////////////////////////////////////////////////////////*/

    function test_Batch_ReturnsOneResultPerToken() public {
        MockFeeOnTransferToken taxed = newToken(200, 300, 100);
        MockFeeOnTransferToken clean = newToken(0, 0, 0);
        MockFeeOnTransferToken broken = newToken(500, 500, 500);

        address[] memory tokens = new address[](3);
        tokens[0] = address(taxed);
        tokens[1] = address(clean);
        tokens[2] = address(broken);

        address[] memory pools = new address[](3);
        pools[0] = createV2Pair(taxed, baseToken, V2CallbackStyle.Pancake);
        pools[1] = createV2Pair(clean, baseToken, V2CallbackStyle.Pancake);
        pools[2] = address(0xdead); // stale / wrong pool

        TokenFees[] memory results = validator.batchValidateV2ByPools(tokens, pools, AMOUNT_TO_BORROW, GAS_LIMIT);

        assertEq(results.length, 3);
        assertFees(results[0], 200, 300, 100, ErrorCode.NoError);
        assertFees(results[1], 0, 0, 0, ErrorCode.NoError);
        assertErrorCode(results[2], ErrorCode.PoolInvalid);
    }

    function test_Batch_OutOfGasIsReportedAsOthers() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address pair = createV2Pair(token, baseToken, V2CallbackStyle.Pancake);

        TokenFees[] memory results =
            validator.batchValidateV2ByPools(asArray(address(token)), asArray(pair), AMOUNT_TO_BORROW, 5_000);
        assertErrorCode(results[0], ErrorCode.Others);
    }

    function test_Batch_LengthMismatchReverts() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address pair = createV2Pair(token, baseToken, V2CallbackStyle.Pancake);

        vm.expectRevert(TokenValidator.ArrayLengthMismatch.selector);
        validator.batchValidateV2ByPools(
            asArray(address(token), address(baseToken)), asArray(pair), AMOUNT_TO_BORROW, GAS_LIMIT
        );

        vm.expectRevert(TokenValidator.ArrayLengthMismatch.selector);
        validator.batchValidateV4ByPoolIds(
            asArray(address(token), address(baseToken)), asArray(bytes32(0)), AMOUNT_TO_BORROW, GAS_LIMIT
        );
    }

    function test_Batch_AllFourFamilies() public {
        MockFeeOnTransferToken token = newToken(200, 300, 100);
        address pair = createV2Pair(token, baseToken, V2CallbackStyle.Pancake);
        address pool = createV3Pool(token, baseToken, 500, V3CallbackStyle.Uniswap);
        bytes32 v4 = createV4Pool(token, baseToken, 500, 10);
        bytes32 inf = createInfinityCLPool(token, baseToken, 335, 1);

        address[] memory one = asArray(address(token));

        assertFees(
            validator.batchValidateV2ByPools(one, asArray(pair), AMOUNT_TO_BORROW, GAS_LIMIT)[0],
            200,
            300,
            100,
            ErrorCode.NoError
        );
        assertFees(
            validator.batchValidateV3ByPools(one, asArray(pool), AMOUNT_TO_BORROW, GAS_LIMIT)[0],
            200,
            300,
            100,
            ErrorCode.NoError
        );
        assertFees(
            validator.batchValidateV4ByPoolIds(one, asArray(v4), AMOUNT_TO_BORROW, GAS_LIMIT)[0],
            200,
            300,
            100,
            ErrorCode.NoError
        );
        assertFees(
            validator.batchValidateInfinityCLByPoolIds(one, asArray(inf), AMOUNT_TO_BORROW, GAS_LIMIT)[0],
            200,
            300,
            100,
            ErrorCode.NoError
        );
    }

    /*//////////////////////////////////////////////////////////////
                          CALLBACK ACCESS CONTROL
    //////////////////////////////////////////////////////////////*/

    function test_CallbacksRejectAnUnexpectedCaller() public {
        bytes memory payload = abi.encode(address(0xdead), address(baseToken), uint256(0), AMOUNT_TO_BORROW);

        vm.expectRevert(TokenValidator.UnexpectedCallback.selector);
        validator.pancakeCall(address(this), AMOUNT_TO_BORROW, 0, payload);

        vm.expectRevert(TokenValidator.UnexpectedCallback.selector);
        validator.uniswapV2Call(address(this), AMOUNT_TO_BORROW, 0, payload);

        vm.expectRevert(TokenValidator.UnexpectedCallback.selector);
        validator.pancakeV3FlashCallback(1, 0, payload);

        vm.expectRevert(TokenValidator.UnexpectedCallback.selector);
        validator.uniswapV3FlashCallback(1, 0, payload);

        vm.expectRevert(TokenValidator.UnexpectedCallback.selector);
        validator.unlockCallback(abi.encode(address(poolManagerV4), address(baseToken), uint256(0), AMOUNT_TO_BORROW));

        vm.expectRevert(TokenValidator.UnexpectedCallback.selector);
        validator.lockAcquired(abi.encode(address(infinityVault), address(baseToken), uint256(0), AMOUNT_TO_BORROW));
    }

    /*//////////////////////////////////////////////////////////////
                         REVERT DATA CLASSIFICATION
    //////////////////////////////////////////////////////////////*/

    function test_ErrorCodeFromCustomErrors() public {
        assertEq(
            uint256(validator.exposedErrorCodeFromReason(abi.encodeWithSelector(TokenValidator.PoolInvalid.selector))),
            uint256(ErrorCode.PoolInvalid)
        );
        assertEq(
            uint256(
                validator.exposedErrorCodeFromReason(
                    abi.encodeWithSelector(TokenValidator.InsufficientLiquidity.selector)
                )
            ),
            uint256(ErrorCode.InsufficientLiquidity)
        );
        assertEq(uint256(validator.exposedErrorCodeFromReason("")), uint256(ErrorCode.Others));
        assertEq(
            uint256(validator.exposedErrorCodeFromReason(abi.encodeWithSignature("SomethingElse()"))),
            uint256(ErrorCode.Others)
        );
    }

    /// @notice The V2 message table must work for every fork prefix, not just PancakeSwap.
    function test_ErrorCodeFromV2MessagesOfAnyFork() public {
        string[2] memory prefixes = ["Pancake: ", "UniswapV2: "];
        for (uint256 i; i < prefixes.length; ++i) {
            assertEq(
                uint256(_codeFor(string.concat(prefixes[i], "INSUFFICIENT_OUTPUT_AMOUNT"))),
                uint256(ErrorCode.InsufficientOutputAmount)
            );
            assertEq(
                uint256(_codeFor(string.concat(prefixes[i], "INSUFFICIENT_LIQUIDITY"))),
                uint256(ErrorCode.InsufficientLiquidity)
            );
            assertEq(
                uint256(_codeFor(string.concat(prefixes[i], "TRANSFER_FAILED"))), uint256(ErrorCode.TransferFailed1)
            );
        }
    }

    function test_ErrorCodeFromV3ShortMessages() public {
        assertEq(uint256(_codeFor("L")), uint256(ErrorCode.InsufficientLiquidity));
        assertEq(uint256(_codeFor("TF")), uint256(ErrorCode.TransferFailed1));
        assertEq(uint256(_codeFor("F0")), uint256(ErrorCode.Others));
        assertEq(uint256(_codeFor("")), uint256(ErrorCode.Others));
    }

    function test_RevertMessageExtractionToleratesMalformedData() public {
        assertEq(validator.exposedRevertMessage(hex"08c379a0"), "");
        bytes memory truncated = abi.encodePacked(bytes4(0x08c379a0), uint256(32), uint256(1024));
        assertEq(validator.exposedRevertMessage(truncated), "");
    }

    function test_RevertMessageExtractionMatchesAbiDecode() public {
        bytes memory encoded = abi.encodeWithSignature("Error(string)", "Pancake: INSUFFICIENT_LIQUIDITY");
        assertEq(validator.exposedRevertMessage(encoded), bytes("Pancake: INSUFFICIENT_LIQUIDITY"));
    }

    function test_EndsWith() public {
        assertTrue(validator.exposedEndsWith("Pancake: TRANSFER_FAILED", "TRANSFER_FAILED"));
        assertTrue(validator.exposedEndsWith("TRANSFER_FAILED", "TRANSFER_FAILED"));
        assertFalse(validator.exposedEndsWith("TRANSFER_FAILED_X", "TRANSFER_FAILED"));
        assertFalse(validator.exposedEndsWith("FAILED", "TRANSFER_FAILED"));
    }

    function _codeFor(string memory message) internal view returns (ErrorCode) {
        return validator.exposedErrorCodeFromReason(abi.encodeWithSignature("Error(string)", message));
    }
}
