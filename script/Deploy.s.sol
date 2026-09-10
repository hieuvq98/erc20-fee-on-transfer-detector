// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.18;

import {Script, console2} from "forge-std/Script.sol";
import {TokenValidator, ValidatorConfig} from "../src/TokenValidator.sol";
import {ChainConfigs} from "../src/config/ChainConfigs.sol";

/// @notice Deploys a `TokenValidator` configured for one chain.
/// @dev    The preset is picked from `block.chainid` and every field can be overridden
///         through the environment, so the same source produces per-chain constructor
///         arguments and therefore per-chain deployment bytecode.
contract DeployScript is Script {
    function setUp() public {}

    function run() public returns (TokenValidator validator) {
        ValidatorConfig memory config = resolveConfig();

        vm.broadcast();
        validator = new TokenValidator(config);

        console2.log("TokenValidator       ", address(validator));
        console2.log("  sellFeeReference   ", config.sellFeeReferenceRecipient);
        console2.log("  poolManagerV4      ", config.poolManagerV4);
        console2.log("  positionManagerV4  ", config.positionManagerV4);
        console2.log("  infinityVault      ", config.infinityVault);
        console2.log("  infinityCLPoolMgr  ", config.infinityCLPoolManager);
    }

    /// @notice Preset for the current chain, with environment overrides applied.
    function resolveConfig() public view returns (ValidatorConfig memory config) {
        config = presetFor(block.chainid);

        config.sellFeeReferenceRecipient = vm.envOr("SELL_FEE_REFERENCE_RECIPIENT", config.sellFeeReferenceRecipient);
        config.poolManagerV4 = vm.envOr("POOL_MANAGER_V4", config.poolManagerV4);
        config.positionManagerV4 = vm.envOr("POSITION_MANAGER_V4", config.positionManagerV4);
        config.v4PoolsSlot = vm.envOr("V4_POOLS_SLOT", config.v4PoolsSlot);
        config.infinityVault = vm.envOr("INFINITY_VAULT", config.infinityVault);
        config.infinityCLPoolManager = vm.envOr("INFINITY_CL_POOL_MANAGER", config.infinityCLPoolManager);
    }

    function presetFor(uint256 chainId) public pure returns (ValidatorConfig memory) {
        if (chainId == 56) return ChainConfigs.bsc();
        if (chainId == 1) return ChainConfigs.ethereum();
        if (chainId == 8453) return ChainConfigs.base();
        if (chainId == 88) return ChainConfigs.viction();

        // Unknown chain: everything must come from the environment. The sell fee reference
        // is mandatory, so a bare deployment fails loudly rather than measuring against
        // address(0).
        return ValidatorConfig({
            sellFeeReferenceRecipient: address(0),
            poolManagerV4: address(0),
            positionManagerV4: address(0),
            v4PoolsSlot: ChainConfigs.UNISWAP_V4_POOLS_SLOT,
            infinityVault: address(0),
            infinityCLPoolManager: address(0)
        });
    }
}
