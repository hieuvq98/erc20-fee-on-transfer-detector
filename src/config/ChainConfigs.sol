// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity =0.8.18;

import {ValidatorConfig} from "../TokenValidator.sol";

/// @notice Ready-made `ValidatorConfig`s so deploying to a new chain is a one-liner and the
///         generated constructor arguments are reproducible.
/// @dev    Only the singleton designs appear here. Uniswap V2 and V3 style pools need no
///         configuration at all: they are named directly and expose their own
///         `token0`/`token1`, so the same bytecode measures them on any chain and any fork.
///
///         A singleton left at `address(0)` disables that family: its entry points report
///         `ErrorCode.PoolInvalid` instead of reverting in a confusing way.
library ChainConfigs {
    /// @dev Storage slot of `mapping(PoolId => Pool.State) pools` in the Uniswap V4
    ///      `PoolManager`. Matches `StateLibrary.POOLS_SLOT`.
    uint256 internal constant UNISWAP_V4_POOLS_SLOT = 6;

    /// @notice BNB Smart Chain. Uniswap V4 is deployed here alongside PancakeSwap Infinity,
    ///         and both are reachable through their own entry points.
    /// @dev    The sell fee reference is PancakeSwap's V2 factory, which is what the
    ///         validator has always used - keeping it makes results comparable with earlier
    ///         deployments. Any address that is neither a pool nor blacklisted works.
    function bsc() internal pure returns (ValidatorConfig memory) {
        return ValidatorConfig({
            sellFeeReferenceRecipient: 0xcA143Ce32Fe78f1f7019d7d551a6402fC5350c73, // factory
            poolManagerV4: 0x28e2Ea090877bF75740558f6BFB36A5ffeE9e9dF,
            positionManagerV4: 0x7A4a5c919aE2541AeD11041A1AEeE68f1287f95b,
            v4PoolsSlot: UNISWAP_V4_POOLS_SLOT,
            infinityVault: 0x238a358808379702088667322f80aC48bAd5e6c4,
            infinityCLPoolManager: 0xa0FfB9c1CE1Fe56963B0321B32E7A0302114058b
        });
    }

    /// @notice Ethereum mainnet. No Infinity deployment.
    function ethereum() internal pure returns (ValidatorConfig memory) {
        return ValidatorConfig({
            sellFeeReferenceRecipient: 0x5C69bEe701ef814a2B6a3EDD4B1652CB9cc5aA6f, // factory
            poolManagerV4: 0x000000000004444c5dc75cB358380D2e3dE08A90,
            positionManagerV4: 0xbD216513d74C8cf14cf4747E6AaA6420FF64ee9e,
            v4PoolsSlot: UNISWAP_V4_POOLS_SLOT,
            infinityVault: address(0),
            infinityCLPoolManager: address(0)
        });
    }

    /// @notice Base.
    /// @dev    `positionManagerV4` is unset: it was not verified on chain, so the
    ///         `validateV4ByPoolId` path is disabled here until an address is supplied.
    ///         `validateV4ByPoolKey` works regardless - it needs no registry.
    function base() internal pure returns (ValidatorConfig memory) {
        return ValidatorConfig({
            sellFeeReferenceRecipient: 0x8909Dc15e40173Ff4699343b6eB8132c65e18eC6,
            poolManagerV4: 0x498581fF718922c3f8e6A244956aF099B2652b2b,
            positionManagerV4: 0x7C5f5A4bBd8fD63184577525326123B519429bDc,
            v4PoolsSlot: UNISWAP_V4_POOLS_SLOT,
            infinityVault: address(0),
            infinityCLPoolManager: address(0)
        });
    }

    /// @notice Viction. V3 style pools only, which need no configuration - so the only
    ///         field that matters is the sell fee reference.
    function viction() internal pure returns (ValidatorConfig memory) {
        return ValidatorConfig({
            sellFeeReferenceRecipient: 0x1F09b50e8cbAed8A157fEe28716d13AfE36A77E7,
            poolManagerV4: address(0),
            positionManagerV4: address(0),
            v4PoolsSlot: UNISWAP_V4_POOLS_SLOT,
            infinityVault: address(0),
            infinityCLPoolManager: address(0)
        });
    }
}
