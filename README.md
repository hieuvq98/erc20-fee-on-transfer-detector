# ERC20 fee-on-transfer detector

Measures the buy / sell tax of an ERC20 by flash-borrowing it from a pool, immediately
transferring it back, and reverting so nothing is ever settled. The measurement is carried
out of the callback as revert data.

**You name the pool.** This contract does no discovery — see
[Why there is no pool discovery](#why-there-is-no-pool-discovery).

## Entry points

| Pool shape | Single | Batch |
| --- | --- | --- |
| Uniswap V2 style | `validateV2ByPool(token, pair, amount)` | `batchValidateV2ByPools` |
| Uniswap V3 style | `validateV3ByPool(token, pool, amount)` | `batchValidateV3ByPools` |
| Uniswap V4 | `validateV4ByPoolId(token, poolId, amount)` | `batchValidateV4ByPoolIds` |
| PancakeSwap Infinity CL | `validateInfinityCLByPoolId(token, poolId, amount)` | `batchValidateInfinityCLByPoolIds` |

Batch calls take parallel arrays — `tokens[i]` is measured against `pools[i]` / `poolIds[i]` —
and report an `ErrorCode` per token instead of reverting, so one bad token never fails the
batch. Mismatched lengths revert with `ArrayLengthMismatch`.

For V4 and Infinity the pool key is read back on chain from the id
(`PositionManager.poolKeys(bytes25)` and `CLPoolManager.poolIdToPoolKey(bytes32)`), exposed as
`v4PoolKey(poolId)` and `infinityCLPoolKey(poolId)`. Two escape hatches take the full key
instead, deriving the id themselves and consulting no registry:

```solidity
validateV4ByPoolKey(token, V4PoolKey(currency0, currency1, fee, tickSpacing, hooks), amount)
validateInfinityCLByPoolKey(token, InfinityPoolKey(currency0, currency1, hooks, poolManager, fee, parameters), amount)
```

Use them when V4's registry misses — it only records pools that had a position minted through
the canonical position manager.

Every path checks that the pool actually lists the token, so a wrong or stale pool fails as
`PoolInvalid` rather than returning a meaningless number.

### Native currency

V4 and Infinity spell the chain's native currency (ETH, BNB) as `address(0)`, and their
deepest pools are native-paired. That is handled transparently: the native side is just a
component of the pool key, never something this contract transfers. The **token under test**
must be a real ERC20 — native currency has no transfer fee — so `address(0)` there reverts
with `NativeCurrencyNotSupported`.

### Result

```solidity
struct TokenFees {
    uint256 buyFeeBpsForPair;     // tax taken when the pool sends the token out
    uint256 sellFeeBpsForPair;    // tax taken when the token is sent back to the pool
    uint256 sellFeeBpsForFactory; // tax taken when the token is sent to a neutral address
    ErrorCode[] errCode;
}
```

`sellFeeBpsForFactory` is measured against `sellFeeReferenceRecipient()`. The name is kept for
ABI compatibility; the address no longer has to be a factory.

A token can be taxed differently by different pools — on BSC, `0x3CB2…` charges 200 bps
against its USDT pair and nothing against its WBNB pair. There is no single "the fee of this
token", which is why the pool is an input rather than something to search for.

### Error codes

Indices are part of the ABI. Members are never reordered, and a removed member leaves its slot
reserved, so every code keeps the index it has always had.

| # | Code | Meaning |
| --- | --- | --- |
| 0 | `NoError` | measurement succeeded |
| 1 | `Deprecated_SameToken` | reserved; cannot occur now the caller names the pool |
| 2 | `PoolInvalid` | zero/non-pool address, pool does not list the token, or unknown/stale pool id |
| 3 | `InsufficientOutputAmount` | the pool rejected a zero-size loan |
| 4 | `InsufficientLiquidity` | the pool exists but cannot lend the requested amount |
| 5 | `TransferFailed1` | the pool could not send the token to the detector |
| 6 | `TransferFailed2` | the detector could not send the token back to the pool |
| 7 | `TransferFailed3` | the detector could not send the token to the reference recipient |
| 8 | `Others` | anything else, including running out of gas |

Slot 2 was previously named `PairLookupFailed` and meant the same thing.

## Why there is no pool discovery

An earlier design looked pools up itself: a factory for V2/V3, a fee-tier table for
V4/Infinity. The table half does not work, and cannot be made to work.

A Uniswap V4 or Infinity LP fee is a free 24-bit value capped at `1_000_000` — not one of a
handful of tiers the way Uniswap V3 fees are (V3's factory enforces
`feeAmountTickSpacing[fee] != 0`). The live, hookless, native-paired **BNB/CAKE** Infinity pool
charges **fee 335**:

```
poolId 0xd1fab6f2f0547468575ecf8b24d70014b4091218cd5c9983853771bad9a0190b
  currency0   0x0000…0000  (native BNB)
  currency1   CAKE
  hooks       0x0000…0000
  poolManager CLPoolManager
  fee         335
  parameters  0x…010000    (tick spacing 1, packed at bit 16)
```

Nothing about 335 is guessable. Infinity also does not tie a tick spacing to a fee —
`USDT/WBNB` exists at fee 500 with both tick spacing 10 *and* 60 — and a hooked pool carries
its hook address and registration bitmap in the key as well. A table produces false "no pool"
answers that are indistinguishable from real ones.

Since the off-chain indexer already knows the pools, it passes them in. That also makes V2 and
V3 need no configuration whatsoever, and reaches pools discovery never could — a pair no
factory lists, for instance.

## Per-chain configuration

Only the singleton designs need addresses, because there the contract that custodies the
tokens is not the pool. V2 and V3 style pools are named directly and expose their own
`token0`/`token1`, so the same bytecode measures them on any chain and any fork.

```solidity
struct ValidatorConfig {
    address sellFeeReferenceRecipient; // required; must not be address(0)
    address poolManagerV4;             // Uniswap V4 singleton
    address positionManagerV4;         // Uniswap V4 pool-key registry
    uint256 v4PoolsSlot;               // 6 on Uniswap V4
    address infinityVault;             // Infinity Vault (custodies currencies)
    address infinityCLPoolManager;     // Infinity CL pool registry
}
```

A singleton left at `address(0)` disables that family: its entry points report `PoolInvalid`.
`sellFeeReferenceRecipient` must be set — `address(0)` is a burn address many tokens reject,
which would surface as a token defect rather than a configuration mistake, so the constructor
refuses it.

`src/config/ChainConfigs.sol` holds presets: `bsc()`, `ethereum()`, `base()`, `viction()`.

## Usage

```shell
forge build
forge test                              # unit tests + BSC and Ethereum fork tests
forge test --no-match-contract Fork     # unit tests only, no network needed
```

Deploy — the preset is chosen from `block.chainid` and any field can be overridden through the
environment:

```shell
forge script script/Deploy.s.sol:DeployScript --rpc-url $RPC --broadcast
```

Recognised overrides: `SELL_FEE_REFERENCE_RECIPIENT`, `POOL_MANAGER_V4`,
`POSITION_MANAGER_V4`, `V4_POOLS_SLOT`, `INFINITY_VAULT`, `INFINITY_CL_POOL_MANAGER`.

Fork tests read `BSC_RPC_URL` and `ETH_RPC_URL`, falling back to public endpoints.
