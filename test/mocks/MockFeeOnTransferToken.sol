// SPDX-License-Identifier: MIT
pragma solidity =0.8.18;

import "solmate/tokens/ERC20.sol";

/// @notice ERC20 whose transfer tax depends on which side of a pool the transfer touches.
/// @dev    The three knobs map one-to-one onto the three fields of `TokenFees`:
///         - buy fee       pool -> anyone    => `buyFeeBpsForPair`
///         - sell fee      anyone -> pool    => `sellFeeBpsForPair`
///         - transfer fee  everything else   => `sellFeeBpsForFactory`
///         A pool can override the buy/sell fees so that multi-pool merging can be tested.
contract MockFeeOnTransferToken is ERC20 {
    uint256 internal constant BPS = 10_000;

    uint256 public buyFeeBps;
    uint256 public sellFeeBps;
    uint256 public transferFeeBps;

    mapping(address => bool) public isPool;
    mapping(address => bool) public hasPoolOverride;
    mapping(address => uint256) public poolBuyFeeBps;
    mapping(address => uint256) public poolSellFeeBps;
    mapping(address => bool) public isBlocked;

    constructor(
        string memory name_,
        string memory symbol_,
        uint256 buyFeeBps_,
        uint256 sellFeeBps_,
        uint256 transferFeeBps_
    ) ERC20(name_, symbol_, 18) {
        buyFeeBps = buyFeeBps_;
        sellFeeBps = sellFeeBps_;
        transferFeeBps = transferFeeBps_;
    }

    function mint(address to, uint256 amount) external {
        _mint(to, amount);
    }

    /// @notice Registers `pool` so that transfers in and out of it are taxed at the
    ///         contract wide buy / sell rates.
    function setPool(address pool, bool value) external {
        isPool[pool] = value;
    }

    /// @notice Registers `pool` with its own buy / sell rates.
    function setPoolWithFees(address pool, uint256 buyBps, uint256 sellBps) external {
        isPool[pool] = true;
        hasPoolOverride[pool] = true;
        poolBuyFeeBps[pool] = buyBps;
        poolSellFeeBps[pool] = sellBps;
    }

    /// @notice Makes every transfer to `account` revert, to exercise the TransferFailed paths.
    function setBlocked(address account, bool value) external {
        isBlocked[account] = value;
    }

    function transfer(address to, uint256 amount) public override returns (bool) {
        _taxedTransfer(msg.sender, to, amount);
        return true;
    }

    function transferFrom(address from, address to, uint256 amount) public override returns (bool) {
        uint256 allowed = allowance[from][msg.sender];
        if (allowed != type(uint256).max) allowance[from][msg.sender] = allowed - amount;
        _taxedTransfer(from, to, amount);
        return true;
    }

    function _feeBpsFor(address from, address to) internal view returns (uint256) {
        if (isPool[from]) {
            return hasPoolOverride[from] ? poolBuyFeeBps[from] : buyFeeBps;
        }
        if (isPool[to]) {
            return hasPoolOverride[to] ? poolSellFeeBps[to] : sellFeeBps;
        }
        return transferFeeBps;
    }

    function _taxedTransfer(address from, address to, uint256 amount) internal {
        require(!isBlocked[to], "MockToken: BLOCKED");

        uint256 fee = (amount * _feeBpsFor(from, to)) / BPS;

        balanceOf[from] -= amount;
        unchecked {
            balanceOf[to] += amount - fee;
            totalSupply -= fee; // the tax is burnt
        }

        emit Transfer(from, to, amount - fee);
    }
}
