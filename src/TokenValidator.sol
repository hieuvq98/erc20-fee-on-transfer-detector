// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity =0.8.19;
pragma abicoder v2;

import "solmate/tokens/ERC20.sol";
import "solmate/utils/SafeTransferLib.sol";
import "solmate/utils/FixedPointMathLib.sol";
import "./interfaces/IPancakePair.sol";
import "./lib/PancakeLibrary.sol";

enum ErrorCode {
    NoError,
    SameToken,
    PairLookupFailed,
    InsufficientLiquidity,
    PairTransferFailed,
    OutOfGas
}

struct TokenFees {
    uint256 buyFeeBps;
    uint256 sellFeeBps;
    bool STF;
    ErrorCode errorCode;
}

contract TokenValidator {
    using SafeTransferLib for ERC20;
    using FixedPointMathLib for uint256;

    error SameToken();
    error PairLookupFailed();
    error InsufficientLiquidity();
    error PairTransferFailed();
    error UnknownExternalTransferFailure(string reason);
    error OutOfGas();

    uint256 constant BPS = 10_000;
    address internal immutable factoryV2;
    uint256 public gasLimit;
    string internal constant STF_REVERT_STRING_SUFFIX = 'Pancake: TRANSFER_FAILED';
    string internal constant INSUFFICIENT_LIQUIDITY_REVERT_STRING_SUFFIX = 'Pancake: INSUFFICIENT_LIQUIDITY';

    address public owner;

    constructor(address _factoryV2, uint256 _gasLimit) {
        factoryV2 = _factoryV2;
        gasLimit = _gasLimit;
        owner = msg.sender;
    }

    modifier onlyOwner() {
        require(owner == msg.sender, "Sender is not owner");
        _;
    }

    function validate(address token, address baseToken, uint256 amountToBorrow)
        public
        returns (TokenFees memory fotResult)
    {
        return _validate(token, baseToken, amountToBorrow);
    }

    function batchValidate(address[] calldata tokens, address baseToken, uint256 amountToBorrow)
        public
        returns (TokenFees[] memory fotResults)
    {
        fotResults = new TokenFees[](tokens.length);
        for (uint256 i = 0; i < tokens.length; i++) {
            try this.validate{gas: gasLimit}(tokens[i], baseToken, amountToBorrow) returns (TokenFees memory fotResult) {
                fotResults[i] = fotResult;
            } catch (bytes memory reason) {
                bytes4 selector;
                assembly {
                    selector := mload(add(reason, 32))
                }
                
                if (selector == TokenValidator.SameToken.selector) {
                    fotResults[i] = TokenFees({
                        buyFeeBps: 0,
                        sellFeeBps: 0,
                        STF: false,
                        errorCode: ErrorCode.SameToken });
                } else if (selector == TokenValidator.PairLookupFailed.selector) {
                    fotResults[i] = TokenFees({
                        buyFeeBps: 0,
                        sellFeeBps: 0,
                        STF: true,
                        errorCode: ErrorCode.PairLookupFailed 
                    });
                } else if (selector == TokenValidator.PairTransferFailed.selector) {
                    fotResults[i] = TokenFees({
                        buyFeeBps: 0,
                        sellFeeBps: 0,
                        STF: true,
                        errorCode: ErrorCode.PairTransferFailed 
                    });
                } else if (selector == TokenValidator.InsufficientLiquidity.selector) {
                    fotResults[i] = TokenFees({
                        buyFeeBps: 0,
                        sellFeeBps: 0,
                        STF: true,
                        errorCode: ErrorCode.InsufficientLiquidity 
                    });
                } else {
                    fotResults[i] = TokenFees({
                        buyFeeBps: 0,
                        sellFeeBps: 0,
                        STF: true,
                        errorCode: ErrorCode.OutOfGas 
                    });
                }
            }
        }
    }

    function _validate(address token, address baseToken, uint256 amountToBorrow)
        internal
        returns (TokenFees memory result)
    {
        if (token == baseToken) {
            revert SameToken();
        }

        address pairAddress = PancakeLibrary.pairFor(factoryV2, token, baseToken);

        (, bytes memory returnData) =
            address(pairAddress).staticcall(abi.encodeWithSelector(IPancakePair.token0.selector));

        if (returnData.length == 0) {
            revert PairLookupFailed();
        }

        address token0Address = abi.decode(returnData, (address));

        (uint256 amount0Out, uint256 amount1Out) =
            token == token0Address ? (amountToBorrow, uint256(0)) : (uint256(0), amountToBorrow);

        uint256 detectorBalanceBeforeLoan = ERC20(token).balanceOf(address(this));

        IPancakePair pair = IPancakePair(pairAddress);

        try pair.swap(amount0Out, amount1Out, address(this), abi.encode(detectorBalanceBeforeLoan, amountToBorrow)) {}
        catch (bytes memory reason) {
            result = parseRevertReason(reason);
        }
    }

    function parseRevertReason(bytes memory reason) private pure returns (TokenFees memory) {
        if (reason.length != 128) {
            if(isTransferFailed(reason)) {
                revert PairTransferFailed();
            }
            if(isInsufficientLiquidity(reason)) {
                revert InsufficientLiquidity();
            }
            revert OutOfGas();
        } else {
            return abi.decode(reason, (TokenFees));
        }
    }

    function isTransferFailed(bytes memory reason) internal pure returns (bool) {
        string memory stf = STF_REVERT_STRING_SUFFIX;
        assembly {
            reason := add(reason, 0x04)
        }

        string memory reasonStr = abi.decode(reason, (string));

        return keccak256(bytes(reasonStr)) == keccak256(bytes(stf));
    }

    function isInsufficientLiquidity(bytes memory reason) internal pure returns (bool) {
        string memory insufficientLiquidity = INSUFFICIENT_LIQUIDITY_REVERT_STRING_SUFFIX;
        assembly {
            reason := add(reason, 0x04)
        }

        string memory reasonStr = abi.decode(reason, (string));

        return keccak256(bytes(reasonStr)) == keccak256(bytes(insufficientLiquidity));
    }

    function pancakeCall(address, uint256 amount0, uint256, bytes calldata data) external {
        IPancakePair pair = IPancakePair(msg.sender);
        (address token0, address token1) = (pair.token0(), pair.token1());

        ERC20 tokenBorrowed = ERC20(amount0 > 0 ? token0 : token1);

        (uint256 detectorBalanceBeforeLoan, uint256 amountRequestedToBorrow) = abi.decode(data, (uint256, uint256));
        uint256 amountBorrowed = tokenBorrowed.balanceOf(address(this)) - detectorBalanceBeforeLoan;

        uint256 buyFeeBps = _calculateBuyFee(amountRequestedToBorrow, amountBorrowed);

        (bool externalSTF) =
            tryExternalTransferAndRevert(tokenBorrowed, amountBorrowed);

        (uint256 sellFeeBps, bool sellRevertSTF) = _calculateSellFee(pair, tokenBorrowed, amountBorrowed, buyFeeBps);

        bytes memory fees = abi.encode(
            TokenFees({
                buyFeeBps: buyFeeBps,
                sellFeeBps: sellFeeBps,
                STF: externalSTF ? externalSTF : sellRevertSTF,
                errorCode: ErrorCode.NoError
            })
        );

        assembly {
            revert(add(32, fees), mload(fees))
        }
    }

    function _calculateBuyFee(uint256 amountRequestedToBorrow, uint256 amountBorrowed)
        internal
        pure
        returns (uint256 buyFeeBps)
    {
        buyFeeBps = (amountRequestedToBorrow - amountBorrowed).mulDivUp(BPS, amountRequestedToBorrow);
    }

    function _calculateSellFee(IPancakePair pair, ERC20 tokenBorrowed, uint256 amountBorrowed, uint256 buyFeeBps)
        internal
        returns (uint256 sellFeeBps, bool STF)
    {
        uint256 pairBalanceBeforeSell = tokenBorrowed.balanceOf(address(pair));
        try this.callTransfer(tokenBorrowed, address(pair), amountBorrowed) {
            uint256 amountSold = tokenBorrowed.balanceOf(address(pair)) - pairBalanceBeforeSell;
            uint256 sellFee = amountBorrowed - amountSold;
            sellFeeBps = sellFee.mulDivUp(BPS, amountBorrowed);
        } catch (bytes memory) {
            sellFeeBps = buyFeeBps;
            STF = true;
        }
    }

    function tryExternalTransferAndRevert(ERC20 tokenBorrowed, uint256 amountBorrowed)
        internal
        returns (bool STF)
    {
        uint256 balanceBeforeLoan = tokenBorrowed.balanceOf(factoryV2);
        try this.callTransfer(tokenBorrowed, factoryV2, amountBorrowed, balanceBeforeLoan + amountBorrowed) {}
        catch (bytes memory revertData) {
            if (revertData.length > 32) {
                assembly {
                    revertData := add(revertData, 0x04)
                }
                string memory reason = abi.decode(revertData, (string));
                if (keccak256(bytes(reason)) == keccak256(bytes("TRANSFER_FAILED"))) {
                    STF = true;
                } else {
                    revert UnknownExternalTransferFailure(reason);
                }
            } else {
                STF = abi.decode(revertData, (bool));
            }
        }
    }

    function callTransfer(ERC20 token, address to, uint256 amount) external {
        token.safeTransfer(to, amount);
    }

    function callTransfer(ERC20 token, address to, uint256 amount, uint256 expectedBalance) external {
        try this.callTransfer(token, to, amount) {}
        catch (bytes memory revertData) {
            if (revertData.length < 68) revert();
            assembly {
                revertData := add(revertData, 0x04)
            }
            revert(abi.decode(revertData, (string)));
        }
        bytes memory feeTakenOnTransfer = abi.encode(token.balanceOf(to) != expectedBalance);
        assembly {
            revert(add(32, feeTakenOnTransfer), mload(feeTakenOnTransfer))
        }
    }

    function setGasLimit(uint256 _gasLimit) public onlyOwner {
        gasLimit = _gasLimit;
    }

    function setOwner(address _owner) public onlyOwner {
        owner = _owner;
    }
}