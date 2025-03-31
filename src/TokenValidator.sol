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
    InsufficientOutputAmount,
    InsufficientLiquidity,
    TransferFailed1, // from Pair
    TransferFailed2, // to Pair
    TransferFailed3, // to Factory
    Others
}

struct TokenFees {
    uint256 buyFeeBpsForPair;
    uint256 sellFeeBpsForPair;
    uint256 sellFeeBpsForFactory;
    ErrorCode[] errCode;
}

contract TokenValidator {
    using SafeTransferLib for ERC20;
    using FixedPointMathLib for uint256;

    error SameToken();
    error PairLookupFailed();

    uint256 constant BPS = 10_000;
    address internal immutable factoryV2;

    constructor(address _factoryV2) {
        factoryV2 = _factoryV2;
    }

    function batchValidateWithBatchBaseTokens(
        address[] calldata tokens,
        address[] calldata baseTokens,
        uint256 amountToBorrow,
        uint256 gasLimit
    ) public returns (TokenFees[] memory tokenFeesResults) {
        tokenFeesResults = new TokenFees[](tokens.length);
        for (uint256 i = 0; i < tokens.length; i++) {
            bool breakFlag = false;
            TokenFees memory largestTokenFees;
            for (uint256 j = 0; j < baseTokens.length; j++) {
                try this.validate{gas: gasLimit * baseTokens.length}(tokens[i], baseTokens[j], amountToBorrow) returns (
                    TokenFees memory tokenFees
                ) {
                    if (tokenFees.buyFeeBpsForPair > largestTokenFees.buyFeeBpsForPair) {
                        largestTokenFees.buyFeeBpsForPair = tokenFees.buyFeeBpsForPair;
                    }
                    if (tokenFees.sellFeeBpsForPair > largestTokenFees.sellFeeBpsForPair) {
                        largestTokenFees.sellFeeBpsForPair = tokenFees.sellFeeBpsForPair;
                    }
                    if (tokenFees.sellFeeBpsForFactory > largestTokenFees.sellFeeBpsForFactory) {
                        largestTokenFees.sellFeeBpsForFactory = tokenFees.sellFeeBpsForFactory;
                    }
                    largestTokenFees.errCode = tokenFees.errCode;
                } catch Error(string memory reason) {
                    // revert("reason") | require("reason")
                    ErrorCode[] memory errCode;
                    errCode = new ErrorCode[](1);

                    if (keccak256(bytes(reason)) == keccak256(bytes("Pancake: INSUFFICIENT_OUTPUT_AMOUNT"))) {
                        errCode[0] = ErrorCode.InsufficientOutputAmount;
                    } else if (keccak256(bytes(reason)) == keccak256(bytes("Pancake: INSUFFICIENT_LIQUIDITY"))) {
                        errCode[0] = ErrorCode.InsufficientLiquidity;
                    } else if (keccak256(bytes(reason)) == keccak256(bytes("Pancake: TRANSFER_FAILED"))) {
                        errCode[0] = ErrorCode.TransferFailed1;
                    }

                    tokenFeesResults[i] = TokenFees({
                        buyFeeBpsForPair: 0,
                        sellFeeBpsForPair: 0,
                        sellFeeBpsForFactory: 0,
                        errCode: errCode
                    });
                    breakFlag = true;
                    break;
                } catch (bytes memory reason) {
                    ErrorCode[] memory errCode;
                    errCode = new ErrorCode[](1);

                    if (reason.length == 0) {
                        // revert() | Out_of_Gas
                        errCode[0] = ErrorCode.Others;
                    } else {
                        // Custom Error
                        if (bytes4(reason) == TokenValidator.SameToken.selector) {
                            errCode[0] = ErrorCode.SameToken;
                        } else if (bytes4(reason) == TokenValidator.PairLookupFailed.selector) {
                            errCode[0] = ErrorCode.PairLookupFailed;
                            continue;
                        }
                    }

                    tokenFeesResults[i] = TokenFees({
                        buyFeeBpsForPair: 0,
                        sellFeeBpsForPair: 0,
                        sellFeeBpsForFactory: 0,
                        errCode: errCode
                    });
                    breakFlag = true;
                    break;
                }
            }
            if (!breakFlag) {
                tokenFeesResults[i] = largestTokenFees;
            }
        }
    }

    function batchValidate(address[] calldata tokens, address baseToken, uint256 amountToBorrow, uint256 gasLimit)
        public
        returns (TokenFees[] memory tokenFeesResults)
    {
        tokenFeesResults = new TokenFees[](tokens.length);

        for (uint256 i = 0; i < tokens.length; i++) {
            try this.validate{gas: gasLimit}(tokens[i], baseToken, amountToBorrow) returns (TokenFees memory tokenFees)
            {
                tokenFeesResults[i] = tokenFees;
            } catch Error(string memory reason) {
                // revert("reason") | require("reason")
                ErrorCode[] memory errCode;
                errCode = new ErrorCode[](1);

                if (keccak256(bytes(reason)) == keccak256(bytes("Pancake: INSUFFICIENT_OUTPUT_AMOUNT"))) {
                    errCode[0] = ErrorCode.InsufficientOutputAmount;
                } else if (keccak256(bytes(reason)) == keccak256(bytes("Pancake: INSUFFICIENT_LIQUIDITY"))) {
                    errCode[0] = ErrorCode.InsufficientLiquidity;
                } else if (keccak256(bytes(reason)) == keccak256(bytes("Pancake: TRANSFER_FAILED"))) {
                    errCode[0] = ErrorCode.TransferFailed1;
                }

                tokenFeesResults[i] =
                    TokenFees({buyFeeBpsForPair: 0, sellFeeBpsForPair: 0, sellFeeBpsForFactory: 0, errCode: errCode});
            } catch (bytes memory reason) {
                ErrorCode[] memory errCode;
                errCode = new ErrorCode[](1);

                if (reason.length == 0) {
                    // revert() | Out_of_Gas
                    errCode[0] = ErrorCode.Others;
                } else {
                    // Custom Error
                    if (bytes4(reason) == TokenValidator.SameToken.selector) {
                        errCode[0] = ErrorCode.SameToken;
                    } else if (bytes4(reason) == TokenValidator.PairLookupFailed.selector) {
                        errCode[0] = ErrorCode.PairLookupFailed;
                    }
                }

                tokenFeesResults[i] =
                    TokenFees({buyFeeBpsForPair: 0, sellFeeBpsForPair: 0, sellFeeBpsForFactory: 0, errCode: errCode});
            }
        }
    }

    function validate(address token, address baseToken, uint256 amountToBorrow) public returns (TokenFees memory) {
        return _validate(token, baseToken, amountToBorrow);
    }

    function _validate(address token, address baseToken, uint256 amountToBorrow) internal returns (TokenFees memory) {
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
            return parseRevertReason(reason);
        }
    }

    function parseRevertReason(bytes memory reason) private pure returns (TokenFees memory) {
        if (reason.length == 224 || reason.length == 256) {
            return abi.decode(reason, (TokenFees));
        } else {
            assembly {
                revert(add(reason, 0x20), mload(reason))
            }
        }
    }

    function pancakeCall(address, uint256 amount0, uint256, bytes calldata data) external {
        IPancakePair pair = IPancakePair(msg.sender);
        (address token0, address token1) = (pair.token0(), pair.token1());

        ERC20 tokenBorrowed = ERC20(amount0 > 0 ? token0 : token1);

        (uint256 detectorBalanceBeforeLoan, uint256 amountRequestedToBorrow) = abi.decode(data, (uint256, uint256));
        uint256 amountBorrowed = tokenBorrowed.balanceOf(address(this)) - detectorBalanceBeforeLoan;

        //
        uint256 buyFeeBpsForPair = _calculateBuyFee(amountRequestedToBorrow, amountBorrowed);

        //
        (uint256 sellFeeBpsForFactory, bool transferFailedForFactory) =
            _calculateSellFee(tokenBorrowed, factoryV2, amountBorrowed, true);

        //
        (uint256 sellFeeBpsForPair, bool transferFailedForPair) =
            _calculateSellFee(tokenBorrowed, address(pair), amountBorrowed, false);

        //
        ErrorCode[] memory errCode;
        if (transferFailedForFactory == true && transferFailedForPair == true) {
            errCode = new ErrorCode[](2);
            errCode[0] = ErrorCode.TransferFailed2;
            errCode[1] = ErrorCode.TransferFailed3;
        } else if (transferFailedForFactory == true) {
            errCode = new ErrorCode[](1);
            errCode[0] = ErrorCode.TransferFailed3;
        } else if (transferFailedForPair == true) {
            errCode = new ErrorCode[](1);
            errCode[0] = ErrorCode.TransferFailed2;
        } else {
            errCode = new ErrorCode[](1);
            errCode[0] = ErrorCode.NoError;
        }

        bytes memory tokenFees = abi.encode(
            TokenFees({
                buyFeeBpsForPair: buyFeeBpsForPair,
                sellFeeBpsForPair: sellFeeBpsForPair,
                sellFeeBpsForFactory: sellFeeBpsForFactory,
                errCode: errCode
            })
        );

        //
        assembly {
            revert(add(tokenFees, 0x20), mload(tokenFees))
        }
    }

    function _calculateBuyFee(uint256 amountRequestedToBorrow, uint256 amountBorrowed)
        internal
        pure
        returns (uint256 buyFeeBps)
    {
        buyFeeBps = (amountRequestedToBorrow - amountBorrowed).mulDivUp(BPS, amountRequestedToBorrow);
    }

    function _calculateSellFee(ERC20 tokenBorrowed, address to, uint256 amountBorrowed, bool isRevert)
        internal
        returns (uint256 sellFeeBps, bool transferFailed)
    {
        try this.callTransfer(tokenBorrowed, to, amountBorrowed, isRevert) returns (
            uint256 _sellFeeBps, bool _transferFailed
        ) {
            (sellFeeBps, transferFailed) = (_sellFeeBps, _transferFailed);
        } catch (bytes memory revertData) {
            (sellFeeBps, transferFailed) = abi.decode(revertData, (uint256, bool));
        }
    }

    function callTransfer(ERC20 tokenBorrowed, address to, uint256 amountBorrowed, bool isRevert)
        external
        returns (uint256 sellFeeBps, bool transferFailed)
    {
        uint256 toBalanceBeforeSell = tokenBorrowed.balanceOf(to);

        try this.callTransfer(tokenBorrowed, to, amountBorrowed) {
            uint256 amountSold = tokenBorrowed.balanceOf(to) - toBalanceBeforeSell;
            sellFeeBps = (amountBorrowed - amountSold).mulDivUp(BPS, amountBorrowed);
        } catch {
            // TRANSFER_FAILED
            transferFailed = true;
        }

        if (isRevert) {
            bytes memory result = abi.encode(sellFeeBps, transferFailed);
            assembly {
                revert(add(result, 0x20), mload(result))
            }
        }
    }

    function callTransfer(ERC20 token, address to, uint256 amount) external {
        token.safeTransfer(to, amount);
    }
}
