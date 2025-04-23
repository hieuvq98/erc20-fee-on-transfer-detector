// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity =0.8.18;

import "solmate/tokens/ERC20.sol";
import "solmate/utils/SafeTransferLib.sol";
import "solmate/utils/FixedPointMathLib.sol";
import "./interfaces/IPool.sol";
import "./interfaces/IFactory.sol";

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

    uint24[] public fees = [100, 500, 2500, 3000, 10000];
    uint256 constant BPS = 10_000;

    address internal constant factoryV2 = 0xcA143Ce32Fe78f1f7019d7d551a6402fC5350c73;
    address internal constant factoryV3 = 0x0BFbCF9fa4f9C56B0F40a671Ad40E0805A091865;

    function batchValidateWithBatchBaseTokens(
        address[] calldata tokens,
        address[] calldata baseTokens,
        uint256 amountToBorrow,
        uint256 gasLimit
    ) public returns (TokenFees[] memory tokenFeesResults) {
        tokenFeesResults = new TokenFees[](tokens.length);
        for (uint256 i = 0; i < tokens.length; i++) {
            TokenFees memory largestFees;
            for (uint256 j = 0; j < baseTokens.length; j++) {
                try this.validate{gas: gasLimit * baseTokens.length}(tokens[i], baseTokens[j], amountToBorrow) returns (
                    TokenFees memory tokenFees
                ) {
                    largestFees.buyFeeBpsForPair = _max(largestFees.buyFeeBpsForPair, tokenFees.buyFeeBpsForPair);
                    largestFees.sellFeeBpsForPair = _max(largestFees.sellFeeBpsForPair, tokenFees.sellFeeBpsForPair);
                    largestFees.sellFeeBpsForFactory =
                        _max(largestFees.sellFeeBpsForFactory, tokenFees.sellFeeBpsForFactory);
                    largestFees.errCode = tokenFees.errCode;
                } catch Error(string memory reason) {
                    tokenFeesResults[i] = _handleStringErrorV2(reason, largestFees, j == baseTokens.length - 1);
                } catch (bytes memory reason) {
                    tokenFeesResults[i] =
                        _handleCustomError(reason, largestFees, j == baseTokens.length - 1, tokenFeesResults[i]);
                }
            }
            if (
                tokenFeesResults[i].errCode.length == 0
                    || (tokenFeesResults[i].errCode.length == 1 && tokenFeesResults[i].errCode[0] == ErrorCode.NoError)
            ) {
                tokenFeesResults[i] = largestFees;
            }
        }
    }

    function batchValidateWithBatchBaseTokensV3(
        address[] calldata tokens,
        address[] calldata baseTokens,
        uint256 amountToBorrow,
        uint256 gasLimit
    ) public returns (TokenFees[] memory tokenFeesResults) {
        tokenFeesResults = new TokenFees[](tokens.length);
        for (uint256 i = 0; i < tokens.length; i++) {
            TokenFees memory largestFees;
            for (uint256 j = 0; j < baseTokens.length; j++) {
                try this.validateV3{gas: gasLimit * baseTokens.length}(tokens[i], baseTokens[j], amountToBorrow)
                returns (TokenFees memory tokenFees) {
                    largestFees.buyFeeBpsForPair = _max(largestFees.buyFeeBpsForPair, tokenFees.buyFeeBpsForPair);
                    largestFees.sellFeeBpsForPair = _max(largestFees.sellFeeBpsForPair, tokenFees.sellFeeBpsForPair);
                    largestFees.sellFeeBpsForFactory =
                        _max(largestFees.sellFeeBpsForFactory, tokenFees.sellFeeBpsForFactory);
                    largestFees.errCode = tokenFees.errCode;
                } catch Error(string memory reason) {
                    tokenFeesResults[i] = _handleStringErrorV3(reason, largestFees, j == baseTokens.length - 1);
                } catch (bytes memory reason) {
                    tokenFeesResults[i] =
                        _handleCustomError(reason, largestFees, j == baseTokens.length - 1, tokenFeesResults[i]);
                }
            }
            if (
                tokenFeesResults[i].errCode.length == 0
                    || (tokenFeesResults[i].errCode.length == 1 && tokenFeesResults[i].errCode[0] == ErrorCode.NoError)
            ) {
                tokenFeesResults[i] = largestFees;
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
                tokenFeesResults[i] = _handleStringErrorV2(reason, tokenFeesResults[i], true);
            } catch (bytes memory reason) {
                tokenFeesResults[i] = _handleCustomError(reason, tokenFeesResults[i], true, tokenFeesResults[i]);
            }
        }
    }

    function batchValidateV3(address[] calldata tokens, address baseToken, uint256 amountToBorrow, uint256 gasLimit)
        public
        returns (TokenFees[] memory tokenFeesResults)
    {
        tokenFeesResults = new TokenFees[](tokens.length);

        for (uint256 i = 0; i < tokens.length; i++) {
            try this.validateV3{gas: gasLimit}(tokens[i], baseToken, amountToBorrow) returns (
                TokenFees memory tokenFees
            ) {
                tokenFeesResults[i] = tokenFees;
            } catch Error(string memory reason) {
                tokenFeesResults[i] = _handleStringErrorV3(reason, tokenFeesResults[i], true);
            } catch (bytes memory reason) {
                tokenFeesResults[i] = _handleCustomError(reason, tokenFeesResults[i], true, tokenFeesResults[i]);
            }
        }
    }

    function validate(address token, address baseToken, uint256 amountToBorrow) public returns (TokenFees memory) {
        return _validate(token, baseToken, amountToBorrow);
    }

    function validateV3(address token, address baseToken, uint256 amountToBorrow)
        public
        returns (TokenFees memory tokenFeesResult)
    {
        uint24[] memory _fees = fees;
        bool[4] memory errors; // [pairLookFailed, L, OutOfGas, TransferFailed]

        for (uint256 i; i < _fees.length; i++) {
            try this._validateV3(token, baseToken, amountToBorrow, _fees[i]) returns (TokenFees memory tokenFees) {
                tokenFeesResult.buyFeeBpsForPair = _max(tokenFeesResult.buyFeeBpsForPair, tokenFees.buyFeeBpsForPair);
                tokenFeesResult.sellFeeBpsForPair = _max(tokenFeesResult.sellFeeBpsForPair, tokenFees.sellFeeBpsForPair);
                tokenFeesResult.sellFeeBpsForFactory =
                    _max(tokenFeesResult.sellFeeBpsForFactory, tokenFees.sellFeeBpsForFactory);
                tokenFeesResult.errCode = tokenFees.errCode;
            } catch Error(string memory reason) {
                if (keccak256(bytes(reason)) == keccak256("L")) errors[1] = true;
                else if (keccak256(bytes(reason)) == keccak256("TF")) errors[3] = true;
            } catch (bytes memory reason) {
                if (reason.length == 0) {
                    errors[2] = true;
                } else if (
                    bytes4(reason) == TokenValidator.PairLookupFailed.selector && i == fees.length - 1
                        && tokenFeesResult.errCode.length == 0
                ) {
                    errors[0] = true;
                }
            }
        }

        if (
            tokenFeesResult.errCode.length == 0
                || (tokenFeesResult.errCode.length == 1 && tokenFeesResult.errCode[0] != ErrorCode.NoError)
        ) {
            if (errors[2]) revert(); // empty revert
            if (errors[1]) revert("L"); // liquidity
            if (errors[3]) revert("TF"); // transfer failed
            if (errors[0]) revert PairLookupFailed(); // no pool
        }
    }

    function _validate(address token, address baseToken, uint256 amountToBorrow) internal returns (TokenFees memory) {
        if (token == baseToken) {
            revert SameToken();
        }

        address pairAddress = IFactory(factoryV2).getPair(token, baseToken);

        (, bytes memory returnData) = address(pairAddress).staticcall(abi.encodeWithSelector(IPool.token0.selector));

        if (returnData.length == 0) {
            revert PairLookupFailed();
        }

        address token0Address = abi.decode(returnData, (address));
        (uint256 amount0Out, uint256 amount1Out) =
            token == token0Address ? (amountToBorrow, uint256(0)) : (uint256(0), amountToBorrow);

        uint256 detectorBalanceBeforeLoan = ERC20(token).balanceOf(address(this));

        IPool pair = IPool(pairAddress);
        try pair.swap(amount0Out, amount1Out, address(this), abi.encode(detectorBalanceBeforeLoan, amountToBorrow)) {}
        catch (bytes memory reason) {
            return parseRevertReason(reason);
        }
    }

    function _validateV3(address token, address baseToken, uint256 amountToBorrow, uint24 fee)
        external
        returns (TokenFees memory)
    {
        if (token == baseToken) {
            revert SameToken();
        }

        address poolAddress = IFactory(factoryV3).getPool(token, baseToken, fee);

        (, bytes memory returnData) = address(poolAddress).staticcall(abi.encodeWithSelector(IPool.token0.selector));

        if (returnData.length == 0) {
            revert PairLookupFailed();
        }

        address token0Address = abi.decode(returnData, (address));
        (uint256 amount0, uint256 amount1) =
            token == token0Address ? (amountToBorrow, uint256(0)) : (uint256(0), amountToBorrow);

        uint256 detectorBalanceBeforeLoan = ERC20(token).balanceOf(address(this));

        try IPool(poolAddress).flash(
            address(this), amount0, amount1, abi.encode(detectorBalanceBeforeLoan, amountToBorrow)
        ) {} catch (bytes memory reason) {
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
        IPool pair = IPool(msg.sender);
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

    function pancakeV3FlashCallback(uint256 fee0, uint256, bytes calldata data) external {
        IPool pair = IPool(msg.sender);
        (address token0, address token1) = (pair.token0(), pair.token1());

        ERC20 tokenBorrowed = ERC20(fee0 > 0 ? token0 : token1);

        (uint256 detectorBalanceBeforeLoan, uint256 amountRequestedToBorrow) = abi.decode(data, (uint256, uint256));
        uint256 amountBorrowed = tokenBorrowed.balanceOf(address(this)) - detectorBalanceBeforeLoan;

        uint256 buyFeeBpsForPair = _calculateBuyFee(amountRequestedToBorrow, amountBorrowed);

        (uint256 sellFeeBpsForFactory, bool transferFailedForFactory) =
            _calculateSellFee(tokenBorrowed, factoryV2, amountBorrowed, true);

        (uint256 sellFeeBpsForPair, bool transferFailedForPair) =
            _calculateSellFee(tokenBorrowed, address(pair), amountBorrowed, false);

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

    function _max(uint256 a, uint256 b) private pure returns (uint256) {
        return a > b ? a : b;
    }

    function _handleStringErrorV2(string memory reason, TokenFees memory current, bool isLast)
        private
        pure
        returns (TokenFees memory)
    {
        ErrorCode[] memory err;
        err = new ErrorCode[](1);

        if (keccak256(bytes(reason)) == keccak256("Pancake: INSUFFICIENT_OUTPUT_AMOUNT")) {
            err[0] = ErrorCode.InsufficientOutputAmount;
        } else if (keccak256(bytes(reason)) == keccak256("Pancake: INSUFFICIENT_LIQUIDITY")) {
            if (isLast && current.errCode.length == 0) {
                err[0] = ErrorCode.InsufficientLiquidity;
            } else {
                return current;
            }
        } else if (keccak256(bytes(reason)) == keccak256("Pancake: TRANSFER_FAILED")) {
            err[0] = ErrorCode.TransferFailed1;
        }

        return TokenFees(0, 0, 0, err);
    }

    function _handleStringErrorV3(string memory reason, TokenFees memory current, bool isLast)
        private
        pure
        returns (TokenFees memory)
    {
        ErrorCode[] memory err;
        err = new ErrorCode[](1);

        if (keccak256(bytes(reason)) == keccak256("L")) {
            if (isLast && current.errCode.length == 0) {
                err[0] = ErrorCode.InsufficientLiquidity;
            } else {
                return current;
            }
        } else if (keccak256(bytes(reason)) == keccak256("TF")) {
            err[0] = ErrorCode.TransferFailed1;
        }

        return TokenFees(0, 0, 0, err);
    }

    function _handleCustomError(bytes memory reason, TokenFees memory current, bool isLast, TokenFees memory previous)
        private
        pure
        returns (TokenFees memory)
    {
        ErrorCode[] memory err;
        err = new ErrorCode[](1);

        if (reason.length == 0) {
            err[0] = ErrorCode.Others;
        } else {
            bytes4 selector = bytes4(reason);
            if (selector == TokenValidator.SameToken.selector) {
                err[0] = ErrorCode.SameToken;
            } else if (selector == TokenValidator.PairLookupFailed.selector) {
                if (isLast && current.errCode.length == 0) {
                    err[0] = ErrorCode.PairLookupFailed;
                } else {
                    return current;
                }
            }
        }

        if (previous.errCode.length == 0 || (previous.errCode.length == 1 && previous.errCode[0] == ErrorCode.NoError))
        {
            return TokenFees(0, 0, 0, err);
        }

        return previous;
    }
}
