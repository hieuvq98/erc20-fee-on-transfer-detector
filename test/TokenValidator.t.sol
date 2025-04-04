// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "../src/TokenValidator.sol";

contract TokenValidatorTest is Test {
    TokenValidator private validator;

    function setUp() public {
        vm.selectFork(vm.createFork("https://bsc.blockrazor.xyz"));
        validator = new TokenValidator();
    }

    function testValidateTokenHasFeeOnTransfer_V2() public {
        address token = 0x3CB20d96E866D128BC469a6e66505d46D7F9BaBa;
        address[] memory tokens = new address[](1);
        tokens[0] = token;

        address[] memory baseTokens = new address[](2);
        baseTokens[0] = 0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c; // wbnb
        baseTokens[1] = 0x55d398326f99059fF775485246999027B3197955; // usdt

        uint256 amountToBorrow = 10000;
        TokenFees[] memory fees =
            validator.batchValidateWithBatchBaseTokens(tokens, baseTokens, amountToBorrow, 1000000);

        assertEq(fees[0].buyFeeBpsForPair, 200, "Buy fee for pair should be 200");
        assertEq(fees[0].sellFeeBpsForPair, 200, "Sell fee for pair should be 200");
        assertEq(fees[0].sellFeeBpsForFactory, 0, "Sell fee for factory should be 0");
        assertEq(uint256(fees[0].errCode[0]), uint256(ErrorCode.NoError), "Error code should be NoError");
    }

    function testValidateTokenNoPairFound_V2() public {
        address token = 0x1c3995a53087BF8fC7458E56868Ca87CbCB57D07;
        address[] memory tokens = new address[](1);
        tokens[0] = token;

        address[] memory baseTokens = new address[](2);
        baseTokens[0] = 0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c; // wbnb
        baseTokens[1] = 0x55d398326f99059fF775485246999027B3197955; // usdt

        uint256 amountToBorrow = 10000;
        TokenFees[] memory fees =
            validator.batchValidateWithBatchBaseTokens(tokens, baseTokens, amountToBorrow, 1000000);

        assertEq(fees[0].buyFeeBpsForPair, 0, "Buy fee for pair should be 0");
        assertEq(fees[0].sellFeeBpsForPair, 0, "Sell fee for pair should be 0");
        assertEq(fees[0].sellFeeBpsForFactory, 0, "Sell fee for factory should be 0");
        assertEq(
            uint256(fees[0].errCode[0]), uint256(ErrorCode.PairLookupFailed), "Error code should be PairLookupFailed"
        );
    }

    function testValidateTokenHasFeeOnTransfer_V3() public {
        address token = 0x3ADE350e05F631f946B6d2B1a2deAAF95DCB243a;
        address[] memory tokens = new address[](1);
        tokens[0] = token;

        address[] memory baseTokens = new address[](2);
        baseTokens[0] = 0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c; // wbnb
        baseTokens[1] = 0x55d398326f99059fF775485246999027B3197955; // usdt

        uint256 amountToBorrow = 10000;
        TokenFees[] memory fees =
            validator.batchValidateWithBatchBaseTokensV3(tokens, baseTokens, amountToBorrow, 1000000);

        assertEq(fees[0].buyFeeBpsForPair, 100, "Buy fee for pair should be 100");
        assertEq(fees[0].sellFeeBpsForPair, 100, "Sell fee for pair should be 100");
        assertEq(fees[0].sellFeeBpsForFactory, 100, "Sell fee for factory should be 100");
        assertEq(uint256(fees[0].errCode[0]), uint256(ErrorCode.NoError), "Error code should be NoError");
    }

    function testValidateTokenNoPoolFound_V3() public {
        address token = 0x1c3995a53087BF8fC7458E56868Ca87CbCB57D07;
        address[] memory tokens = new address[](1);
        tokens[0] = token;

        address[] memory baseTokens = new address[](2);
        baseTokens[0] = 0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c; // wbnb
        baseTokens[1] = 0x55d398326f99059fF775485246999027B3197955; // usdt

        uint256 amountToBorrow = 10000;
        TokenFees[] memory fees =
            validator.batchValidateWithBatchBaseTokensV3(tokens, baseTokens, amountToBorrow, 1000000);

        assertEq(fees[0].buyFeeBpsForPair, 0, "Buy fee for pair should be 0");
        assertEq(fees[0].sellFeeBpsForPair, 0, "Sell fee for pair should be 0");
        assertEq(fees[0].sellFeeBpsForFactory, 0, "Sell fee for factory should be 0");
        assertEq(
            uint256(fees[0].errCode[0]), uint256(ErrorCode.PairLookupFailed), "Error code should be PairLookupFailed"
        );
    }
}
