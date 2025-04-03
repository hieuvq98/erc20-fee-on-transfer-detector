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

    function testValidateToken() public {
        address token = 0x3ADE350e05F631f946B6d2B1a2deAAF95DCB243a;

        address[] memory tokens = new address[](1);
        tokens[0] = token;
        address baseToken = 0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c;

        address[] memory baseTokens = new address[](2);
        baseTokens[0] = baseToken;
        baseTokens[1] = 0x55d398326f99059fF775485246999027B3197955;
        uint256 amountToBorrow = 10000;
        TokenFees[] memory fees = validator.batchValidateWithBatchBaseTokensV3(tokens, baseTokens, amountToBorrow, 1000000);
        // assertTrue(result, "Token validation failed");
    }
}