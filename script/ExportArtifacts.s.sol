// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.18;

import {Script} from "forge-std/Script.sol";
import {TokenValidator, ValidatorConfig} from "../src/TokenValidator.sol";
import {ChainConfigs} from "../src/config/ChainConfigs.sol";

/// @notice Emits the runtime bytecode of a `TokenValidator` configured for each chain.
/// @dev    The crawler does not deploy this contract: it injects the runtime bytecode into
///         an `eth_call` state override. Because the chain configuration lives in
///         immutables, that bytecode differs per chain, so one file is written per preset.
///         `script/export-artifacts.sh` pairs each with the ABI.
contract ExportArtifactsScript is Script {
    function run() public {
        _export("Bnb", ChainConfigs.bsc());
        _export("Eth", ChainConfigs.ethereum());
        _export("Base", ChainConfigs.base());
        _export("Viction", ChainConfigs.viction());
    }

    function _export(string memory name, ValidatorConfig memory config) internal {
        TokenValidator validator = new TokenValidator(config);

        vm.writeFile(
            string.concat("artifacts/tokenFeeValidator", name, ".runtime.hex"), vm.toString(address(validator).code)
        );
    }
}
