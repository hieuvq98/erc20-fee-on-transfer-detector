#!/usr/bin/env bash
# Emits { abi, bytecode } per chain, in the shape the pool crawler expects at
# src/jsons/tokenFeeValidator<Chain>.abi.json. `bytecode` is the RUNTIME bytecode with that
# chain's immutables baked in, because the crawler injects it via an eth_call state override
# rather than deploying.
set -euo pipefail
cd "$(dirname "$0")/.."

mkdir -p artifacts
forge build >/dev/null
forge script script/ExportArtifacts.s.sol:ExportArtifactsScript >/dev/null
forge inspect TokenValidator abi --json > artifacts/abi.json

for chain in Bnb Eth Base Viction; do
  python3 - "$chain" <<'PY'
import json, sys
chain = sys.argv[1]
abi = json.load(open('artifacts/abi.json'))
code = open(f'artifacts/tokenFeeValidator{chain}.runtime.hex').read().strip()
path = f'artifacts/tokenFeeValidator{chain}.abi.json'
json.dump({'abi': abi, 'bytecode': code}, open(path, 'w'), indent=2)
print(f'{path}  runtime={len(code)} chars')
PY
  rm -f "artifacts/tokenFeeValidator${chain}.runtime.hex"
done
rm -f artifacts/abi.json
