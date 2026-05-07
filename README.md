# cryptography-specs

Specifications for cryptography in Ethereum, written in Lean.

## Specs

- `EthCryptographySpecs/Bls/`, BLS12-381 curve arithmetic, hash-to-curve, and signatures.
- `EthCryptographySpecs/Kzg/`, KZG polynomial commitments.

## Prerequisites

- [`elan`](https://github.com/leanprover/elan), for `lean` and `lake`.

## Building

```bash
lake build
```

## Tests

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -e '.[test]'
pytest
```

*Note*: Pre-generated reference tests are written to `tests/` at the project
root. These tests are intended for use across implementations and may be pinned
by downstream consumers.
