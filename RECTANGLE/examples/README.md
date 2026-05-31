# RECTANGLE Examples

This directory contains example scripts demonstrating the use of the RECTANGLE key differential cryptanalysis framework.

## Running Examples

All examples can be run from the project root:

```bash
cd RECTANGLE
python examples/example_1_basic_differential.py
```

Or use the main entry point:

```bash
python main.py --rounds 6
```

## Available Examples

| File | Description |
|------|-------------|
| `example_1_basic_differential.py` | Basic differential trail search on 4-round RECTANGLE |
| `example_2_related_key.py` | Related-key differential analysis with KEY_NOT_ZERO constraint |
| `example_3_active_sbox.py` | Count minimum active S-boxes for rounds 1-6 |
| `example_4_multi_round.py` | Progressive multi-round analysis from 1 to 6 rounds |
| `example_5_64_128_version.py` | Compare 64/80 and 64/128 key versions |

## Command Line Interface

The `main.py` entry point supports various options:

```bash
# Basic analysis (6 rounds, 64/80)
python main.py

# 10-round analysis with related-key constraint
python main.py --rounds 10 --key-diff

# Multi-round search
python main.py --multi-round 1 10

# Active S-box counting
python main.py --sbox-count --rounds 8

# 64/128 key version
python main.py --version 64_128 --rounds 6

# Different SAT solver
python main.py --solver Lingeling --rounds 4
```
