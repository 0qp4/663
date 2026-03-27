# RECTANGLE Related-Key Differential Analysis

## Overview

This project implements a SAT-based related-key differential analysis for the RECTANGLE lightweight block cipher.

## Files

- `RECTANGLE_RelatedKey.py` - Main script for related-key differential analysis
- `RECTANGLE_M_sim.py` - Original single-key differential analysis (with Matsui constraint)
- `RECTANGLE_M_sun.py` - Original single-key differential analysis (simplified version)
- `Rectangle-lightweight-block-cipher-main/rectangle.js` - RECTANGLE cipher reference implementation

## RECTANGLE Cipher Specification

- **Block Size**: 64 bits
- **Key Size**: 80 bits (or 128 bits)
- **Rounds**: 25
- **Structure**: SP-network (Substitution-Permutation Network)

### S-box (4-bit)
```
[6, 5, 12, 10, 1, 14, 7, 9, 11, 0, 3, 13, 8, 15, 4, 2]
```

### ShiftRow
- Row 0: No shift
- Row 1: Left shift by 1
- Row 2: Left shift by 12
- Row 3: Left shift by 13

## Related-Key Differential Analysis

### Key Schedule Differential Propagation

The related-key analysis models the differential propagation through both the cipher and the key schedule:

1. **Key State Variables**
   - `key_in[r]`: 80-bit key difference input at round r
   - `key_out[r]`: 64-bit round key difference at round r

2. **Key Schedule Constraints**
   - S-box differential propagation in key schedule
   - Key state transitions (shifts and XORs)
   - Round key extraction

3. **AddRoundKey Constraint**
   - XOR between plaintext difference and round key difference

### SAT Model Structure

```
Variables:
- xin[r]: 64-bit plaintext difference at round r
- xout[r]: 64-bit ciphertext difference at round r
- p, q, m: Probability variables for S-box differentials
- key_in[r]: 80-bit key difference at round r
- key_out[r]: 64-bit round key difference at round r
- key_p, key_q, key_m: Probability variables for key schedule S-box

Clauses:
- Round function S-box constraints
- ShiftRow constraints
- Key schedule S-box constraints
- Key state transition constraints
- AddRoundKey constraints
- Sequential encoding for probability bounds
```

## Requirements

- Python 3.x
- Gurobi Optimizer (for bound computation)
- CaDiCaL SAT solver (or compatible)

## Usage

```bash
python RECTANGLE_RelatedKey.py
```

## Output Files

- `Problem-Round{n}-Probability{p}-RelatedKey.cnf` - SAT problem in CNF format
- `Round{n}-Probability{p}-RelatedKey-solution.txt` - SAT solver output
- `ProcessResult_RelatedKey.txt` - Detailed results for each round
- `RunTimeSummarise_RelatedKey.out` - Summary of runtime and statistics

## Configuration

Modify these parameters in the script:

```python
FullRound = 25              # Total number of rounds
SearchRoundStart = 1        # Start round for search
SearchRoundEnd = FullRound  # End round for search
```

## SAT Solver Path

Update the solver path in the `Decision` function:

```python
order = "d:/solver/cadical-master/build/cadical " + ...
```

## Results Format

```
Round: n; Probability: p; Sat/Unsat; TotalCost: time; p: var_count; cnf: clause_count
```

## Reference

Zhang, W., Bao, Z., Lin, D., Rijmen, V., Yang, B., & Verbauwhede, I. (2015). RECTANGLE: a bit-slice lightweight block cipher suitable for multiple platforms. Science China Information Sciences, 58(12), 1-15.
