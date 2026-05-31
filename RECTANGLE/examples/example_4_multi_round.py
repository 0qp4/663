"""
Example 4: Multi-Round Progressive Analysis
Search for optimal differential trails from 1 to 6 rounds.
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from primitives.rectangle import RECTANGLE_BLOCKCIPHER
from attacks.attacks import diff_attacks

print("Multi-Round Differential Analysis for RECTANGLE-64/80")
print("=" * 50)

results = []
for rounds in range(1, 7):
    cipher = RECTANGLE_BLOCKCIPHER(r=rounds, version=[64, 80])
    trails = diff_attacks(
        cipher,
        goal='DIFFERENTIALPATH_PROB',
        constraints=['INPUT_NOT_ZERO'],
        objective_target='OPTIMAL',
        config_model={'model_type': 'sat'},
        config_solver={'solver': 'Cadical195'},
    )
    if trails:
        weight = trails[0].data['diff_weight']
        prob = 2 ** (-weight) if weight else 1.0
        results.append((rounds, weight, prob))
        print(f"  Rounds {rounds:2d}: weight={weight:3d}, prob={prob:.4e}")
    else:
        results.append((rounds, None, None))
        print(f"  Rounds {rounds:2d}: UNSAT")

print("\nSummary:")
print(f"  {'Rounds':>6} | {'Weight':>6} | {'Probability':>12} | {'2^r Weight':>10}")
print(f"  {'-'*6}-+-{'-'*6}-+-{'-'*12}-+-{'-'*10}")
for rounds, weight, prob in results:
    if weight is not None:
        print(f"  {rounds:>6} | {weight:>6} | {prob:>12.4e} | {2**weight:>10.1f}")
    else:
        print(f"  {rounds:>6} |    UNSAT")
