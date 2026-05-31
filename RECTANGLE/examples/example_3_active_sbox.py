"""
Example 3: Minimum Active S-box Count
Count the minimum number of active S-boxes over multiple rounds.
This metric is important for measuring resistance to differential attacks.
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from primitives.rectangle import RECTANGLE_BLOCKCIPHER
from attacks.attacks import diff_attacks

print("Minimum Active S-box Analysis for RECTANGLE-64/80")
print("=" * 50)

for rounds in range(1, 7):
    cipher = RECTANGLE_BLOCKCIPHER(r=rounds, version=[64, 80])
    trails = diff_attacks(
        cipher,
        goal='DIFFERENTIAL_SBOXCOUNT',
        constraints=['INPUT_NOT_ZERO'],
        objective_target='OPTIMAL',
        config_model={'model_type': 'sat'},
        config_solver={'solver': 'Cadical195'},
    )
    if trails:
        weight = trails[0].data['diff_weight']
        print(f"  Rounds {rounds:2d}: {int(weight):3d} active S-boxes")
    else:
        print(f"  Rounds {rounds:2d}: UNSAT")
