"""
Example 5: RECTANGLE-64/128 Version Analysis
Search for differential trails on the 64/128-bit key version.
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from primitives.rectangle import RECTANGLE_BLOCKCIPHER
from attacks.attacks import diff_attacks

for version_name, version in [("64/80", [64, 80]), ("64/128", [64, 128])]:
    print(f"\n{'=' * 50}")
    print(f"RECTANGLE-{version_name} Differential Analysis")
    print(f"{'=' * 50}")

    for rounds in [2, 4, 6]:
        cipher = RECTANGLE_BLOCKCIPHER(r=rounds, version=version)
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
            print(f"  {rounds}-round: weight={weight}")
        else:
            print(f"  {rounds}-round: UNSAT")
