"""
Example 1: Basic Differential Trail Search
Search for optimal differential trail on 4-round RECTANGLE-64/80.
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from primitives.rectangle import RECTANGLE_BLOCKCIPHER
from attacks.attacks import diff_attacks

cipher = RECTANGLE_BLOCKCIPHER(r=4, version=[64, 80])

trails = diff_attacks(
    cipher,
    goal='DIFFERENTIALPATH_PROB',
    constraints=['INPUT_NOT_ZERO'],
    objective_target='OPTIMAL',
    config_model={'model_type': 'sat'},
    config_solver={'solver': 'Cadical195'},
)

if trails:
    trail = trails[0]
    print(f"\nOptimal trail found!")
    print(f"  Total weight: {trail.data['diff_weight']}")
    print(f"  Round weights: {trail.data['rounds_diff_weight']}")
    print(f"  Probability: {2**(-trail.data['diff_weight']):.6e}")
