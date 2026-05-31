"""
RECTANGLE Key Differential Cryptanalysis - A SAT-based framework for
related-key differential analysis of the RECTANGLE lightweight block cipher.

Usage (after installation or when running from the project root):
    from primitives.rectangle import RECTANGLE_BLOCKCIPHER
    import attacks.differential_cryptanalysis as attacks

    cipher = RECTANGLE_BLOCKCIPHER(r=8, version=[64, 80])

    # Ordinary differential trail search
    trails = attacks.diff_attacks(
        cipher,
        goal="DIFFERENTIALPATH_PROB",
        constraints=["INPUT_NOT_ZERO"],
        objective_target="OPTIMAL",
        config_model={"model_type": "sat"},
        config_solver={"solver": "Cadical195"},
    )

    # Related-key differential trail search (KEY_NOT_ZERO constraint)
    trails = attacks.diff_attacks(
        cipher,
        goal="DIFFERENTIALPATH_PROB",
        constraints=["INPUT_NOT_ZERO", "KEY_NOT_ZERO"],
        objective_target="OPTIMAL",
        config_model={"model_type": "sat"},
        config_solver={"solver": "Cadical195"},
    )
"""
import sys
from pathlib import Path

_FILE_ = Path(__file__).resolve()
_PROJECT_ROOT = _FILE_.parent
if str(_PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(_PROJECT_ROOT))

__version__ = "1.0"
