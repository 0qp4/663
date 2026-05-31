from pathlib import Path
from math import log2
from attacks.attack_trace import DifferentialTrail
import tools.model_constraints as model_constraints
import tools.model_objective as model_objective
import tools.sat_search as sat_search

try:
    import tools.milp_search as milp_search
    milp_search_available = True
except ImportError:
    milp_search_available = False

ROOT = Path(__file__).resolve().parents[1] # differential_cryptanalysis.py -> attacks -> <ROOT>
FILES_DIR = ROOT / "files"
FILES_DIR.mkdir(parents=True, exist_ok=True)


# **************************************************************************** #
# This module is the interface for differential attacks, including:
# 1. search differential trails
# **************************************************************************** #


# ---------------------- Model and Solver Configuration ----------------------
def parse_and_set_configs(cipher, goal, objective_target, config_model, config_solver): # Parse input parameters and apply default values for model and solver configurations.
    # ===== Set Default config_model and config_solver =====
    config_model = config_model or {}
    config_solver = config_solver or {}

    # Set "model_type", the automated model framework, 'milp' or 'sat'
    config_model["model_type"] = config_model.get("model_type", "milp").lower()

    # Set "functions", "rounds", "layers", "positions" for modeling
    functions, rounds, layers, positions = model_constraints.fill_functions_rounds_layers_positions(cipher, functions=None, rounds=None, layers=None, positions=None)
    config_model.setdefault("functions", functions)
    config_model.setdefault("rounds", rounds)
    config_model.setdefault("layers", layers)
    config_model.setdefault("positions", positions)

    # Set "solver" for solving the model
    config_solver.setdefault("solver", "DEFAULT")

    # Determine output directory
    output_dir = config_model.get("output_dir", None)
    if output_dir:
        # Use custom output directory
        target_dir = Path(output_dir)
    else:
        # Use default files directory
        target_dir = FILES_DIR
    target_dir.mkdir(parents=True, exist_ok=True)

    if config_model["model_type"] == "milp":
        # Set the model "filename".
        config_model["filename"] = str(target_dir / f"{cipher.nbr_rounds}round_{cipher.name}_{goal}_{objective_target}_milp_model.lp")

    elif config_model["model_type"] == "sat":
        # Set the model "filename".
        config_model["filename"] = str(target_dir / f"{cipher.nbr_rounds}round_{cipher.name}_{goal}_{objective_target}_sat_model.cnf")

    # Set solution_number to a large value if not defined when searching for differentials
    if goal == "DIFFERENTIAL_PROB":
        config_solver.setdefault("solution_number", 1000000)

    return config_model, config_solver


# -------------------- Predefined Additional Constraints --------------------
def expand_var_ids(var, bitwise=False): # Expand variable IDs by bits if necessary.
    if bitwise and var.bitsize > 1:
        return [f"{var.ID}_{i}" for i in range(var.bitsize)]
    return [var.ID]

def gen_input_non_zero_constraints(cipher, goal, config_model): # Generate input non-zero constraints for the cipher based on the goal and model type.
    cons_vars = [var for cons in cipher.inputs_constraints for var in cons.input_vars]
    model_type = config_model.get("model_type", "milp").lower()
    encoding = config_model.get("atleast_encoding_sat", "SEQUENTIAL") if model_type == "sat" else None
    bitwise = "TRUNCATEDDIFF" not in goal
    constraints = model_constraints.gen_predefined_constraints(
        model_type=model_type,
        cons_type="SUM_AT_LEAST",
        cons_vars=cons_vars,
        cons_value=1,
        bitwise=bitwise,
        encoding=encoding,
    )
    # MILP-specific: declare decision variables as binary
    if model_type == "milp":
        binary_vars = []
        for var in cons_vars:
            binary_vars += (expand_var_ids(var, bitwise=bitwise))
        if binary_vars:
            constraints.append("Binary\n" + " ".join(binary_vars))
    return constraints


def gen_fixed_input_output_constraints(in_out, fix_diff, cipher, config_model):
    cons_vars = []
    if in_out == "input":
        assert hasattr(cipher, "inputs") and isinstance(cipher.inputs, dict), "[WARNING] Cipher 'inputs' attribute invalid."
        for input_name in cipher.inputs.keys():
            cons_vars += cipher.inputs[input_name]
    elif in_out == "output":
        assert hasattr(cipher, "outputs") and isinstance(cipher.outputs, dict), "[WARNING] Cipher 'outputs' attribute invalid."
        for output_name in cipher.outputs.keys():
            cons_vars += cipher.outputs[output_name]
    else:
        raise ValueError(f"[WARNING] Invalid in_out: {in_out}. Expected 'input' or 'output'.")
    n = len(cons_vars) * cons_vars[0].bitsize
    s = fix_diff.strip().lower()
    if s.startswith("0b"):
        diff = s[2:].zfill(n)
    elif s.startswith("0x"):
        diff = bin(int(s, 16))[2:].zfill(n)
    else:
        raise ValueError(f"[WARNING] Invalid fix_diff format: {fix_diff}. Expected binary (0b...) or hexadecimal (0x...) string.")

    model_type = config_model.get("model_type", "milp").lower()
    constraints = []
    if cons_vars[0].bitsize == 1:
        for i in range(len(cons_vars)):
            if model_type == "sat":
                if diff[i] == '1':
                    constraints.append(f"{cons_vars[i].ID}")
                elif diff[i] == '0':
                    constraints.append(f"-{cons_vars[i].ID}")
            elif model_type == "milp":
                constraints.append(f"{cons_vars[i].ID} = {diff[i]}")
                constraints.append("Binary\n" + f"{cons_vars[i].ID}")
        return constraints
    for i in range(len(cons_vars)):
        for j in range(cons_vars[i].bitsize):
            if model_type == "sat":
                if diff[i*cons_vars[i].bitsize+j] == '1':
                    constraints.append(f"{cons_vars[i].ID}_{j}")
                elif diff[i*cons_vars[i].bitsize+j] == '0':
                    constraints.append(f"-{cons_vars[i].ID}_{j}")
            elif model_type == "milp":
                constraints.append(f"{cons_vars[i].ID}_{j} = {diff[i*cons_vars[i].bitsize+j]}")
                constraints.append("Binary\n" + f"{cons_vars[i].ID}_{j}")
    return constraints


# -------------------- Key Differential Constraints --------------------
def gen_key_diff_constraints(cipher, config_model, goal="DIFFERENTIALPATH_PROB", target="NOT_ZERO", rounds=None, extraction_layer=1, fixed_value=1, k=1):
    """
    Generate constraints on the key difference variables in a block cipher.

    This function provides a unified interface for enforcing key difference constraints,
    analogous to gen_input_non_zero_constraints() but for key variables.

    Parameters
    ----------
    cipher : Primitive
        The cipher object (must be a Block_cipher with KEY_SCHEDULE and SUBKEYS functions).
    config_model : dict
        Model configuration dict (used to determine model_type and encoding).
    goal : str
        The differential attack goal (e.g. "DIFFERENTIALPATH_PROB").
        Determines whether bitwise expansion is used.
    target : str
        The constraint type to generate:
        - "NOT_ZERO"   : At least one bit of the key diff must be 1 (OR of all bits).
                        This is the most common related-key constraint, forcing the
                        key difference to be non-zero.
        - "EXACTLY_v" : All key-diff bits must equal a given value v (0 or 1).
                        Use the 'fixed_value' parameter to specify the value.
                        (This is the PRESENT-related-key style, fixed per bit.)
        - "SUM_AT_LEAST_k" : At least k bits of the key diff must be 1.
    rounds : list of int or None
        Which rounds to generate key constraints for.
        - None     : Apply constraint to ALL rounds (rounds 1..nbr_rounds).
        - [r]      : Apply constraint to round r only.
        - [r1,r2]  : Apply constraint to rounds r1..r2.
    extraction_layer : int
        The layer of the SUBKEYS function that holds the extracted subkey variables.
        Both PRESENT and RECTANGLE store the extracted 64-bit subkey at Layer 1
        of the SUBKEYS function (via ExtractionLayer). Defaults to 1.

        Variable format at the extracted layer: ``vsk_{round}_1_{bit}`` (bits 0..63).

    fixed_value : int
        Used only with ``target="EXACTLY_v"``. The value (0 or 1) to assign to
        every subkey-diff bit. Defaults to 1.

    k : int
        Used only with ``target="SUM_AT_LEAST_k"`` or ``target="SUM_EXACTLY_k"``.
        The minimum/exact number of active key-diff bits required. Defaults to 1.

    Returns
    -------
    list of str
        List of generated model constraint strings (in MILP or SAT format).

    Notes
    -----
    For a block cipher, the key difference variables live in two places:

    1. SUBKEYS function — ``cipher.functions["SUBKEYS"]``:
       Contains the subkey differences for each round, extracted from the key
       schedule via ExtractionLayer. Variable ID format: ``v{label}_{round}_{layer}_{pos}``.
       - PRESENT  (label='sk', 64-bit subkey):  ``vsk_{round}_1_{bit}``  (layer=1)
       - RECTANGLE (label='sk', 64-bit subkey): ``vsk_{round}_1_{bit}``  (layer=1)

    2. KEY_SCHEDULE function — ``cipher.functions["KEY_SCHEDULE"]``:
       Contains the full 80/128-bit key schedule state variables.
       Variable ID format: ``vk_{round}_{layer}_{pos}``.
       - RECTANGLE-80: 112 words per round (80 key + 32 temp), indexed 0-111.

    The constraint on SUBKEYS is the standard choice for related-key differential
    analysis because it directly constrains the per-round subkey XOR difference.

    Examples
    --------
    1. Force the key difference to be non-zero in all rounds (most common pattern):

       >>> from primitives.rectangle import RECTANGLE_BLOCKCIPHER
       >>> cipher = RECTANGLE_BLOCKCIPHER(r=8, version=[64, 80])
       >>> config = {"model_type": "sat"}
       >>> constraints = gen_key_diff_constraints(cipher, config, target="NOT_ZERO")
       >>> trails = attacks.diff_attacks(
       ...     cipher, goal="DIFFERENTIALPATH_PROB",
       ...     constraints=constraints,
       ...     objective_target="OPTIMAL",
       ...     config_model=config,
       ...     config_solver={"solver": "Cadical195"},
       ... )

    2. Fix every subkey difference to a specific value (PRESENT-related-key style):

       >>> for rnd in range(1, 9):
       ...     K = bin(test_trail_subkey[rnd-1])[2:].zfill(64)
       ...     for bit in range(64):
       ...         constraints += gen_key_diff_constraints(
       ...             cipher, config, goal="DIFFERENTIALPATH_PROB",
       ...             target="EXACTLY_v", fixed_value=int(K[bit]),
       ...             rounds=[rnd], extraction_layer=1
       ...         )

    3. Require at least 3 active subkey bits per round:

       >>> constraints = gen_key_diff_constraints(
       ...     cipher, config, target="SUM_AT_LEAST_k", k=3
       ... )
    """
    if "SUBKEYS" not in cipher.functions:
        raise ValueError("[ERROR] Cipher does not have a SUBKEYS function. "
                         "gen_key_diff_constraints only works for Block_cipher types.")
    subkeys_func = cipher.functions["SUBKEYS"]
    nbr_rounds = subkeys_func.nbr_rounds
    sk_label = subkeys_func.label  # e.g. 'sk' for PRESENT and RECTANGLE

    # Resolve rounds
    if rounds is None:
        target_rounds = list(range(1, nbr_rounds + 1))
    elif isinstance(rounds, int):
        target_rounds = [rounds]
    else:
        target_rounds = list(rounds)

    model_type = config_model.get("model_type", "milp").lower()
    _enc_raw = config_model.get("atleast_encoding_sat", None)
    if model_type == "sat":
        if _enc_raw == "SEQUENTIAL" or _enc_raw is None:
            encoding = 1  # CardEnc encoding 1 = ladder
        else:
            encoding = _enc_raw
    else:
        encoding = None
    bitwise = "TRUNCATEDDIFF" not in goal

    # All subkey variables for the targeted rounds.
    # The extracted subkey lives at `extraction_layer` (e.g. layer 1).
    all_sk_vars = []
    for rnd in target_rounds:
        layer_vars = subkeys_func.vars[rnd][extraction_layer]
        all_sk_vars.extend(expand_var_ids(v, bitwise=bitwise) for v in layer_vars)

    constraints = []

    if target == "NOT_ZERO":
        # At least one key-diff bit must be 1 across all targeted rounds.
        # Build a flat list of all bit-level variable names.
        flat_vars = []
        for varlist in all_sk_vars:
            flat_vars.extend(varlist)

        constraints += model_constraints.gen_predefined_constraints(
            model_type=model_type,
            cons_type="SUM_AT_LEAST",
            cons_vars=flat_vars,
            cons_value=1,
            bitwise=False,  # vars already expanded
            encoding=encoding,
        )
        if model_type == "milp":
            if flat_vars:
                constraints.append("Binary\n" + " ".join(flat_vars))

    elif target == "EXACTLY_v":
        for rnd in target_rounds:
            layer_vars = subkeys_func.vars[rnd][extraction_layer]
            for v in layer_vars:
                expanded = expand_var_ids(v, bitwise=bitwise)
                for var_name in expanded:
                    constraints += model_constraints.gen_predefined_constraints(
                        model_type=model_type,
                        cons_type="EXACTLY",
                        cons_vars=[var_name],
                        cons_value=fixed_value,
                        bitwise=False,
                    )
                    if model_type == "milp":
                        constraints.append("Binary\n" + var_name)

    elif target == "SUM_AT_LEAST_k":
        flat_vars = []
        for varlist in all_sk_vars:
            flat_vars.extend(varlist)

        constraints += model_constraints.gen_predefined_constraints(
            model_type=model_type,
            cons_type="SUM_AT_LEAST",
            cons_vars=flat_vars,
            cons_value=k,
            bitwise=False,
            encoding=encoding,
        )
        if model_type == "milp":
            if flat_vars:
                constraints.append("Binary\n" + " ".join(flat_vars))

    elif target == "SUM_EXACTLY_k":
        flat_vars = []
        for varlist in all_sk_vars:
            flat_vars.extend(varlist)

        constraints += model_constraints.gen_predefined_constraints(
            model_type=model_type,
            cons_type="SUM_EXACTLY",
            cons_vars=flat_vars,
            cons_value=k,
            bitwise=False,
            encoding=encoding,
        )
        if model_type == "milp":
            if flat_vars:
                constraints.append("Binary\n" + " ".join(flat_vars))

    else:
        raise ValueError(f"[ERROR] Unknown target '{target}'. "
                         f"Supported: 'NOT_ZERO', 'EXACTLY_v', 'SUM_AT_LEAST_k', 'SUM_EXACTLY_k'.")

    return constraints


# ------------------------ Differential Trail Search -------------------------
def search_diff_trail(cipher, goal="DIFFERENTIALPATH_PROB", constraints=["INPUT_NOT_ZERO"], objective_target="OPTIMAL", show_mode=0, config_model=None, config_solver=None):
    """
    Perform differential attacks on a given cipher using the specified model_type.

    Parameters:
        cipher (Cipher): The cipher object to analyze.
        goal (str): The specific cryptanalysis goal: GOAL or GOAL_OPERATOR_NUMBER
            - DIFFERENTIAL_SBOXCOUNT
            - DIFFERENTIALPATH_PROB
            - DIFFERENTIAL_PROB
            - TRUNCATEDDIFF_SBOXCOUNT
        constraints (list of string): User-specified constraints to be added to the model.
            - ['INPUT_NOT_ZERO']: Automatically add input non-zero constraints as required by the goal.
            - ['KEY_NOT_ZERO']: Generate non-zero key-difference constraints via gen_key_diff_constraints().
            - Specific variables constraints, e.g., ['v_1_0_0 = 1', 'v_2_1_0 = 0'] for MILP, ['v_1_0_0', '-v_2_1_0'] for SAT.
            - Any other user-defined constraints.
        objective_target (str): The target for the objective function, which can be:
            - 'OPTIMAL': Find the optimal solution.
            - 'AT MOST X': Find a solution with an objective value at most X.
            - 'EXACTLY X': Find a solution with an objective value exactly X.
            - 'AT LEAST X': Find a solution with an objective value at least X.
            - 'EXISTENCE': Find any feasible solution.
        show_mode (int): The level of solution/result visualization: 0, 1, 2.
        config_model (dict): Optional advanced arguments for modeling, see attacks.parse_and_set_configs() for details.
        config_solver (dict): Optional advanced arguments for solving, see attacks.parse_and_set_configs() for details.

    Returns: A list of differential trail objects.
    """

    assert any(goal.startswith(prefix) for prefix in ["DIFFERENTIAL_SBOXCOUNT", "DIFFERENTIALPATH_PROB", "DIFFERENTIAL_PROB", "TRUNCATEDDIFF_SBOXCOUNT"]), f"Invalid goal: {goal}. Expected one of ['DIFFERENTIAL_SBOXCOUNT', 'DIFFERENTIALPATH_PROB', 'DIFFERENTIAL_PROB', 'TRUNCATEDDIFF_SBOXCOUNT']"
    assert isinstance(constraints, list), f"Invalid constraints: {constraints}. Expected a list of strings."
    assert any(objective_target.startswith(prefix) for prefix in ['OPTIMAL', 'AT MOST', 'EXACTLY', 'AT LEAST', 'EXISTENCE']), f"Invalid objective_target: {objective_target}. Expected one of ['OPTIMAL', 'AT MOST X', 'EXACTLY X', 'AT LEAST X']"
    assert show_mode in [0, 1, 2, 3], f"Invalid show_mode: {show_mode}. Expected one of [0, 1, 2]"
    assert isinstance(config_model, dict) or config_model is None, f"Invalid config_model: {config_model}. Expected a dictionary or None."
    assert isinstance(config_solver, dict) or config_solver is None, f"Invalid config_solver: {config_solver}. Expected a dictionary or None."

    # Step 1. Parse and set model and solver configurations.
    config_model, config_solver = parse_and_set_configs(cipher, goal, objective_target, config_model, config_solver)
    model_type = config_model.get("model_type", "milp")

    # Step 2. Generate round constraints and objective function for the cipher.
    round_constraints, obj_fun = model_constraints.gen_round_model_constraint_obj_fun(cipher, goal, model_type, config_model)

    # Step 3. Process additional constraints.
    model_cons = []
    for cons in constraints:
        if cons == "INPUT_NOT_ZERO":  # Deal with specific additional constraints.
            model_cons += gen_input_non_zero_constraints(cipher, goal, config_model)
        elif cons == "KEY_NOT_ZERO":
            model_cons += gen_key_diff_constraints(cipher, config_model, goal=goal, target="NOT_ZERO")
        else:
            model_cons += [cons]
    model_cons += round_constraints

    # For the goal of searching for differentials, fix the input and output differences
    if goal == "DIFFERENTIAL_PROB":
        input_diff = config_model.get("input_diff", None)
        output_diff = config_model.get("output_diff", None)
        if input_diff == None and output_diff == None:
            raise ValueError("For goal='DIFFERENTIAL_PROB', either input_diff or output_diff must be specified in config_model.")
        if input_diff is not None:
            model_cons += gen_fixed_input_output_constraints("input", input_diff, cipher, config_model)
        if output_diff is not None:
            model_cons += gen_fixed_input_output_constraints("output", output_diff, cipher, config_model)

    # Step 4: Modeling and Solving.
    if model_type == "milp":
        solutions = milp_search.modeling_solving_milp(objective_target, model_cons, obj_fun, config_model, config_solver)

    elif model_type == "sat":
        if goal in ["DIFFERENTIALPATH_PROB", "DIFFERENTIAL_PROB"] and model_objective.has_Sbox_with_decimal_weights(cipher, goal):
            config_model["decimal_objective_function"] = {}
            Sbox = model_objective.detect_Sbox(cipher)
            config_model["decimal_objective_function"]["Sbox"] = Sbox
            if goal in {'DIFFERENTIALPATH_PROB', 'DIFFERENTIAL_PROB'}:
                config_model["decimal_objective_function"]["table"] = Sbox.computeDDT()

        solutions = sat_search.modeling_solving_sat(objective_target, model_cons, obj_fun, config_model, config_solver)

    else:
        raise ValueError(f"Invalid model_type: {model_type}. Expected one of ['milp', 'sat'].")

    # Step 5: Extract and Visualize Trails from Solutions.
    if isinstance(solutions, list):
        return extract_and_format_diff_trails(cipher, goal, config_model, config_solver, show_mode, solutions)

    raise ValueError("[WARNING] No valid solutions found.")


# -------------------- Trail Extraction and Visualization --------------------
def extract_and_format_diff_trails(cipher, goal, config_model, config_solver, show_mode, solutions):
    trails = []
    trail_structs = []
    pr = 0
    for i, sol in enumerate(solutions):
        trail_struct = extract_trail_structures(cipher, goal, sol)
        if trail_struct in trail_structs:
            continue
        trail_structs.append(trail_struct)
        data = {"cipher": f"{cipher.functions['PERMUTATION'].nbr_rounds}_round_{cipher.name}",
                "functions": config_model["functions"],
                "rounds": config_model["rounds"],
                "config_model": config_model,
                "config_solver": config_solver,
                "trail_struct": trail_struct,
                "diff_weight": sol.get("obj_fun_value"),
                "rounds_diff_weight": sol.get("rounds_obj_fun_values")}
        trail = DifferentialTrail(data, solution_trace=sol)
        if i > 0:
            print(f"[INFO] Saving the {i+1}-th Trail.")
            trail.json_filename = trail.json_filename.replace(".json", f"_{i}.json") if trail.json_filename else str(FILES_DIR / f"{trail.data['cipher']}_trail_{i}.json")
            trail.txt_filename = trail.txt_filename.replace(".txt", f"_{i}.txt") if trail.txt_filename else str(FILES_DIR / f"{trail.data['cipher']}_trail_{i}.txt")
        trail.save_json()
        trail.save_txt(show_mode=show_mode)  # Print the trail in a human-readable format and save it to a file.
        trails.append(trail)
        pr += 2 ** ( - trail.data['diff_weight'] ) if trail.data['diff_weight'] is not None else 0
    if solutions and goal == "DIFFERENTIAL_PROB":
        print(f"[INFO] Total probability of all {len(trails)} found trails: 2^{log2(pr) if pr > 0 else 'undefined'}")
    return trails

def extract_trail_structures(cipher, goal, solution):
    """
    Extract a structured differential trail (trail_struct) from a solver assignment.

    Returned structure (example):
    """
    bitwise = "TRUNCATEDDIFF" not in goal

    def _get_solution_bit(var_id): # Map a variable id to '0'/'1'/'-'.
        v = solution.get(var_id, None)
        if v is None:
            return "-"
        try: # robust handling for bool/int/float
            return "1" if int(round(v)) == 1 else "0"
        except Exception:
            return "-"

    def node(var):
        """Build a per-variable node."""
        ids = expand_var_ids(var, bitwise=bitwise)
        bits = "".join(_get_solution_bit(v_id) for v_id in ids)
        return {
            "var_ID": getattr(var, "ID", str(var)), # ID of var
            "variables": ids, # List of extended word/bit variables from the given var
            "bin_values": bits, # Binary string value
            }

    # ------------------------------ Build trail_struct ------------------------------
    trail_struct = {
        "bitwise": bitwise,
        "inputs": {},
        "outputs": {},
        "functions": {}
    }

    # ------------------------------ Inputs / Outputs ------------------------------
    # Prefer cipher.inputs/cipher.outputs if present; otherwise fall back to constraints.
    if hasattr(cipher, "inputs") and isinstance(cipher.inputs, dict):
        for name, var_list in cipher.inputs.items():
            trail_struct["inputs"][name] = [node(v) for v in var_list]
    if hasattr(cipher, "outputs") and isinstance(cipher.outputs, dict):
        for name, var_list in cipher.outputs.items():
            trail_struct["outputs"][name] = [node(v) for v in var_list]

    # ------------------------------ Functions / Rounds / Layers ------------------------------
    for fun in cipher.functions:
        fun_store = {
        "rounds": list(range(1, cipher.functions[fun].nbr_rounds + 1)),
        "nbr_words": cipher.functions[fun].nbr_words if hasattr(cipher.functions[fun], "nbr_words") else None,
        "nbr_temp_words": cipher.functions[fun].nbr_temp_words if hasattr(cipher.functions[fun], "nbr_temp_words") else None
        }
        for r in range(1, cipher.functions[fun].nbr_rounds + 1):
            round_store = {}
            for l in range(cipher.functions[fun].nbr_layers + 1):
                layer_nodes = [node(v) for v in cipher.functions[fun].vars[r][l]]
                round_store[l] = layer_nodes
            fun_store[r] = round_store
        trail_struct["functions"][fun] = fun_store
    return trail_struct
