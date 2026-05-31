from primitives.primitives import Permutation, Block_cipher, generateID
from operators.Sbox import RECTANGLE_Sbox
from operators.boolean_operators import XOR
import operators.operators as op
import variables.variables as var


ROUND_CONSTANTS = [
    0x01, 0x02, 0x04, 0x09, 0x12,
    0x05, 0x0B, 0x16, 0x0C, 0x19,
    0x13, 0x07, 0x0F, 0x1F, 0x1E,
    0x1C, 0x18, 0x11, 0x03, 0x06,
    0x0D, 0x1B, 0x17, 0x0E, 0x1D,
]


def _bits_from_rows(rows):
    return [int(bit) for row in rows for bit in row]


def _row_indexes(row, row_size):
    start = row * row_size
    return list(range(start, start + row_size))


def _bit_index(row, row_size, bit_pos):
    return row * row_size + (row_size - 1 - bit_pos)


def _state_sbox_indexes():
    return [[_bit_index(3, 16, j), _bit_index(2, 16, j), _bit_index(1, 16, j), _bit_index(0, 16, j)] for j in range(16)]


def _state_shift_permutation():
    shifts = [0, 1, 12, 13]
    perm = []
    for row, shift in enumerate(shifts):
        for col in range(16):
            perm.append(row * 16 + ((col + shift) % 16))
    return perm


def _round_constant_table():
    return [[(rc >> bit) & 1 for bit in reversed(range(5))] for rc in ROUND_CONSTANTS]


def _add_identity_constraints(function, round_idx, layer_idx, indexes):
    for pos in indexes:
        function.constraints[round_idx][layer_idx].append(
            op.Equal(
                [function.vars[round_idx][layer_idx][pos]],
                [function.vars[round_idx][layer_idx + 1][pos]],
                ID=generateID("ID", round_idx, layer_idx + 1, pos),
            )
        )


def _add_key_schedule_sbox(function, round_idx, layer_idx, column_count, row_size):
    active = set()
    for col in range(column_count):
        indexes = [_bit_index(3, row_size, col), _bit_index(2, row_size, col), _bit_index(1, row_size, col), _bit_index(0, row_size, col)]
        active.update(indexes)
        function.constraints[round_idx][layer_idx].append(
            RECTANGLE_Sbox(
                [function.vars[round_idx][layer_idx][idx] for idx in indexes],
                [function.vars[round_idx][layer_idx + 1][idx] for idx in indexes],
                ID=generateID("K_SB", round_idx, layer_idx + 1, col),
            )
        )
    remaining = [idx for idx in range(function.nbr_words + function.nbr_temp_words) if idx not in active]
    _add_identity_constraints(function, round_idx, layer_idx, remaining)


def _add_key_schedule_round_80(function, round_idx, constant_table):
    row0 = _row_indexes(0, 16)
    row1 = _row_indexes(1, 16)
    row2 = _row_indexes(2, 16)
    row3 = _row_indexes(3, 16)
    row4 = _row_indexes(4, 16)
    tmp_rot0 = list(range(80, 96))
    tmp_rot3 = list(range(96, 112))

    _add_key_schedule_sbox(function, round_idx, 0, column_count=4, row_size=16)

    for pos in range(80):
        function.constraints[round_idx][1].append(
            op.Equal(
                [function.vars[round_idx][1][pos]],
                [function.vars[round_idx][2][pos]],
                ID=generateID("K_KEEP", round_idx, 2, pos),
            )
        )
    for col in range(16):
        function.constraints[round_idx][1].append(
            op.Equal(
                [function.vars[round_idx][1][row0[(col + 8) % 16]]],
                [function.vars[round_idx][2][tmp_rot0[col]]],
                ID=generateID("K_ROT0", round_idx, 2, col),
            )
        )
        function.constraints[round_idx][1].append(
            op.Equal(
                [function.vars[round_idx][1][row3[(col + 12) % 16]]],
                [function.vars[round_idx][2][tmp_rot3[col]]],
                ID=generateID("K_ROT3", round_idx, 2, col),
            )
        )

    for col in range(16):
        function.constraints[round_idx][2].append(
            XOR(
                [function.vars[round_idx][2][tmp_rot0[col]], function.vars[round_idx][2][row1[col]]],
                [function.vars[round_idx][3][row0[col]]],
                ID=generateID("K_XOR0", round_idx, 3, col),
            )
        )
        function.constraints[round_idx][2].append(
            op.Equal(
                [function.vars[round_idx][2][row2[col]]],
                [function.vars[round_idx][3][row1[col]]],
                ID=generateID("K_EQ1", round_idx, 3, 16 + col),
            )
        )
        function.constraints[round_idx][2].append(
            op.Equal(
                [function.vars[round_idx][2][row3[col]]],
                [function.vars[round_idx][3][row2[col]]],
                ID=generateID("K_EQ2", round_idx, 3, 32 + col),
            )
        )
        function.constraints[round_idx][2].append(
            XOR(
                [function.vars[round_idx][2][tmp_rot3[col]], function.vars[round_idx][2][row4[col]]],
                [function.vars[round_idx][3][row3[col]]],
                ID=generateID("K_XOR3", round_idx, 3, 48 + col),
            )
        )
        function.constraints[round_idx][2].append(
            op.Equal(
                [function.vars[round_idx][2][row0[col]]],
                [function.vars[round_idx][3][row4[col]]],
                ID=generateID("K_EQ4", round_idx, 3, 64 + col),
            )
        )
        function.constraints[round_idx][2].append(
            op.Equal(
                [function.vars[round_idx][2][tmp_rot0[col]]],
                [function.vars[round_idx][3][tmp_rot0[col]]],
                ID=generateID("K_TMP0", round_idx, 3, 80 + col),
            )
        )
        function.constraints[round_idx][2].append(
            op.Equal(
                [function.vars[round_idx][2][tmp_rot3[col]]],
                [function.vars[round_idx][3][tmp_rot3[col]]],
                ID=generateID("K_TMP3", round_idx, 3, 96 + col),
            )
        )

    function.AddConstantLayer(
        "K_C",
        round_idx,
        3,
        "xor",
        [None] * 11 + [True] * 5 + [None] * (function.nbr_words + function.nbr_temp_words - 16),
        constant_table,
    )


def _add_key_schedule_round_128(function, round_idx, constant_table):
    row0 = _row_indexes(0, 32)
    row1 = _row_indexes(1, 32)
    row2 = _row_indexes(2, 32)
    row3 = _row_indexes(3, 32)
    tmp_rot0 = list(range(128, 160))
    tmp_rot2 = list(range(160, 192))

    _add_key_schedule_sbox(function, round_idx, 0, column_count=8, row_size=32)

    for pos in range(128):
        function.constraints[round_idx][1].append(
            op.Equal(
                [function.vars[round_idx][1][pos]],
                [function.vars[round_idx][2][pos]],
                ID=generateID("K_KEEP", round_idx, 2, pos),
            )
        )
    for col in range(32):
        function.constraints[round_idx][1].append(
            op.Equal(
                [function.vars[round_idx][1][row0[(col + 8) % 32]]],
                [function.vars[round_idx][2][tmp_rot0[col]]],
                ID=generateID("K_ROT0", round_idx, 2, col),
            )
        )
        function.constraints[round_idx][1].append(
            op.Equal(
                [function.vars[round_idx][1][row2[(col + 16) % 32]]],
                [function.vars[round_idx][2][tmp_rot2[col]]],
                ID=generateID("K_ROT2", round_idx, 2, col),
            )
        )

    for col in range(32):
        function.constraints[round_idx][2].append(
            XOR(
                [function.vars[round_idx][2][tmp_rot0[col]], function.vars[round_idx][2][row1[col]]],
                [function.vars[round_idx][3][row0[col]]],
                ID=generateID("K_XOR0", round_idx, 3, col),
            )
        )
        function.constraints[round_idx][2].append(
            op.Equal(
                [function.vars[round_idx][2][row2[col]]],
                [function.vars[round_idx][3][row1[col]]],
                ID=generateID("K_EQ1", round_idx, 3, 32 + col),
            )
        )
        function.constraints[round_idx][2].append(
            XOR(
                [function.vars[round_idx][2][tmp_rot2[col]], function.vars[round_idx][2][row3[col]]],
                [function.vars[round_idx][3][row2[col]]],
                ID=generateID("K_XOR2", round_idx, 3, 64 + col),
            )
        )
        function.constraints[round_idx][2].append(
            op.Equal(
                [function.vars[round_idx][2][row0[col]]],
                [function.vars[round_idx][3][row3[col]]],
                ID=generateID("K_EQ3", round_idx, 3, 96 + col),
            )
        )
        function.constraints[round_idx][2].append(
            op.Equal(
                [function.vars[round_idx][2][tmp_rot0[col]]],
                [function.vars[round_idx][3][tmp_rot0[col]]],
                ID=generateID("K_TMP0", round_idx, 3, 128 + col),
            )
        )
        function.constraints[round_idx][2].append(
            op.Equal(
                [function.vars[round_idx][2][tmp_rot2[col]]],
                [function.vars[round_idx][3][tmp_rot2[col]]],
                ID=generateID("K_TMP2", round_idx, 3, 160 + col),
            )
        )

    function.AddConstantLayer(
        "K_C",
        round_idx,
        3,
        "xor",
        [None] * 27 + [True] * 5 + [None] * (function.nbr_words + function.nbr_temp_words - 32),
        constant_table,
    )


class RECTANGLE_permutation(Permutation):
    def __init__(self, name, s_input, s_output, nbr_rounds=None, represent_mode=0):
        if nbr_rounds is None:
            nbr_rounds = 25
        if represent_mode != 0:
            raise ValueError("RECTANGLE currently supports only represent_mode=0.")

        super().__init__(name, s_input, s_output, nbr_rounds, [2, 64, 0, 1])
        state = self.functions["PERMUTATION"]
        sbox_index = _state_sbox_indexes()
        shift_perm = _state_shift_permutation()

        for rnd in range(1, nbr_rounds + 1):
            state.SboxLayer("SB", rnd, 0, RECTANGLE_Sbox, index=sbox_index)
            state.PermutationLayer("SR", rnd, 1, shift_perm)

    def gen_test_vectors(self):
        pass


def RECTANGLE_PERMUTATION(r=None, represent_mode=0, copy_operator=False):
    my_input = [var.Variable(1, ID=f"in{i}") for i in range(64)]
    my_output = [var.Variable(1, ID=f"out{i}") for i in range(64)]
    my_permutation = RECTANGLE_permutation("RECTANGLE_PERM", my_input, my_output, nbr_rounds=r, represent_mode=represent_mode)
    my_permutation.gen_test_vectors()
    my_permutation.post_initialization(copy_operator=copy_operator)
    return my_permutation


class RECTANGLE_block_cipher(Block_cipher):
    def __init__(
        self, name, version, p_input, k_input, c_output, nbr_rounds=None, represent_mode=0, final_key_addition=True
    ):
        assert version in [[64, 80], [64, 128]], f"Unsupported version: {version}."
        if represent_mode != 0:
            raise ValueError("RECTANGLE currently supports only represent_mode=0.")

        if nbr_rounds is not None:
            algorithm_rounds = nbr_rounds
            if algorithm_rounds < 0:
                raise ValueError("RECTANGLE round number must be non-negative.")
            if not final_key_addition and algorithm_rounds == 0:
                raise ValueError("RECTANGLE without final key addition needs at least one round.")
        else:
            algorithm_rounds = 25
            if final_key_addition:
                print(
                    "[INFO] For RECTANGLE, after 25 round transformations, there is still a final AddRoundKey layer. "
                    f"Hence, the internal modeling round number is set to {algorithm_rounds + 1}."
                )

        # Only add extra ARK round for the default 25-round algorithm with final_key_addition.
        # For explicit nbr_rounds, state_rounds equals algorithm_rounds (no extra ARK).
        if nbr_rounds is None and final_key_addition:
            state_rounds = algorithm_rounds + 1
        elif nbr_rounds is None:
            state_rounds = algorithm_rounds
        else:
            state_rounds = algorithm_rounds  # explicit nbr_rounds: no extra ARK
        self.algorithm_rounds = algorithm_rounds
        self.final_key_addition = final_key_addition

        if version == [64, 80]:
            s_config = [3, 64, 0, 1]
            k_config = [4, 80, 32, 1]
            sk_config = [1, 64, 0, 1]
        else:
            s_config = [3, 64, 0, 1]
            k_config = [4, 128, 64, 1]
            sk_config = [1, 64, 0, 1]

        super().__init__(name, p_input, k_input, c_output, state_rounds, state_rounds, s_config, k_config, sk_config)

        state = self.functions["PERMUTATION"]
        key_schedule = self.functions["KEY_SCHEDULE"]
        subkeys = self.functions["SUBKEYS"]
        constant_table = _round_constant_table()
        sbox_index = _state_sbox_indexes()
        shift_perm = _state_shift_permutation()

        if version == [64, 80]:
            extraction_indexes = list(range(64))
        else:
            extraction_indexes = list(range(16, 32)) + list(range(48, 64)) + list(range(80, 96)) + list(range(112, 128))

        for rnd in range(1, subkeys.nbr_rounds + 1):
            subkeys.ExtractionLayer("SK_EX", rnd, 0, extraction_indexes, key_schedule.vars[rnd][0])

        # KEY_SCHEDULE must update through round (nbr_rounds + 1) so that the subkey for
        # round nbr_rounds is fully defined. The SUBKEYS ExtractionLayer (built above)
        # extracts subkeys for rounds 1..nbr_rounds from key_schedule.vars[rnd][0], and
        # each extraction references the key state BEFORE that round's update. For round 2
        # (nbr_rounds=2), the extraction uses key_schedule.vars[2][0], which is the state
        # BEFORE round 2's update -- this state IS built by the round-1 update (the output
        # of round 1 becomes vars[2][0] after identity/Equal constraints propagate). However,
        # to also count KEY_SCHEDULE S-boxes for round 2, we must build round 2's update too.
        # More critically: if key_schedule_updates < nbr_rounds, then subkey variables for
        # rounds beyond key_schedule_updates have no KEY_SCHEDULE->SUBKEYS linkage, making
        # vsk_r_1_bit FREE variables -- KEY_NOT_ZERO constraints applied to them are NOPs.
        # Fix: always build at least nbr_rounds KEY_SCHEDULE updates.
        key_schedule_updates = max(algorithm_rounds, nbr_rounds) if final_key_addition else max(algorithm_rounds - 1, nbr_rounds - 1)
        for rnd in range(1, key_schedule_updates + 1):
            if version == [64, 80]:
                _add_key_schedule_round_80(key_schedule, rnd, constant_table)
            else:
                _add_key_schedule_round_128(key_schedule, rnd, constant_table)

        for rnd in range(1, state.nbr_rounds + 1):
            state.AddRoundKeyLayer("ARK", rnd, 0, XOR, subkeys, [1] * 64)
            # Extra final ARK round only for default 25-round with final_key_addition
            if rnd <= algorithm_rounds:
                state.SboxLayer("SB", rnd, 1, RECTANGLE_Sbox, index=sbox_index)
                state.PermutationLayer("SR", rnd, 2, shift_perm)
            elif rnd == state.nbr_rounds and nbr_rounds is None and final_key_addition:
                state.AddIdentityLayer("ID", rnd, 1)
                state.AddIdentityLayer("ID", rnd, 2)

    def gen_test_vectors(self, version):
        self.test_vectors = []

        if version == [64, 80]:
            plaintext = _bits_from_rows([
                "0000000000000000",
                "0000000000000000",
                "0000000000000000",
                "0000000000000000",
            ])
            key = _bits_from_rows([
                "0000000000000000",
                "0000000000000000",
                "0000000000000000",
                "0000000000000000",
                "0000000000000000",
            ])
            ciphertext = _bits_from_rows([
                "0010110110010110",
                "1110001101010100",
                "1110100010110001",
                "0000100001110100",
            ])
            self.test_vectors.append([[plaintext, key], ciphertext])

            plaintext = _bits_from_rows([
                "1111111111111111",
                "1111111111111111",
                "1111111111111111",
                "1111111111111111",
            ])
            key = _bits_from_rows([
                "1111111111111111",
                "1111111111111111",
                "1111111111111111",
                "1111111111111111",
                "1111111111111111",
            ])
            ciphertext = _bits_from_rows([
                "1001100101000101",
                "1010101000110100",
                "1010111000111101",
                "0000000100010010",
            ])
            self.test_vectors.append([[plaintext, key], ciphertext])


def RECTANGLE_BLOCKCIPHER(
    r=None, version=[64, 80], represent_mode=0, copy_operator=False, final_key_addition=True
):
    p_bitsize, k_bitsize = version
    plaintext = [var.Variable(1, ID=f"in{i}") for i in range(p_bitsize)]
    key = [var.Variable(1, ID=f"k{i}") for i in range(k_bitsize)]
    ciphertext = [var.Variable(1, ID=f"out{i}") for i in range(p_bitsize)]
    cipher = RECTANGLE_block_cipher(
        f"RECTANGLE{p_bitsize}_{k_bitsize}",
        version,
        plaintext,
        key,
        ciphertext,
        nbr_rounds=r,
        represent_mode=represent_mode,
        final_key_addition=final_key_addition,
    )
    cipher.gen_test_vectors(version=version)
    cipher.post_initialization(copy_operator=copy_operator)
    return cipher
