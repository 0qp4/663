from abc import ABC
import variables.variables as var
import operators.operators as op
from operators.matrix import Matrix, GF2Linear_Trans
from operators.boolean_operators import ConstantXOR
from operators.modular_operators import ConstantAdd


def generateID(name, round_nb, layer, position):
    return name + '_' + str(round_nb) + '_' + str(layer) + '_' + str(position)


# ********************* LAYERED_FUNCTION ********************* #
class Layered_Function:
    def __init__(self, name, label, nbr_rounds, nbr_layers, nbr_words, nbr_temp_words, word_bitsize):
        self.name = name
        self.label = label
        self.nbr_rounds = nbr_rounds
        self.nbr_layers = nbr_layers
        self.nbr_words = nbr_words
        self.nbr_temp_words = nbr_temp_words
        self.word_bitsize = word_bitsize
        self.vars = [[[] for i in range(nbr_layers+1)] for j in range(nbr_rounds+1)]
        self.constraints = [[[] for i in range(nbr_layers+1)] for j in range(nbr_rounds+1)]
        for i in range(0, nbr_rounds+1):
            for l in range(0, nbr_layers+1):
                self.vars[i][l] = [var.Variable(word_bitsize, ID = generateID('v' + label,i,l,j)) for j in range(nbr_words + nbr_temp_words)]
        for i in range(0, nbr_rounds):
            self.constraints[i][nbr_layers] = [op.Equal([self.vars[i][nbr_layers][j]], [self.vars[i+1][0][j]], ID=generateID('LINK_EQ_' + label,i,nbr_layers+1,j)) for j in range(nbr_words + nbr_temp_words)]

    def display(self, representation='binary'):
        print("Name: " + str(self.name), " / nbr_words: " + str(self.nbr_words), " / word_bitsize: " + str(self.word_bitsize))
        print("Vars: [" + str([ len(self.vars[i]) for i in range(len(self.vars))])   + "]")
        print("Constraints: [" + str([ len(self.constraints[i]) for i in range(len(self.constraints))])  + "]")

    def SboxLayer(self, name, crt_round, crt_layer, sbox_operator, mask = None, index=None):
        if index is not None:
            bitsize = len(index[0])
            n_words = int((self.nbr_words+self.nbr_temp_words)/bitsize)
            if mask is None: mask = [1]*int(self.nbr_words/bitsize)
            if len(mask)<n_words: mask = mask + [0]*(n_words - len(mask))
            for j in range(n_words):
                if mask[j]==1:
                    in_vars = [self.vars[crt_round][crt_layer][i] for i in index[j]]
                    out_vars = [self.vars[crt_round][crt_layer+1][i] for i in index[j]]
                    self.constraints[crt_round][crt_layer].append(sbox_operator(in_vars, out_vars, ID=generateID(name,crt_round,crt_layer+1,j)))
                else:
                    for i in range(bitsize):
                        in_var = self.vars[crt_round][crt_layer][j*bitsize+i]
                        out_var = self.vars[crt_round][crt_layer+1][j*bitsize+i]
                        self.constraints[crt_round][crt_layer].append(op.Equal([in_var], [out_var], ID=generateID(name + "_EQ",crt_round,crt_layer+1,j)))
        else:
            if mask is None: mask = [1]*self.nbr_words
            if len(mask)<(self.nbr_words + self.nbr_temp_words): mask = mask + [0]*(self.nbr_words + self.nbr_temp_words - len(mask))
            for j in range(self.nbr_words + self.nbr_temp_words):
                in_var = self.vars[crt_round][crt_layer][j]
                out_var = self.vars[crt_round][crt_layer+1][j]
                if mask[j]==1:
                    self.constraints[crt_round][crt_layer].append(sbox_operator([in_var], [out_var], ID=generateID(name,crt_round,crt_layer+1,j)))
                else:
                    self.constraints[crt_round][crt_layer].append(op.Equal([in_var], [out_var], ID=generateID(name + "_EQ",crt_round,crt_layer+1,j)))

    def PermutationLayer(self, name, crt_round, crt_layer, permutation):
        if len(permutation)<(self.nbr_words + self.nbr_temp_words): permutation = permutation + [i for i in range(len(permutation), self.nbr_words + self.nbr_temp_words)]
        for j in range(len(permutation)):
            in_var = self.vars[crt_round][crt_layer][permutation[j]]
            out_var = self.vars[crt_round][crt_layer+1][j]
            self.constraints[crt_round][crt_layer].append(op.Equal([in_var], [out_var], ID=generateID(name + "_EQ",crt_round,crt_layer+1,j)))

    def RotationLayer(self, name, crt_round, crt_layer, rot):
        if type(rot[0]) is not list: rot = [rot]
        table = [None]*(self.nbr_words + self.nbr_temp_words)
        for r in rot:
            index_in = r[2]
            out_index = r[2] if len(r)==3 else r[3]
            table[out_index] = (r[0], r[1], index_in, out_index)
        for j in range(self.nbr_words + self.nbr_temp_words):
            if table[j] is not None:
                self.constraints[crt_round][crt_layer].append(op.Rot([self.vars[crt_round][crt_layer][table[j][2]]], [self.vars[crt_round][crt_layer+1][table[j][3]]], table[j][0], table[j][1], ID=generateID(name,crt_round,crt_layer+1,table[j][3])))
            else:
                self.constraints[crt_round][crt_layer].append(op.Equal([self.vars[crt_round][crt_layer][j]], [self.vars[crt_round][crt_layer+1][j]], ID=generateID(name + "_EQ",crt_round,crt_layer+1,j)))

    def AddIdentityLayer(self, name, crt_round, crt_layer):
        for j in range(self.nbr_words + self.nbr_temp_words):
            in_var = self.vars[crt_round][crt_layer][j]
            out_var = self.vars[crt_round][crt_layer+1][j]
            self.constraints[crt_round][crt_layer].append(op.Equal([in_var], [out_var], ID=generateID(name + "_EQ",crt_round,crt_layer+1,j)))

    def AddConstantLayer(self, name, crt_round, crt_layer, add_type, constant, constant_table, modulo=None):
        if len(constant)<(self.nbr_words + self.nbr_temp_words): constant = constant + [None]*(self.nbr_words + self.nbr_temp_words - len(constant))
        i = 0
        for j in range(self.nbr_words + self.nbr_temp_words):
            in_var = self.vars[crt_round][crt_layer][j]
            out_var = self.vars[crt_round][crt_layer+1][j]
            if constant[j]!=None:
                if add_type == 'xor':
                    self.constraints[crt_round][crt_layer].append(ConstantXOR([in_var], [out_var], constant_table, crt_round, i, ID=generateID(name,crt_round,crt_layer+1,j)))
                elif add_type == 'modadd':
                    self.constraints[crt_round][crt_layer].append(ConstantAdd([in_var], [out_var], constant_table, crt_round, i, modulo=modulo, ID=generateID(name,crt_round,crt_layer+1,j)))
                i += 1
            else:
                self.constraints[crt_round][crt_layer].append(op.Equal([in_var], [out_var], ID=generateID(name + "_EQ",crt_round,crt_layer+1,j)))

    def SingleOperatorLayer(self, name, crt_round, crt_layer, my_operator, index_in, index_out):
        flat_index_out = [idx for sub in index_out for idx in (sub if isinstance(sub, list) else [sub])]
        for j in range(self.nbr_words + self.nbr_temp_words):
            if j not in flat_index_out:
                in_var = [self.vars[crt_round][crt_layer][j]]
                out_var = [self.vars[crt_round][crt_layer+1][j]]
                self.constraints[crt_round][crt_layer].append(op.Equal(in_var, out_var, ID=generateID(name + "_EQ",crt_round,crt_layer+1,j)))
            else:
                if isinstance(index_out[0], int):
                    in_vars = [self.vars[crt_round][crt_layer][k] for k in index_in[index_out.index(j)]]
                    out_vars = [self.vars[crt_round][crt_layer+1][j]]
                    self.constraints[crt_round][crt_layer].append(my_operator(in_vars, out_vars, ID=generateID(name,crt_round,crt_layer+1,j)))
                elif isinstance(index_out[0], list):
                    for id, sub_index in enumerate(index_out):
                        if j == sub_index[0]:
                            in_vars = [self.vars[crt_round][crt_layer][k] for k in index_in[id]]
                            out_vars = [self.vars[crt_round][crt_layer + 1][i] for i in sub_index]
                            self.constraints[crt_round][crt_layer].append(my_operator(in_vars, out_vars, ID=generateID(name,crt_round,crt_layer+1,j)))

    def GF2Linear_TransLayer(self, name, crt_round, crt_layer, index_in, index_out, mat, constants=None):
        flat_index_out = [idx for sub in index_out for idx in (sub if isinstance(sub, list) else [sub])]
        for j in range(self.nbr_words + self.nbr_temp_words):
            if j not in flat_index_out:
                in_var = [self.vars[crt_round][crt_layer][j]]
                out_var = [self.vars[crt_round][crt_layer+1][j]]
                self.constraints[crt_round][crt_layer].append(op.Equal(in_var, out_var, ID=generateID(name + "_EQ",crt_round,crt_layer+1,j)))
            else:
                in_vars = [self.vars[crt_round][crt_layer][index_in[index_out.index(j)]]]
                out_vars = [self.vars[crt_round][crt_layer+1][j]]
                self.constraints[crt_round][crt_layer].append(GF2Linear_Trans(in_vars, out_vars, mat, ID=generateID(name,crt_round,crt_layer+1,j), constants=constants))

    def MatrixLayer(self, name, crt_round, crt_layer, mat, indexes_list, polynomial = None):
        m = len(mat)
        for i in mat:
            if len(i)!=m: raise Exception("MatrixLayer: matrix shape is not square")
        flat_indexes = [x for sublist in indexes_list for x in sublist]
        for j in range(self.nbr_words + self.nbr_temp_words):
            if j not in flat_indexes:
                self.constraints[crt_round][crt_layer].append(op.Equal([self.vars[crt_round][crt_layer][j]], [self.vars[crt_round][crt_layer+1][j]], ID=generateID(name + "_EQ",crt_round,crt_layer+1,j)))
        for j, indexes in enumerate(indexes_list):
            if len(indexes)!=m: raise Exception("MatrixLayer: input vector does not match matrix size")
            self.constraints[crt_round][crt_layer].append(Matrix(name, [self.vars[crt_round][crt_layer][x] for x in indexes], [self.vars[crt_round][crt_layer+1][x] for x in indexes], mat = mat, polynomial = polynomial, ID=generateID(name,crt_round,crt_layer+1,j)))

    def ExtractionLayer(self, name, crt_round, crt_layer, extraction_indexes, external_variable):
        for j, indexes in enumerate(extraction_indexes):
            in_var = external_variable[indexes]
            out_var = self.vars[crt_round][crt_layer+1][j]
            self.constraints[crt_round][crt_layer].append(op.Equal([in_var], [out_var],ID=generateID(name + "_EQ",crt_round,crt_layer+1,j)))

    def AddRoundKeyLayer(self, name, crt_round, crt_layer, my_operator, sk_function, mask = None):
        if mask is None: mask = [1]*sk_function.nbr_words
        if sum(mask)!=sk_function.nbr_words: raise Exception("AddRoundKeyLayer: subkey size does not match the mask")
        if len(mask)<(self.nbr_words + self.nbr_temp_words): mask += [0]*(self.nbr_words + self.nbr_temp_words - len(mask))
        cpt = 0
        for j in range(self.nbr_words + self.nbr_temp_words):
            in_var = self.vars[crt_round][crt_layer][j]
            out_var = self.vars[crt_round][crt_layer+1][j]
            if mask[j]==1:
                sk_var = sk_function.vars[crt_round][-1][cpt]
                self.constraints[crt_round][crt_layer].append(my_operator([in_var, sk_var], [out_var], ID=generateID(name,crt_round,crt_layer+1,j)))
                cpt = cpt + 1
            else:
                self.constraints[crt_round][crt_layer].append(op.Equal([in_var], [out_var], ID=generateID(name + "_EQ",crt_round,crt_layer+1,j)))


# ********************* PRIMITIVES ********************* #
class Primitive(ABC):
    def __init__(self, name, inputs, outputs):
        self.name = name
        self.inputs = inputs
        self.outputs = outputs
        self.functions = []
        self.inputs_constraints = []
        self.outputs_constraints = []
        self.test_vectors = []
        self.vars_dictionary = {}
        self.constraints_dictionary = {}

    def post_initialization(self, copy_operator=False):
        self.clean_graph()
        if copy_operator: self.add_copy_operators()
        self.build_dictionaries()

    def build_dictionaries(self):
        self.vars_dictionary = {}
        self.constraints_dictionary = {}
        for f in self.functions.values():
            for r in range(f.nbr_rounds+1):
                for l in range(f.nbr_layers+1):
                    for v in f.vars[r][l]:
                        self.vars_dictionary[v.ID] = v
                        for v_copy in v.copied_vars:
                            self.vars_dictionary[v_copy[0].ID] = v_copy[0]
                    for n in range(len(f.constraints[r][l])):
                        self.constraints_dictionary[f.constraints[r][l][n].ID] = f.constraints[r][l][n]
        for n in range(len(self.inputs_constraints)):
            self.constraints_dictionary[self.inputs_constraints[n].ID] = self.inputs_constraints[n]
        for n in range(len(self.outputs_constraints)):
            self.constraints_dictionary[self.outputs_constraints[n].ID] = self.outputs_constraints[n]

    def clean_graph(self):
        changed = True
        while changed:
            changed = False
            for f in self.functions.values():
                for r in range(f.nbr_rounds+1):
                    for l in range(f.nbr_layers+1):
                        for v in f.vars[r][l]:
                            if len(v.connected_vars)==1 and v.connected_vars[0][1].__class__.__name__=="Equal":
                                v_temp=v
                                while len(v_temp.connected_vars)==1 and v_temp.connected_vars[0][1].__class__.__name__=="Equal":
                                    (new_v, new_op, direction) = v_temp.connected_vars[0]
                                    v_temp.connected_vars.pop(0)
                                    index = new_v.connected_vars.index((v_temp,new_op, "in" if direction=="out" else "out"))
                                    new_v.connected_vars.pop(index)
                                    new_op.is_ghost = True
                                    v_temp = new_v
                                    changed = True
        for f in self.functions.values():
            for r in range(f.nbr_rounds+1):
                for l in range(f.nbr_layers+1):
                    for n in range(len(f.constraints[r][l])):
                        if f.constraints[r][l][n].is_ghost:
                            f.constraints[r][l][n] = op.NoneOperator(input_vars=f.constraints[r][l][n].input_vars, output_vars=f.constraints[r][l][n].output_vars, ID=generateID("NONE",r,l,n))
        for n in range(len(self.inputs_constraints)):
            if self.inputs_constraints[n].is_ghost:
                self.inputs_constraints[n] = op.NoneOperator(input_vars=self.inputs_constraints[n].input_vars, output_vars=self.inputs_constraints[n].output_vars, ID="NONE_INPUT_" + str(n))
        for n in range(len(self.outputs_constraints)):
            if self.outputs_constraints[n].is_ghost:
                self.outputs_constraints[n] = op.NoneOperator(input_vars=self.outputs_constraints[n].input_vars, output_vars=self.outputs_constraints[n].output_vars, ID="NONE_OUTPUT_" + str(n))

    def add_copy_operators(self, functions_list=None):
        if functions_list is None:
            functions_list = self.functions.values()
        for f in functions_list:
            for r in range(f.nbr_rounds+1):
                for l in range(f.nbr_layers+1):
                    for v in f.vars[r][l]:
                        connected_vars_with_unique_operator = []
                        added_operators = []
                        for (vv,opop,direction) in v.connected_vars:
                            if direction=='in':
                                if opop not in added_operators:
                                    added_operators.append(opop)
                                    connected_vars_with_unique_operator.append((vv,opop,direction))
                        if len(connected_vars_with_unique_operator)>1:
                            for i in range(1,len(connected_vars_with_unique_operator)):
                                if connected_vars_with_unique_operator[i][1].__class__.__name__=="Equal":
                                    connected_vars_with_unique_operator[0], connected_vars_with_unique_operator[i] = connected_vars_with_unique_operator[i], connected_vars_with_unique_operator[0]
                                    break
                            v_new = [var.Variable(v.bitsize, ID=v.ID + "_COPY_" + str(i), copyorigin=v) for i in range(len(connected_vars_with_unique_operator))]
                            op_new = op.CopyOperator([v], v_new, ID= "COPYOPERATOR_" + v.ID)
                            f.constraints[r][l].append(op_new)
                            for i in range(len(connected_vars_with_unique_operator)):
                                v.copied_vars.append((v_new[i], connected_vars_with_unique_operator[i][1], op_new))
                            for i in range(len(connected_vars_with_unique_operator)):
                                (vv, opop, direction) = connected_vars_with_unique_operator[i]
                                for v_index in range(len(opop.input_vars)):
                                    if opop.input_vars[v_index]==v: opop.input_vars[v_index] = v_new[i]
                                index = vv.connected_vars.index((v, opop, "out"))
                                vv.connected_vars.pop(index)
                                index = v.connected_vars.index((vv, opop, "in"))
                                v.connected_vars.pop(index)
                                vv.connected_vars.append((v_new[i], opop, "out"))
                                v_new[i].connected_vars.append((vv, opop, "in"))


class Function(Primitive):
    def __init__(self, name, s_input, s_output, nbr_rounds, config):
        super().__init__(name, {"IN_":s_input}, {"OUT_":s_output})
        nbr_layers, nbr_words_input, nbr_words_output, nbr_temp_words, word_bitsize = config[0], config[1], config[2], config[3], config[4]
        self.nbr_rounds = nbr_rounds
        self.functions = {"FUNCTION": Layered_Function("FUNCTION", "", nbr_rounds, nbr_layers, max(nbr_words_input, nbr_words_output), nbr_temp_words, word_bitsize)}
        self.functions_implementation_order = ["FUNCTION"]
        self.functions_display_order = ["FUNCTION"]
        if len(s_input)!=nbr_words_input: raise Exception("Function: the number of input words does not match the number of input words in function")
        for i in range(len(s_input)): self.inputs_constraints.append(op.Equal([s_input[i]], [self.functions["FUNCTION"].vars[1][0][i]], ID='IN_LINK_EQ_'+str(i)))
        if len(s_output)!=nbr_words_output: raise Exception("Function: the number of output words does not match the number of output words in function")
        for i in range(len(s_output)): self.outputs_constraints.append(op.Equal([self.functions["FUNCTION"].vars[nbr_rounds][nbr_layers][i]], [s_output[i]], ID='OUT_LINK_EQ_'+str(i)))


class Permutation(Primitive):
    def __init__(self, name, s_input, s_output, nbr_rounds, config):
        super().__init__(name, {"IN_":s_input}, {"OUT_":s_output})
        nbr_layers, nbr_words, nbr_temp_words, word_bitsize = config[0], config[1], config[2], config[3]
        self.nbr_rounds = nbr_rounds
        self.functions = {"PERMUTATION": Layered_Function("PERMUTATION", "", nbr_rounds, nbr_layers, nbr_words, nbr_temp_words, word_bitsize)}
        self.functions_implementation_order = ["PERMUTATION"]
        self.functions_display_order = ["PERMUTATION"]
        if len(s_input)!=nbr_words: raise Exception("Permutation: the number of input words does not match the number of words in function")
        for i in range(len(s_input)): self.inputs_constraints.append(op.Equal([s_input[i]], [self.functions["PERMUTATION"].vars[1][0][i]], ID='IN_LINK_EQ_'+str(i)))
        if len(s_output)!=nbr_words: raise Exception("Permutation: the number of output words does not match the number of words in function")
        for i in range(len(s_output)): self.outputs_constraints.append(op.Equal([self.functions["PERMUTATION"].vars[nbr_rounds][nbr_layers][i]], [s_output[i]], ID='OUT_LINK_EQ_'+str(i)))


class Block_cipher(Primitive):
    def __init__(self, name, p_input, k_input, c_output, nbr_rounds, k_nbr_rounds, s_config, k_config, sk_config):
        super().__init__(name, {"plaintext":p_input, "key":k_input}, {"ciphertext":c_output})
        s_nbr_layers, s_nbr_words, s_nbr_temp_words, s_word_bitsize = s_config[0], s_config[1], s_config[2], s_config[3]
        k_nbr_layers, k_nbr_words, k_nbr_temp_words, k_word_bitsize = k_config[0], k_config[1], k_config[2], k_config[3]
        sk_nbr_layers, sk_nbr_words, sk_nbr_temp_words, sk_word_bitsize = sk_config[0], sk_config[1], sk_config[2], sk_config[3]
        self.nbr_rounds = nbr_rounds
        self.functions = {"PERMUTATION": Layered_Function("PERMUTATION", 's', nbr_rounds, s_nbr_layers, s_nbr_words, s_nbr_temp_words, s_word_bitsize), "KEY_SCHEDULE": Layered_Function("KEY_SCHEDULE", 'k', k_nbr_rounds, k_nbr_layers, k_nbr_words, k_nbr_temp_words, k_word_bitsize), "SUBKEYS": Layered_Function("SUBKEYS", 'sk', nbr_rounds, sk_nbr_layers, sk_nbr_words, sk_nbr_temp_words, sk_word_bitsize)}
        self.functions_implementation_order = ["SUBKEYS", "KEY_SCHEDULE", "PERMUTATION"]
        self.functions_display_order = ["PERMUTATION", "KEY_SCHEDULE", "SUBKEYS"]
        if (len(k_input)!=k_nbr_words) or (len(p_input)!=s_nbr_words): raise Exception("Block_cipher: the number of input plaintext/key words does not match the number of plaintext/key words in function")
        if len(p_input)!=s_nbr_words: raise Exception("Block_cipher: the number of plaintext words does not match the number of words in the permutation")
        for i in range(len(p_input)): self.inputs_constraints.append(op.Equal([p_input[i]], [self.functions["PERMUTATION"].vars[1][0][i]], ID='IN_LINK_P_EQ_'+str(i)))
        if len(k_input)!=k_nbr_words: raise Exception("Block_cipher: the number of key words does not match the number of words in the")
        for i in range(len(k_input)): self.inputs_constraints.append(op.Equal([k_input[i]], [self.functions["KEY_SCHEDULE"].vars[1][0][i]], ID='IN_LINK_K_EQ_'+str(i)))
        if len(c_output)!=s_nbr_words: raise Exception("Block_cipher: the number of ciphertext words does not match the number of words in the permutation")
        for i in range(len(c_output)): self.outputs_constraints.append(op.Equal([self.functions["PERMUTATION"].vars[nbr_rounds][s_nbr_layers][i]], [c_output[i]], ID='OUT_LINK_C_EQ_'+str(i)))


class Stream_cipher(Primitive):
    def __init__(self, name, iv_input, k_input, keystream_output, nbr_rounds_init, nbr_rounds_update, nbr_rounds_keystream, init_config, update_config, keystream_config):
        super().__init__(name, {"IV":iv_input, "key":k_input}, {"keystream":keystream_output})
        init_nbr_layers, init_nbr_words, init_nbr_temp_words, init_word_bitsize = init_config[0], init_config[1], init_config[2], init_config[3]
        update_nbr_layers, update_nbr_words, update_nbr_temp_words, update_word_bitsize = update_config[0], update_config[1], update_config[2], update_config[3]
        keystream_nbr_layers, keystream_nbr_words, keystream_nbr_temp_words, keystream_word_bitsize = keystream_config[0], keystream_config[1], keystream_config[2], keystream_config[3]
        self.nbr_rounds_init = nbr_rounds_init
        self.nbr_rounds_update = nbr_rounds_update
        self.nbr_rounds_keystream = nbr_rounds_keystream
        self.functions = {"INITIALIZATION": Layered_Function("INITIALIZATION", 'init', nbr_rounds_init, init_nbr_layers, init_nbr_words, init_nbr_temp_words, init_word_bitsize), "STATE_UPDATE": Layered_Function("STATE_UPDATE", 'upd', nbr_rounds_update, update_nbr_layers, update_nbr_words, update_nbr_temp_words, update_word_bitsize), "KEYSTREAM_GEN": Layered_Function("KEYSTREAM_GEN", 'ks', nbr_rounds_keystream, keystream_nbr_layers, keystream_nbr_words, keystream_nbr_temp_words, keystream_word_bitsize)}
        self.functions_implementation_order = ["INITIALIZATION", "STATE_UPDATE", "KEYSTREAM_GEN"]
        self.functions_display_order = ["INITIALIZATION", "STATE_UPDATE", "KEYSTREAM_GEN"]
        if (len(iv_input)!=init_nbr_words) or (len(k_input)!=init_nbr_words): raise Exception("Stream_cipher: the number of input IV/key words does not match the number of IV/key words in initialization function")
        if len(iv_input)!=init_nbr_words: raise Exception("Stream_cipher: the number of IV words does not match the number of words in the initialization function")
        for i in range(len(iv_input)): self.inputs_constraints.append(op.Equal([iv_input[i]], [self.functions["INITIALIZATION"].vars[1][0][i]], ID='IN_LINK_IV_EQ_'+str(i)))
        if len(k_input)!=init_nbr_words: raise Exception("Stream_cipher: the number of key words does not match the number of words in the initialization function")
        for i in range(len(k_input)): self.inputs_constraints.append(op.Equal([k_input[i]], [self.functions["INITIALIZATION"].vars[1][0][i + init_nbr_words]], ID='IN_LINK_K_EQ_'+str(i)))
        if len(keystream_output)!=keystream_nbr_words: raise Exception("Stream_cipher: the number of keystream words does not match the number of words in the keystream generation function")
        for i in range(len(keystream_output)): self.outputs_constraints.append(op.Equal([self.functions["KEYSTREAM_GEN"].vars[nbr_rounds_keystream][keystream_nbr_layers][i]], [keystream_output[i]], ID='OUT_LINK_KS_EQ_'+str(i)))
