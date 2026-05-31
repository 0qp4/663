import math
import os
from pathlib import Path
from operators.operators import Operator, RaiseExceptionVersionNotExisting
from tools.model_constraints import generate_and_save_constraints, gen_constraints_obj_func_from_template

ROOT = Path(__file__).resolve().parents[1]
BASE_PATH = ROOT / "files/sbox_modeling"
BASE_PATH.mkdir(parents=True, exist_ok=True)


class Sbox(Operator):
    def __init__(self, input_vars, output_vars, input_bitsize, output_bitsize, ID=None):
        super().__init__(input_vars, output_vars, ID=ID)
        self.input_bitsize = input_bitsize
        self.output_bitsize = output_bitsize
        self.table = None
        self.table_inv = None
        self.ddt = None
        self.lat = None

    def computeDDT(self):
        if self.ddt is not None:
            return self.ddt
        ddt = [[0] * (2**self.output_bitsize) for _ in range(2**self.input_bitsize)]
        for in_diff in range(2**self.input_bitsize):
            for j in range(2**self.input_bitsize):
                out_diff = self.table[j] ^ self.table[j ^ in_diff]
                ddt[in_diff][out_diff] += 1
        self.ddt = ddt
        return ddt

    def computeLAT(self):
        if self.lat is not None:
            return self.lat
        lat = [[0] * 2**self.output_bitsize for _ in range(2**self.input_bitsize)]
        for a in range(2**self.input_bitsize):
            for b in range(2**self.output_bitsize):
                acc = 0
                for x in range(2**self.input_bitsize):
                    ax = bin(a & x).count("1") & 1
                    bs = bin(b & self.table[x]).count("1") & 1
                    acc += 1 if (ax ^ bs) == 0 else -1
                lat[a][b] = acc
        self.lat = lat
        return lat

    def differential_branch_number(self):
        ret = (1 << self.input_bitsize) + (1 << self.output_bitsize)
        for a in range(1 << self.input_bitsize):
            for b in range(1 << self.input_bitsize):
                if a != b:
                    x = a ^ b
                    y = self.table[a] ^ self.table[b]
                    w = bin(x).count('1') + bin(y).count('1')
                    if w < ret:
                        ret = w
        return ret

    def linear_branch_number(self):
        m, n = self.input_bitsize, self.output_bitsize
        lat = self.computeLAT()
        ret = (1 << m) + (1 << n)
        for a in range(1 << m):
            for b in range(1, 1 << n):
                if lat[a][b] != 0:
                    w = bin(a).count("1") + bin(b).count("1")
                    if w < ret:
                        ret = w
        return ret

    def is_bijective(self):
        return len(set(self.table)) == len(self.table) and all(i in self.table for i in range(len(self.table)))

    def star_ddt_to_truthtable(self):
        ddt = self.computeDDT()
        ttable = ''
        for n in range(2**(self.input_bitsize + self.output_bitsize)):
            dx = n >> self.output_bitsize
            dy = n & ((1 << self.output_bitsize) - 1)
            if ddt[dx][dy] > 0:
                ttable += '1'
            else:
                ttable += '0'
        return ttable

    def pddt_to_truthtable(self, p):
        ddt = self.computeDDT()
        ttable = ''
        for n in range(2**(self.input_bitsize + self.output_bitsize)):
            dx = n >> self.output_bitsize
            dy = n & ((1 << self.output_bitsize) - 1)
            if ddt[dx][dy] == p:
                ttable += '1'
            else:
                ttable += '0'
        return ttable

    def ddt_to_truthtable_milp(self):
        ddt = self.computeDDT()
        ttable = ''
        diff_weights = self.gen_weights(ddt)
        len_diff_weights = len(diff_weights)
        for n in range(2**(self.input_bitsize + self.output_bitsize + len_diff_weights)):
            dx = n >> (self.output_bitsize + len_diff_weights)
            dy = (n >> len_diff_weights) & ((1 << self.output_bitsize) - 1)
            if ddt[dx][dy] > 0:
                p = bin(n & ((1 << len_diff_weights) - 1))[2:].zfill(len_diff_weights)
                w = 0
                for i in range(len_diff_weights):
                    w += diff_weights[i] * int(p[i])
                if abs(float(math.log(ddt[dx][dy] / (2**self.input_bitsize), 2))) == w:
                    ttable += '1'
                else:
                    ttable += '0'
            else:
                ttable += '0'
        return ttable

    def ddt_to_truthtable_sat(self):
        ddt = self.computeDDT()
        ttable = ''
        integers_weight, floats_weight = self.gen_integer_float_weight(ddt)
        len_diff_weights = int(max(integers_weight) + len(floats_weight))
        for n in range(2**(self.input_bitsize + self.output_bitsize + len_diff_weights)):
            dx = n >> (self.output_bitsize + len_diff_weights)
            dy = (n >> len_diff_weights) & ((1 << self.output_bitsize) - 1)
            if ddt[dx][dy] > 0:
                p = tuple(int(x) for x in bin(n & ((1 << len_diff_weights) - 1))[2:].zfill(len_diff_weights))
                w = abs(float(math.log(ddt[dx][dy] / (2**self.input_bitsize), 2)))
                pattern = self.gen_weight_pattern_sat(integers_weight, floats_weight, w)
                if p == tuple(pattern):
                    ttable += '1'
                else:
                    ttable += '0'
            else:
                ttable += '0'
        return ttable

    def star_lat_to_truthtable(self):
        lat = self.computeLAT()
        ttable = ''
        for n in range(2**(self.input_bitsize + self.output_bitsize)):
            lx = n >> self.output_bitsize
            ly = n & ((1 << self.output_bitsize) - 1)
            if lat[lx][ly] != 0:
                ttable += '1'
            else:
                ttable += '0'
        return ttable

    def plat_to_truthtable(self, p):
        lat = self.computeLAT()
        ttable = ''
        for n in range(2**(self.input_bitsize + self.output_bitsize)):
            lx = n >> self.output_bitsize
            ly = n & ((1 << self.output_bitsize) - 1)
            if lat[lx][ly] == p or lat[lx][ly] == -p:
                ttable += '1'
            else:
                ttable += '0'
        return ttable

    def lat_to_truthtable_milp(self):
        lat = self.computeLAT()
        ttable = ''
        linear_weights = self.gen_weights(lat)
        len_linear_weights = len(linear_weights)
        for n in range(2**(self.input_bitsize + self.output_bitsize + len_linear_weights)):
            lx = n >> (self.output_bitsize + len_linear_weights)
            ly = (n >> len_linear_weights) & ((1 << self.output_bitsize) - 1)
            if lat[lx][ly] != 0:
                p = bin(n & ((1 << len_linear_weights) - 1))[2:].zfill(len_linear_weights)
                w = 0
                for i in range(len_linear_weights):
                    w += linear_weights[i] * int(p[i])
                if abs(float(math.log(abs(lat[lx][ly]) / (2**self.input_bitsize), 2))) == w:
                    ttable += '1'
                else:
                    ttable += '0'
            else:
                ttable += '0'
        return ttable

    def lat_to_truthtable_sat(self):
        lat = self.computeLAT()
        ttable = ''
        integers_weight, floats_weight = self.gen_integer_float_weight(lat)
        len_linear_weights = int(max(integers_weight) + len(floats_weight))
        for n in range(2**(self.input_bitsize + self.output_bitsize + len_linear_weights)):
            lx = n >> (self.output_bitsize + len_linear_weights)
            ly = (n >> len_linear_weights) & ((1 << self.output_bitsize) - 1)
            if lat[lx][ly] != 0:
                p = tuple(int(x) for x in bin(n & ((1 << len_linear_weights) - 1))[2:].zfill(len_linear_weights))
                w = abs(float(math.log(abs(lat[lx][ly]) / (2**self.input_bitsize), 2)))
                pattern = self.gen_weight_pattern_sat(integers_weight, floats_weight, w)
                if p == tuple(pattern):
                    ttable += '1'
                else:
                    ttable += '0'
            else:
                ttable += '0'
        return ttable

    def gen_spectrum(self, table):
        spectrum = sorted(list(set([abs(table[i][j]) for i in range(2**self.input_bitsize) for j in range(2**self.output_bitsize)]) - {0, 2**self.input_bitsize}))
        return spectrum

    def gen_weights(self, table):
        spectrum = self.gen_spectrum(table)
        weights = [abs(float(math.log(i / (2**self.input_bitsize), 2))) for i in spectrum]
        return weights

    def gen_integer_float_weight(self, table):
        weights = self.gen_weights(table)
        integers = sorted(set([int(x) for x in weights]))
        floats = sorted(set([x - int(x) for x in weights if x != int(x)]))
        return integers, floats

    def gen_weight_pattern_sat(self, integers_weight, floats_weight, w):
        int_w = int(w)
        float_w = w - int_w
        return [0] * (max(integers_weight) - int_w) + [1] * int_w + [1 if f == float_w else 0 for f in floats_weight]

    def generate_implementation(self, implementation_type='python', unroll=False):
        if implementation_type == 'python':
            if len(self.input_vars) == 1 and len(self.output_vars) == 1:
                return [self.get_var_ID('out', 0, unroll) + ' = ' + str(self.__class__.__name__) + '[' + self.get_var_ID('in', 0, unroll) + ']']
            elif len(self.input_vars) > 1 and len(self.output_vars) > 1:
                x_bits = len(self.input_vars)
                x_expr = 'x = ' + ' | '.join(f'({self.get_var_ID("in", i, unroll=unroll)} << {x_bits - 1 - i})' for i in range(x_bits))
                model_list = [x_expr]
                model_list.append(f'y = {self.__class__.__name__}[x]')
                y_vars = ', '.join(f'{self.get_var_ID("out", i, unroll=unroll)}' for i in range(x_bits))
                y_bits = ', '.join(f'(y >> {x_bits - 1 - i}) & 1' for i in range(x_bits))
                model_list.append(f'{y_vars} = {y_bits}')
                return model_list
            else:
                raise Exception(str(self.__class__.__name__) + ": unsupported number of input/output variables for 'python' implementation")
        elif implementation_type == 'c':
            if len(self.input_vars) == 1 and len(self.output_vars) == 1:
                return [self.get_var_ID('out', 0, unroll) + ' = ' + str(self.__class__.__name__) + '[' + self.get_var_ID('in', 0, unroll) + '];']
            elif len(self.input_vars) > 1 and len(self.output_vars) > 1:
                x_bits = len(self.input_vars)
                x_expr = 'x = ' + ' | '.join(f'({self.get_var_ID("in", i, unroll=unroll)} << {x_bits - 1 - i})' for i in range(x_bits)) + ";"
                model_list = [x_expr]
                model_list.append(f'y = {str(self.__class__.__name__)}[x];')
                for i in range(x_bits):
                    y_vars = self.get_var_ID("out", i, unroll=unroll)
                    y_bits = f'(y >> {x_bits - 1 - i}) & 1'
                    model_list.append(f'{y_vars} = {y_bits};')
                return model_list
            else:
                raise Exception(str(self.__class__.__name__) + ": unsupported number of input/output variables for 'c' implementation")
        else:
            raise Exception(str(self.__class__.__name__) + ": unknown implementation type '" + implementation_type + "'")

    def get_header_ID(self):
        return [self.__class__.__name__, self.model_version, self.input_bitsize, self.output_bitsize, self.table]

    def generate_implementation_header(self, implementation_type='python'):
        if implementation_type == 'python':
            return [str(self.__class__.__name__) + ' = ' + str(self.table)]
        elif implementation_type == 'c':
            if self.input_bitsize <= 8:
                if len(self.input_vars) > 1 and len(self.output_vars) > 1:
                    return ['uint8_t ' + str(self.__class__.__name__) + '[' + str(2**self.input_bitsize) + '] = {' + str(self.table)[1:-1] + '};'] + ['uint8_t ' + 'x;'] + ['uint8_t ' + 'y;']
                else:
                    return ['uint8_t ' + str(self.__class__.__name__) + '[' + str(2**self.input_bitsize) + '] = {' + str(self.table)[1:-1] + '};']
            else:
                if len(self.input_vars) > 1 and len(self.output_vars) > 1:
                    return ['uint32_t ' + str(self.__class__.__name__) + '[' + str(2**self.input_bitsize) + '] = {' + str(self.table)[1:-1] + '};'] + ['uint32_t ' + 'x;'] + ['uint32_t ' + 'y;']
                else:
                    return ['uint32_t ' + str(self.__class__.__name__) + '[' + str(2**self.input_bitsize) + '] = {' + str(self.table)[1:-1] + '};']
        else:
            return None

    def generate_model(self, model_type='sat', tool_type="minimize_logic", mode=0, filename_load=True):
        self.model_filename = str(BASE_PATH / f"constraints_{model_type}_{self.model_version}_{tool_type}_{mode}.txt")
        self.filename_load = filename_load
        if self.model_version in [self.__class__.__name__ + "_XORDIFF_PR", self.__class__.__name__ + "_LINEAR_PR"]:
            return self._generate_model_diff_linear_pr(model_type, tool_type, mode)
        elif self.model_version in [self.__class__.__name__ + "_XORDIFF", self.__class__.__name__ + "_XORDIFF_A", self.__class__.__name__ + "_LINEAR", self.__class__.__name__ + "_LINEAR_A"]:
            return self._generate_model_diff_linear(model_type, tool_type, mode)
        elif self.model_version in [self.__class__.__name__ + "_XORDIFF_P", self.__class__.__name__ + "_LINEAR_P"]:
            return self._generate_model_diff_linear_p(model_type, tool_type, mode)
        elif self.model_version in [self.__class__.__name__ + "_TRUNCATEDDIFF", self.__class__.__name__ + "_TRUNCATEDDIFF_A", self.__class__.__name__ + "_TRUNCATEDLINEAR", self.__class__.__name__ + "_TRUNCATEDLINEAR_A"] and (not isinstance(self.input_vars[0], list)):
            return self._generate_model_diff_linear_word_truncated(model_type)
        else:
            RaiseExceptionVersionNotExisting(str(self.__class__.__name__), self.model_version, model_type)

    def _generate_model_diff_linear_pr(self, model_type, tool_type, mode):
        var_in, var_out = [], []
        for i in range(len(self.input_vars)):
            var_in += self.get_var_model("in", i)
        for i in range(len(self.output_vars)):
            var_out += self.get_var_model("out", i)

        if self.model_version in [self.__class__.__name__ + "_XORDIFF_PR"]:
            table = self.computeDDT()
        elif self.model_version in [self.__class__.__name__ + "_LINEAR_PR"]:
            table = self.computeLAT()
        else:
            RaiseExceptionVersionNotExisting(str(self.__class__.__name__), self.model_version, model_type)

        if model_type == "sat":
            integers_weight, floats_weight = self.gen_integer_float_weight(table)
            var_p = [f"{self.ID}_p{i}" for i in range(max(integers_weight) + len(floats_weight))]
            pr_variables = [f"p{i}" for i in range(len(var_p))]
            objective_fun = " + ".join(pr_variables[:max(integers_weight)])
            if floats_weight:
                objective_fun += " + " + " + ".join(f"{w:.4f} {v}" for w, v in zip(floats_weight, pr_variables[max(integers_weight):]))
        elif model_type == "milp":
            weights = self.gen_weights(table)
            var_p = [f"{self.ID}_p{i}" for i in range(len(weights))]
            pr_variables = [f"p{i}" for i in range(len(var_p))]
            objective_fun = " + ".join(f"{w:.4f} {v}" for w, v in zip(weights, pr_variables))
        else:
            RaiseExceptionVersionNotExisting(str(self.__class__.__name__), self.model_version, model_type)

        if self.filename_load and os.path.exists(self.model_filename):
            model_list, obj_fun = gen_constraints_obj_func_from_template(self.model_filename, var_in, var_out, var_p)
        else:
            if model_type == "sat" and self.model_version in [self.__class__.__name__ + "_XORDIFF_PR"]:
                ttable = self.ddt_to_truthtable_sat()
            elif model_type == "sat" and self.model_version in [self.__class__.__name__ + "_LINEAR_PR"]:
                ttable = self.lat_to_truthtable_sat()
            elif model_type == "milp" and self.model_version in [self.__class__.__name__ + "_XORDIFF_PR"]:
                ttable = self.ddt_to_truthtable_milp()
            elif model_type == "milp" and self.model_version in [self.__class__.__name__ + "_LINEAR_PR"]:
                ttable = self.lat_to_truthtable_milp()
            else:
                RaiseExceptionVersionNotExisting(str(self.__class__.__name__), self.model_version, model_type)

            input_variables = [f"a{i}" for i in range(len(var_in))]
            output_variables = [f"b{i}" for i in range(len(var_out))]
            generate_and_save_constraints(model_type, tool_type, mode, ttable, input_variables, output_variables, pr_variables, objective_fun=objective_fun, model_filename=self.model_filename)
            model_list, obj_fun = gen_constraints_obj_func_from_template(self.model_filename, var_in, var_out, var_p)
        self.weight = [obj_fun]
        return model_list

    def _generate_model_diff_linear(self, model_type, tool_type, mode):
        if self.model_version in [self.__class__.__name__ + "_XORDIFF_A", self.__class__.__name__ + "_LINEAR_A"]:
            self.model_filename = str(BASE_PATH / f"constraints_{model_type}_{self.model_version.replace('_A', '')}_{tool_type}_{mode}.txt")

        var_in, var_out = [], []
        for i in range(len(self.input_vars)):
            var_in += self.get_var_model("in", i)
        for i in range(len(self.output_vars)):
            var_out += self.get_var_model("out", i)

        if self.filename_load and os.path.exists(self.model_filename):
            model_list, _ = gen_constraints_obj_func_from_template(self.model_filename, var_in, var_out)
        else:
            if self.model_version in [self.__class__.__name__ + "_XORDIFF", self.__class__.__name__ + "_XORDIFF_A"]:
                ttable = self.star_ddt_to_truthtable()
            elif self.model_version in [self.__class__.__name__ + "_LINEAR", self.__class__.__name__ + "_LINEAR_A"]:
                ttable = self.star_lat_to_truthtable()
            else:
                RaiseExceptionVersionNotExisting(str(self.__class__.__name__), self.model_version, model_type)
            input_variables = [f"a{i}" for i in range(len(var_in))]
            output_variables = [f"b{i}" for i in range(len(var_out))]
            generate_and_save_constraints(model_type, tool_type, mode, ttable, input_variables, output_variables, model_filename=self.model_filename)
            model_list, _ = gen_constraints_obj_func_from_template(self.model_filename, var_in, var_out)

        if self.model_version in [self.__class__.__name__ + "_XORDIFF_A", self.__class__.__name__ + "_LINEAR_A"]:
            var_At = [self.ID + '_At']
            if model_type == "sat":
                model_list += [f"-{var} {var_At[0]}" for var in var_in] + [" ".join(var_in) + ' -' + var_At[0]]
            elif model_type == "milp":
                model_list += [f"{var_At[0]} - {var_in[i]} >= 0" for i in range(len(var_in))] + [" + ".join(var_in) + ' - ' + var_At[0] + ' >= 0']
                model_list.append('Binary\n' + ' '.join(v for v in var_At))
            self.weight = var_At

        return model_list

    def _generate_model_diff_linear_p(self, model_type, tool_type, mode):
        model_list = []

        var_in, var_out = [], []
        for i in range(len(self.input_vars)):
            var_in += self.get_var_model("in", i)
        for i in range(len(self.output_vars)):
            var_out += self.get_var_model("out", i)

        if self.model_version in [self.__class__.__name__ + "_XORDIFF_P"]:
            table = self.computeDDT()
        elif self.model_version in [self.__class__.__name__ + "_LINEAR_P"]:
            table = self.computeLAT()
        else:
            RaiseExceptionVersionNotExisting(str(self.__class__.__name__), self.model_version, model_type)

        spectrum = self.gen_spectrum(table) + [2**self.input_bitsize]
        var_p = [f"{self.ID}_p{w}" for w in spectrum]
        model_v = self.model_version
        weight = ''

        for i in range(len(spectrum)):
            self.model_version = model_v + str(spectrum[i])
            self.model_filename = str(BASE_PATH / f"constraints_{model_type}_{self.model_version}_{tool_type}_{mode}.txt")

            if self.filename_load and os.path.exists(self.model_filename):
                sbox_inequalities, _ = gen_constraints_obj_func_from_template(self.model_filename, var_in, var_out)
            else:
                if "XORDIFF" in self.model_version:
                    ttable = self.pddt_to_truthtable(spectrum[i])
                elif "LINEAR" in self.model_version:
                    ttable = self.plat_to_truthtable(spectrum[i])
                else:
                    RaiseExceptionVersionNotExisting(str(self.__class__.__name__), self.model_version, model_type)
                input_variables = [f"a{i}" for i in range(len(var_in))]
                output_variables = [f"b{i}" for i in range(len(var_out))]
                generate_and_save_constraints(model_type, tool_type, mode, ttable, input_variables, output_variables, model_filename=self.model_filename)
                sbox_inequalities, _ = gen_constraints_obj_func_from_template(self.model_filename, var_in, var_out)

            for ineq in sbox_inequalities:
                temp = ineq
                if ">=" in temp:
                    temp_0, temp_1 = temp.split(">=")[0], int(temp.split(" >= ")[1])
                    temp = temp_0 + f"- 10000 {var_p[i]} >= {temp_1 - 10000}"
                model_list += [temp]
            weight += " + " + "{:0.04f} ".format(abs(float(math.log(spectrum[i] / (2**self.input_bitsize), 2)))) + var_p[i]
        weight = weight[3:]
        model_list += [' + '.join(var_p) + ' = 1\n']
        model_list.append('Binary\n' + ' '.join(v for v in var_p))
        self.weight = [weight]
        return model_list

    def _generate_model_diff_linear_word_truncated(self, model_type):
        var_in, var_out = (self.get_var_model("in", 0, bitwise=False), self.get_var_model("out", 0, bitwise=False))

        if model_type == "sat":
            model_list = [f"-{var_in[0]} {var_out[0]}", f"{var_in[0]} -{var_out[0]}"]
        elif model_type == "milp":
            model_list = [f'{var_in[0]} - {var_out[0]} = 0']
            model_list.append('Binary\n' + ' '.join(v for v in var_in + var_out))
        else:
            RaiseExceptionVersionNotExisting(str(self.__class__.__name__), self.model_version, model_type)

        if self.model_version in [self.__class__.__name__ + "_TRUNCATEDDIFF_A", self.__class__.__name__ + "_TRUNCATEDLINEAR_A"]:
            self.weight = var_in

        return model_list


class RECTANGLE_Sbox(Sbox):
    def __init__(self, input_vars, output_vars, ID=None):
        super().__init__(input_vars, output_vars, 4, 4, ID=ID)
        self.table = [0x6, 0x5, 0xC, 0xA, 0x1, 0xE, 0x7, 0x9,
                      0xB, 0x0, 0x3, 0xD, 0x8, 0xF, 0x4, 0x2]
        self.table_inv = [0x9, 0x4, 0xF, 0xA, 0xE, 0x1, 0x0, 0x6,
                          0xC, 0x7, 0x3, 0x8, 0x2, 0xB, 0x5, 0xD]
