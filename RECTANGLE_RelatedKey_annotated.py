"""
================================================================================
RECTANGLE 分组密码 - 相关密钥差分分析 SAT 求解程序
================================================================================

功能说明:
    本程序使用 SAT (布尔可满足性问题) 求解器来搜索 RECTANGLE 分组密码
    在相关密钥场景下的最优差分特征。通过将密码的差分传播约束转化为
    CNF (合取范式) 子句，然后使用 SAT 求解器进行求解。

算法概述:
    1. 使用 MILP (混合整数线性规划) 模型计算每个位置的活跃 S 盒上下界
    2. 将密码的轮函数、密钥扩展和轮密钥加操作转化为 CNF 约束
    3. 使用顺序编码 (Sequential Encoding) 约束活跃 S 盒的总数
    4. 调用 CaDiCaL SAT 求解器求解
    5. 通过二分搜索找到最优差分特征

作者: [原作者]
注释添加: Qingyan Agent
================================================================================
"""

from gurobipy import *       # Gurobi 优化器，用于计算上下界
from functools import partial # 用于部分函数应用
from itertools import repeat  # 迭代工具
from multiprocessing import Pool, freeze_support  # 多进程并行计算
import os
import time
import random
import math

# ==================== 全局配置参数 ====================

FullRound = 25          # RECTANGLE 密码的完整轮数

SearchRoundStart = 1    # 搜索起始轮数
SearchRoundEnd = FullRound  # 搜索结束轮数

# 概率界限数组，存储每轮的最优差分概率（以 -log2 形式表示）
# ProbabilityBound[i] 表示 i 轮的最优差分特征概率
ProbabilityBound = list([])
for i in range(FullRound + 1):
    ProbabilityBound += [0]


# ==================== 结果提取函数 ====================

def ExtractionResults(File):
    """
    从 SAT 求解器输出文件中提取求解结果
    
    参数:
        File: SAT 求解器输出文件路径
        
    返回:
        Result: 求解状态 ("SATISFIABLE" 或 "UNSATISFIABLE" 或 "NoResult")
        Results: 如果可满足，返回变量赋值列表；否则返回空字符串
        
    说明:
        SAT 求解器输出格式:
        - "c ..." 开头的行为注释
        - "s SATISFIABLE" 或 "s UNSATISFIABLE" 表示求解状态
        - "v ..." 开头的行为变量赋值
    """
    Result = "NoResult"
    Results = ""
    file = open(File, "rb")  # 以二进制模式打开文件

    StopResult = 1    # 控制循环是否继续
    StartResult = 0   # 标记是否开始读取结果

    while StopResult:
        result = str(file.readline())  # 逐行读取
        if "[ result ]" in result:
            StartResult = 1
            continue
        if "run-time profiling" in result:
            StopResult = 0
            break
        
        if StartResult == 1:
            if "SATISFIABLE" in result:
                Result = "SATISFIABLE"
            if "UNSATISFIABLE" in result:
                Result = "UNSATISFIABLE"
                break 
            Results += result
        
    # 如果是可满足的，解析变量赋值
    if Result == "SATISFIABLE":
        # 清理字符串中的各种格式字符
        Results = Results.replace("b'", "")
        Results = Results.replace(" '", "")
        Results = Results.replace("'", "")
        Results = Results.replace("c ", "")
        Results = Results.replace("v", "")
        Results = Results.replace("s ", "")
        Results = Results.replace("SATISFIABLE", "")
        Results = Results.replace("UNSATISFIABLE ", "")
        Results = Results.replace("\\n", "")
        Results = Results.replace("\\r", "")

        Results = Results.split(" ")  # 按空格分割
        del Results[0]                # 删除第一个空元素
        del Results[len(Results) - 1]  # 删除最后一个空元素

        for i in range(len(Results)):
            Results[i] = int(Results[i], 10)  # 转换为整数
            
    return (Result, Results)


# ==================== 变量生成函数 ====================

def GenerateAndCountVariables(Round, objLowerBound, objUpperBound):
    """
    生成并计数 SAT 模型中的所有变量
    
    参数:
        Round: 当前分析的轮数
        objLowerBound: 每个位置的活跃 S 盒下界列表
        objUpperBound: 每个位置的活跃 S 盒上界列表
        
    返回:
        xin: 输入状态变量矩阵 [Round][64]
        xout: 输出状态变量矩阵 [Round][64]
        p, q, m: S 盒辅助变量矩阵 [Round][16]
        auxiliary_var_u: 顺序编码辅助变量
        count_var_num: 变量总数
        key_in: 密钥输入状态变量矩阵 [Round+1][80]
        key_out: 密钥输出状态变量矩阵 [Round][64]
        key_p, key_q, key_m: 密钥 S 盒辅助变量矩阵 [Round][16]
        
    说明:
        变量编号从 1 开始，每个变量代表一个比特位的差分状态
        (0 表示无差分，1 表示有差分)
    """
    count_var_num = 0

    # 状态变量
    xin = []   # 每轮输入状态
    p = []     # S盒辅助变量 p
    q = []     # S盒辅助变量 q
    m = []     # S盒辅助变量 m (活跃标志)
    xout = []  # 每轮输出状态

    # 密钥变量
    key_in = []    # 密钥状态输入
    key_out = []   # 密钥状态输出
    key_p = []     # 密钥 S 盒辅助变量
    key_q = []     # 密钥 S 盒辅助变量
    key_m = []     # 密钥 S 盒辅助变量

    # 生成每轮的输入状态变量 (64 bits)
    for i in range(Round):
        xin.append([])
        p.append([])
        q.append([])
        m.append([])
        for j in range(64):
            count_var_num += 1
            xin[i].append(count_var_num)
 
        # 生成 S 盒辅助变量 (16 个 S 盒，每个有 p, q, m 三个辅助变量)
        for j in range(16):
            count_var_num += 1
            p[i].append(count_var_num) 
            count_var_num += 1
            q[i].append(count_var_num)
            count_var_num += 1
            m[i].append(count_var_num)

    # 生成每轮的输出状态变量 (64 bits)
    for i in range(Round):
        xout.append([])
        for j in range(64):
            count_var_num += 1
            xout[i].append(count_var_num)

    # 生成密钥状态变量 (80 bits, Round+1 轮)
    for i in range(Round + 1):
        key_in.append([])
        for j in range(80):
            count_var_num += 1
            key_in[i].append(count_var_num)

    # 生成密钥输出状态变量 (64 bits)
    for i in range(Round):
        key_out.append([])
        for j in range(64):
            count_var_num += 1
            key_out[i].append(count_var_num)

    # 生成密钥 S 盒辅助变量
    for i in range(Round):
        key_p.append([])
        key_q.append([])
        key_m.append([])
        for j in range(16):
            count_var_num += 1
            key_p[i].append(count_var_num)
            count_var_num += 1
            key_q[i].append(count_var_num)
            count_var_num += 1
            key_m[i].append(count_var_num)

    # 生成顺序编码辅助变量
    # 用于约束活跃 S 盒的总数不超过某个阈值
    auxiliary_var_u = []
    for r in range(0, Round):
        auxiliary_var_u.append([])
        for i in range(48):  # 每轮 48 个活跃 S 盒位置 (16*3)
            if (r == (Round - 1)) and (i == 47):
                continue
            auxiliary_var_u[r].append([])
            if (objLowerBound[(r) * (48) + i] == objUpperBound[(r) * (48) + i]):
                continue
            for j in range(objLowerBound[(r) * (48) + i], objUpperBound[(r) * (48) + i]):
                count_var_num += 1
                auxiliary_var_u[r][i].append(count_var_num)

    return (xin, xout, p, q, m, auxiliary_var_u, count_var_num, key_in, key_out, key_p, key_q, key_m)


# ==================== 子句计数函数 ====================

def CountClausesInRoundFunction(Round, count_clause_num):
    """
    计算轮函数约束中的子句数量
    
    参数:
        Round: 轮数
        count_clause_num: 当前子句计数
        
    返回:
        更新后的子句计数
        
    说明:
        每个 S 盒有 40 个 CNF 子句约束
        每轮有 16 个 S 盒
    """
    for r in range(Round):
        for i in range(16):
            for j in range(40):
                count_clause_num += 1
    return count_clause_num


# ==================== 轮函数约束生成 ====================

def GenRoundConstrain(TotalRound, xin, p, q, m, xout, file):
    """
    生成轮函数的 CNF 约束
    
    参数:
        TotalRound: 总轮数
        xin: 输入状态变量
        p, q, m: S 盒辅助变量
        xout: 输出状态变量
        file: 输出文件句柄
        
    说明:
        RECTANGLE 轮函数包括:
        1. S 盒层: 16 个 4x4 S 盒并行替换
        2. 置换层 (P): 比特位置换
        
        S 盒约束使用符号化 CNF 表示，将差分传播的有效性约束转化为子句
    """
    for r in range(TotalRound):
        y = list([])
        # 置换层 P 的定义
        # P 将位置 i 映射到 P[i]
        P = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
             17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 16,
             44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
             61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60]
        
        # S 盒的符号化 CNF 约束
        # 每行代表一个子句，11 个元素对应:
        # [输入4位, 输出4位, p, q, m]
        # 1 表示正文字，-1 表示负文字，0 表示不出现
        SymbolicCNFConstraintForSbox = [ 
            [0, 0, 1, 0, 1, 1, 0, 1, -1, 0, 0],
            [1, 0, 1, 1, 0, 0, 0, 0, 0, 0, -1],
            [1, 1, 1, -1, 0, 0, 1, 0, 0, 0, 0],
            [0, 1, -1, 0, 0, 0, 1, -1, 0, 0, -1],
            [0, 1, 0, 0, 0, 1, -1, 0, 0, 0, 1],
            [0, 1, 0, 0, 1, -1, 1, 1, 0, 0, 0],
            [0, 1, -1, -1, 0, -1, 0, -1, 0, 0, 0],
            [1, 0, -1, -1, -1, -1, 1, -1, 0, 0, 0],
            [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, -1],
            [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1],
            [1, 0, 0, 1, 1, -1, 1, -1, 0, 0, 0],
            [1, 0, 1, 1, 0, 0, 0, 1, -1, 0, 0],
            [1, 0, 0, 1, -1, 1, 1, -1, 0, 0, 0],
            [1, -1, 1, -1, 0, 0, -1, 0, 0, 0, 0],
            [0, -1, 0, 0, 0, 0, 1, -1, 0, 0, 1],
            [0, 0, -1, 0, -1, -1, -1, 1, 0, 0, 0],
            [1, 0, -1, -1, 1, 1, 1, 0, 0, 0, 0],
            [0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
            [1, -1, -1, 0, 1, 0, -1, -1, 0, 0, 0],
            [-1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1],
            [0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
            [0, 0, 1, 0, -1, -1, 1, 0, 0, 0, 1],
            [-1, 0, 0, -1, 0, 0, 1, 1, 0, 0, 1],
            [0, 1, 1, 0, 0, 0, 0, -1, 0, 0, 1],
            [-1, 0, 1, -1, 0, 0, -1, -1, 0, 0, 0],
            [0, 0, -1, 0, 0, 0, 1, 1, 0, 0, 1],
            [-1, 0, -1, 1, 1, 1, 1, 0, 0, 0, 0],
            [0, 1, -1, 1, 0, 1, 0, -1, 0, 0, 0],
            [-1, 0, -1, 1, -1, -1, 1, -1, 0, 0, 0],
            [0, 0, -1, 0, 0, 0, -1, -1, 0, 0, 1],
            [-1, 0, -1, -1, 1, -1, 1, -1, 0, 0, 0],
            [0, 1, -1, 0, 0, 0, 0, 1, 0, 0, 1],
            [-1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
            [-1, -1, 1, 1, 0, 0, 0, -1, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
            [0, -1, 0, 0, 1, -1, -1, 1, 0, 0, 0],
            [-1, -1, -1, 0, -1, 0, -1, 0, 0, 0, 0],
            [0, -1, -1, 0, -1, 1, 0, 1, 0, 0, 0],
            [-1, 0, -1, -1, -1, 1, 1, -1, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0]]
        
        # 应用置换层，得到输出状态 y
        for i in range(64):
            y += [xout[r][P[i]]]
        
        # 为每个 S 盒生成约束
        for i in range(16):
            X = list([])
            # S 盒输入 (按列排列)
            X += [xin[r][i + 48]]
            X += [xin[r][i + 32]]
            X += [xin[r][i + 16]]
            X += [xin[r][i + 0]]

            # S 盒输出 (按列排列)
            X += [y[i + 48]]
            X += [y[i + 32]]
            X += [y[i + 16]]
            X += [y[i + 0]]

            # 辅助变量
            X += [p[r][i]]
            X += [q[r][i]]
            X += [m[r][i]]

            # 生成 40 个 CNF 子句
            for j in range(40):
                clauseseq = ""
                for k in range(11):
                    if (SymbolicCNFConstraintForSbox[j][k] == -1):
                        clauseseq += "-" + str(X[k]) + " "
                    if (SymbolicCNFConstraintForSbox[j][k] == 1):
                        clauseseq += str(X[k]) + " "
                clauseseq += "0" + "\n"
                file.write(clauseseq)


# ==================== 密钥扩展约束生成 ====================

def GenKeyScheduleConstrain(TotalRound, key_in, key_out, key_p, key_q, key_m, file):
    """
    生成密钥扩展的 CNF 约束
    
    参数:
        TotalRound: 总轮数
        key_in: 密钥输入状态变量
        key_out: 密钥输出状态变量
        key_p, key_q, key_m: 密钥 S 盒辅助变量
        file: 输出文件句柄
        
    说明:
        RECTANGLE 密钥扩展:
        1. 80 位主密钥分为 5 个 16 位字
        2. 每轮使用 S 盒更新部分密钥位
        3. 密钥字之间进行循环移位
        
        相关密钥攻击中，需要约束两个相关密钥之间的差分传播
    """
    # S 盒约束 (与轮函数相同)
    SymbolicCNFConstraintForSbox = [ 
        [0, 0, 1, 0, 1, 1, 0, 1, -1, 0, 0],
        [1, 0, 1, 1, 0, 0, 0, 0, 0, 0, -1],
        [1, 1, 1, -1, 0, 0, 1, 0, 0, 0, 0],
        [0, 1, -1, 0, 0, 0, 1, -1, 0, 0, -1],
        [0, 1, 0, 0, 0, 1, -1, 0, 0, 0, 1],
        [0, 1, 0, 0, 1, -1, 1, 1, 0, 0, 0],
        [0, 1, -1, -1, 0, -1, 0, -1, 0, 0, 0],
        [1, 0, -1, -1, -1, -1, 1, -1, 0, 0, 0],
        [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, -1],
        [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1],
        [1, 0, 0, 1, 1, -1, 1, -1, 0, 0, 0],
        [1, 0, 1, 1, 0, 0, 0, 1, -1, 0, 0],
        [1, 0, 0, 1, -1, 1, 1, -1, 0, 0, 0],
        [1, -1, 1, -1, 0, 0, -1, 0, 0, 0, 0],
        [0, -1, 0, 0, 0, 0, 1, -1, 0, 0, 1],
        [0, 0, -1, 0, -1, -1, -1, 1, 0, 0, 0],
        [1, 0, -1, -1, 1, 1, 1, 0, 0, 0, 0],
        [0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [1, -1, -1, 0, 1, 0, -1, -1, 0, 0, 0],
        [-1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1],
        [0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
        [0, 0, 1, 0, -1, -1, 1, 0, 0, 0, 1],
        [-1, 0, 0, -1, 0, 0, 1, 1, 0, 0, 1],
        [0, 1, 1, 0, 0, 0, 0, -1, 0, 0, 1],
        [-1, 0, 1, -1, 0, 0, -1, -1, 0, 0, 0],
        [0, 0, -1, 0, 0, 0, 1, 1, 0, 0, 1],
        [-1, 0, -1, 1, 1, 1, 1, 0, 0, 0, 0],
        [0, 1, -1, 1, 0, 1, 0, -1, 0, 0, 0],
        [-1, 0, -1, 1, -1, -1, 1, -1, 0, 0, 0],
        [0, 0, -1, 0, 0, 0, -1, -1, 0, 0, 1],
        [-1, 0, -1, -1, 1, -1, 1, -1, 0, 0, 0],
        [0, 1, -1, 0, 0, 0, 0, 1, 0, 0, 1],
        [-1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [-1, -1, 1, 1, 0, 0, 0, -1, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
        [0, -1, 0, 0, 1, -1, -1, 1, 0, 0, 0],
        [-1, -1, -1, 0, -1, 0, -1, 0, 0, 0, 0],
        [0, -1, -1, 0, -1, 1, 0, 1, 0, 0, 0],
        [-1, 0, -1, -1, -1, 1, 1, -1, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0]]

    # 密钥 S 盒约束
    for r in range(TotalRound):
        for i in range(16):
            X = list([])
            # S 盒输入
            X += [key_in[r][i + 64]]
            X += [key_in[r][i + 48]]
            X += [key_in[r][i + 32]]
            X += [key_in[r][i + 0]]

            # S 盒输出
            X += [key_out[r][i + 48]]
            X += [key_out[r][i + 32]]
            X += [key_out[r][i + 16]]
            X += [key_out[r][i + 0]]

            # 辅助变量
            X += [key_p[r][i]]
            X += [key_q[r][i]]
            X += [key_m[r][i]]

            for j in range(40):
                clauseseq = ""
                for k in range(11):
                    if (SymbolicCNFConstraintForSbox[j][k] == -1):
                        clauseseq += "-" + str(X[k]) + " "
                    if (SymbolicCNFConstraintForSbox[j][k] == 1):
                        clauseseq += str(X[k]) + " "
                clauseseq += "0" + "\n"
                file.write(clauseseq)

    # 密钥字之间的等价约束
    # key_out[r][i] == key_in[r][i + 16]
    for r in range(TotalRound):
        for i in range(16):
            clauseseq = str(key_out[r][i]) + " -" + str(key_in[r][i + 16]) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(key_out[r][i]) + " " + str(key_in[r][i + 16]) + " 0\n"
            file.write(clauseseq)

    # 密钥状态更新约束
    # key_in[r+1][i+16] == key_in[r][i+32]
    for r in range(TotalRound):
        for i in range(16):
            clauseseq = str(key_in[r + 1][i + 16]) + " -" + str(key_in[r][i + 32]) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(key_in[r + 1][i + 16]) + " " + str(key_in[r][i + 32]) + " 0\n"
            file.write(clauseseq)
            
            clauseseq = str(key_in[r + 1][i + 32]) + " -" + str(key_in[r][i + 48]) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(key_in[r + 1][i + 32]) + " " + str(key_in[r][i + 48]) + " 0\n"
            file.write(clauseseq)

    # key_in[r+1][i+48] == key_in[r][i+64]
    for r in range(TotalRound):
        for i in range(16):
            clauseseq = str(key_in[r + 1][i + 48]) + " -" + str(key_in[r][i + 64]) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(key_in[r + 1][i + 48]) + " " + str(key_in[r][i + 64]) + " 0\n"
            file.write(clauseseq)
            
            clauseseq = str(key_in[r + 1][i + 64]) + " -" + str(key_in[r][i]) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(key_in[r + 1][i + 64]) + " " + str(key_in[r][i]) + " 0\n"
            file.write(clauseseq)

    # XOR 约束: key_in[r+1][i] = key_out[r][i+16] XOR key_in[r][i+16]
    for r in range(TotalRound):
        for i in range(16):
            clauseseq = str(key_in[r + 1][i]) + " -" + str(key_out[r][i + 16]) + " -" + str(key_in[r][i + 16]) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(key_in[r + 1][i]) + " " + str(key_out[r][i + 16]) + " -" + str(key_in[r][i + 16]) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(key_in[r + 1][i]) + " -" + str(key_out[r][i + 16]) + " " + str(key_in[r][i + 16]) + " 0\n"
            file.write(clauseseq)
            clauseseq = str(key_in[r + 1][i]) + " " + str(key_out[r][i + 16]) + " " + str(key_in[r][i + 16]) + " 0\n"
            file.write(clauseseq)


# ==================== 轮密钥加约束生成 ====================

def GenAddRoundKeyConstrain(TotalRound, xin, xout, key_out, file):
    """
    生成轮密钥加操作的 CNF 约束
    
    参数:
        TotalRound: 总轮数
        xin: 输入状态变量
        xout: 输出状态变量
        key_out: 轮密钥变量
        file: 输出文件句柄
        
    说明:
        轮密钥加: xin[r+1][i] = xout[r][i] XOR key_out[r][i]
        使用 4 个子句表示 XOR 约束
    """
    for r in range(TotalRound - 1):
        for i in range(64):
            a = xin[r + 1][i]
            b = xout[r][i]
            c = key_out[r][i]
            # XOR 约束的 CNF 表示
            clauseseq = "-" + str(a) + " -" + str(b) + " -" + str(c) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(a) + " " + str(b) + " " + str(c) + " 0\n"
            file.write(clauseseq)
            clauseseq = str(a) + " -" + str(b) + " " + str(c) + " 0\n"
            file.write(clauseseq)
            clauseseq = str(a) + " " + str(b) + " -" + str(c) + " 0\n"
            file.write(clauseseq)


# ==================== 顺序编码子句计数 ====================

def CountClausesInSequentialEncoding(TotalRound, Wvars, Uvars, objLowerBound, objUpperBound, count_clause_num):
    """
    计算顺序编码约束中的子句数量
    
    参数:
        TotalRound: 总轮数
        Wvars: 权重变量列表
        Uvars: 辅助变量列表
        objLowerBound: 下界列表
        objUpperBound: 上界列表
        count_clause_num: 当前子句计数
        
    返回:
        更新后的子句计数
        
    说明:
        顺序编码用于约束一组布尔变量的和不超过某个阈值
        这是 SAT 问题中表示基数约束的经典方法
    """
    if (len(Uvars[0]) > 0):
        count_clause_num += 1
    if (objLowerBound[0] == 0) and (objUpperBound[0] == 0):
        count_clause_num += 1
    if (objLowerBound[0] == 1) and (objUpperBound[0] == 1):
        count_clause_num += 1

    if len(Wvars) > 2:
        for i in range(1, len(Wvars) - 1):
            l_i_1 = objLowerBound[i - 1]
            m_i_1 = objUpperBound[i - 1]
            
            l_i = objLowerBound[i]
            m_i = objUpperBound[i]
            
            if (m_i == 0):
                count_clause_num += 1
                continue

            if (l_i == 0):
                count_clause_num += 1
                if (l_i_1 < m_i_1):
                    count_clause_num += 1

            if m_i > max(1, l_i):
                for j in range(max(1, l_i), m_i):
                    if (j <= l_i_1):
                        count_clause_num += 1
                    if ((j > l_i_1) and (j <= m_i_1)):
                        count_clause_num += 1
                    if ((j >= l_i_1) and (j <= m_i_1 - 1)):
                        count_clause_num += 1
            
            if (l_i_1 == m_i):
                count_clause_num += 1
            if ((m_i_1 == m_i) and (l_i_1 < m_i)):
                count_clause_num += 1

    if len(Wvars) >= 2:
        i = len(Wvars) - 1
        l_i_1 = objLowerBound[i - 1]
        m_i_1 = objUpperBound[i - 1]
        l_i = objLowerBound[i]
        m_i = objUpperBound[i]
            
        if ((l_i_1 == m_i)):
            count_clause_num += 1
        if ((m_i_1 == m_i) and (l_i_1 < m_i)):
            count_clause_num += 1
                
    return (count_clause_num)


# ==================== 顺序编码约束生成 ====================

def GenSequentialEncoding(TotalRound, Wvars, Uvars, objLowerBound, objUpperBound, file):
    """
    生成顺序编码约束
    
    参数:
        TotalRound: 总轮数
        Wvars: 权重变量列表 (活跃 S 盒标志)
        Uvars: 辅助变量列表
        objLowerBound: 下界列表
        objUpperBound: 上界列表
        file: 输出文件句柄
        
    说明:
        顺序编码将基数约束 (sum <= k) 转化为 CNF
        对于活跃 S 盒数量的约束，这比直接编码更高效
    """
    if (len(Uvars[0]) > 0):
        clauseseq = "-" + str(Wvars[0]) + " " + str(Uvars[0][0]) + " 0" + "\n"
        file.write(clauseseq)
    if (objLowerBound[0] == 0) and (objUpperBound[0] == 0):
        clauseseq = "-" + str(Wvars[0]) + " 0" + "\n"
        file.write(clauseseq)
    if (objLowerBound[0] == 1) and (objUpperBound[0] == 1):
        clauseseq = str(Wvars[0]) + " 0" + "\n"
        file.write(clauseseq)

    if len(Wvars) > 2:
        for i in range(1, len(Wvars) - 1):
            l_i_1 = objLowerBound[i - 1]
            m_i_1 = objUpperBound[i - 1]
            
            l_i = objLowerBound[i]
            m_i = objUpperBound[i]
            
            if (m_i == 0):
                clauseseq = "-" + str(Wvars[i]) + " 0" + "\n"
                file.write(clauseseq)
                continue

            if (l_i == 0):
                clauseseq = "-" + str(Wvars[i]) + " " + str(Uvars[i][0]) + " 0" + "\n"
                file.write(clauseseq)
                if (l_i_1 < m_i_1):
                    clauseseq = "-" + str(Uvars[i - 1][0]) + " " + str(Uvars[i][0]) + " 0" + "\n"
                    file.write(clauseseq)

            if m_i > max(1, l_i):
                for j in range(max(1, l_i), m_i):
                    if (j <= l_i_1):
                        clauseseq = "-" + str(Wvars[i]) + " " + str(Uvars[i][j - l_i]) + " 0\n"
                        file.write(clauseseq)
                    if ((j > l_i_1) and (j <= m_i_1)):
                        clauseseq = "-" + str(Wvars[i]) + " " + "-" + str(Uvars[i - 1][j - 1 - l_i_1]) + " " + str(Uvars[i][j - l_i]) + " 0\n"
                        file.write(clauseseq)
                    if ((j >= l_i_1) and (j <= m_i_1 - 1)):
                        clauseseq = "-" + str(Uvars[i - 1][j - l_i_1]) + " " + str(Uvars[i][j - l_i]) + " 0\n"
                        file.write(clauseseq)
     
            if (l_i_1 == m_i):
                clauseseq = "-" + str(Wvars[i]) + " 0\n"
                file.write(clauseseq)
            if ((m_i_1 == m_i) and (l_i_1 < m_i)):
                clauseseq = "-" + str(Wvars[i]) + " " + "-" + str(Uvars[i - 1][len(Uvars[i - 1]) - 1]) + " 0\n"
                file.write(clauseseq)

    if len(Wvars) >= 2:
        i = len(Wvars) - 1
        l_i_1 = objLowerBound[i - 1]
        m_i_1 = objUpperBound[i - 1]
        l_i = objLowerBound[i]
        m_i = objUpperBound[i]
            
        if ((l_i_1 == m_i)):
            clauseseq = "-" + str(Wvars[i]) + " 0" + "\n"
            file.write(clauseseq)
        if ((m_i_1 == m_i) and (l_i_1 < m_i)):
            clauseseq = "-" + str(Wvars[i]) + " " + "-" + str(Uvars[i - 1][len(Uvars[i - 1]) - 1]) + " 0" + "\n"
            file.write(clauseseq)


# ==================== 上下界计算函数 ====================

def AccurateLowerBound(obj, TOTALROUND, MatsuiProbabilityBound, BlockWeightSize):
    """
    使用 MILP 计算精确下界
    
    参数:
        obj: 目标位置索引
        TOTALROUND: 总轮数
        MatsuiProbabilityBound: Matsui 概率界限
        BlockWeightSize: 块权重大小 (48)
        
    返回:
        下界值或 "infeasible"
        
    说明:
        使用 Gurobi 求解 MILP 模型，计算在给定概率约束下
        前 obj+1 个位置活跃 S 盒数量的最小值
    """
    M = Model()
    M.Params.LogToConsole = 0  # 禁止控制台输出

    # 创建二进制变量矩阵
    wvariables = []
    for i in range(TOTALROUND):
        wvariables.append([])
        for j in range(BlockWeightSize):
            wvariables[i].append(M.addVar(vtype=GRB.BINARY))
    
    # 添加连续轮的概率约束
    for e1 in range(TOTALROUND):
        for e2 in range(e1, max(TOTALROUND, e1 + 1)):
            constrain = LinExpr()
            for i in range(e1, e2 + 1):
                for j in range(BlockWeightSize):
                    constrain += wvariables[i][j]
            M.addConstr(constrain >= MatsuiProbabilityBound[e2 - e1 + 1])
    
    # 添加总概率约束
    constrain = LinExpr()
    for i in range(TOTALROUND):
        for j in range(BlockWeightSize):
            constrain += wvariables[i][j]
    M.addConstr(constrain <= MatsuiProbabilityBound[TOTALROUND])

    # 设置目标函数：最小化前 obj+1 个位置的活跃 S 盒数
    wvar = []
    for var in wvariables:
        wvar += var
    objconstrain = LinExpr()
    for i in range(obj + 1):
        objconstrain += wvar[i]
    M.setObjective(objconstrain, GRB.MINIMIZE)
    M.optimize()

    if (M.Status == 2):  # 最优解
        return (round(M.objVal))
    else:
        return ("infeasible")


def AccurateUpperBound(obj, TOTALROUND, MatsuiProbabilityBound, BlockWeightSize):
    """
    使用 MILP 计算精确上界
    
    参数:
        obj: 目标位置索引
        TOTALROUND: 总轮数
        MatsuiProbabilityBound: Matsui 概率界限
        BlockWeightSize: 块权重大小 (48)
        
    返回:
        上界值或 "infeasible"
        
    说明:
        与 AccurateLowerBound 类似，但目标是最大化
    """
    M = Model()
    M.Params.LogToConsole = 0
    wvariables = []
    for i in range(TOTALROUND):
        wvariables.append([])
        for j in range(BlockWeightSize):
            wvariables[i].append(M.addVar(vtype=GRB.BINARY))
    for e1 in range(TOTALROUND):
        for e2 in range(e1, max(TOTALROUND, e1 + 1)):
            constrain = LinExpr()
            for i in range(e1, e2 + 1):
                for j in range(BlockWeightSize):
                    constrain += wvariables[i][j]
            M.addConstr(constrain >= MatsuiProbabilityBound[e2 - e1 + 1])
    constrain = LinExpr()
    for i in range(TOTALROUND):
        for j in range(BlockWeightSize):
            constrain += wvariables[i][j]
    M.addConstr(constrain <= MatsuiProbabilityBound[TOTALROUND])

    wvar = []
    for var in wvariables:
        wvar += var
    objconstrain = LinExpr()
    for i in range(obj + 1):
        objconstrain += wvar[i]
    M.setObjective(objconstrain, GRB.MAXIMIZE)
    M.optimize()

    if (M.Status == 2):
        return (round(M.objVal))
    else:
        return ("infeasible")


# ==================== 主决策函数 ====================

def Decision(TotalRound, objLowerBound, objUpperBound):
    """
    主决策函数：生成 CNF 文件并调用 SAT 求解器
    
    参数:
        TotalRound: 总轮数
        objLowerBound: 下界列表
        objUpperBound: 上界列表
        
    返回:
        Result: 求解结果
        count_var_num: 变量数量
        count_clause_num: 子句数量
        求解时间
        
    说明:
        1. 生成所有变量
        2. 计算子句数量
        3. 生成 CNF 文件
        4. 调用 SAT 求解器
        5. 提取结果
    """
    Probability = ProbabilityBound[TotalRound]
    count_var_num = 0
    count_clause_num = 0

    (xin, xout, p, q, m, auxiliary_var_u, count_var_num, key_in, key_out, key_p, key_q, key_m) = GenerateAndCountVariables(TotalRound, objLowerBound, objUpperBound)

    # 构建权重变量列表
    Wvars = []
    for r in range(TotalRound):
        for i in range(16):
            Wvars.append(p[r][i])
            Wvars.append(q[r][i])
            Wvars.append(m[r][i])
    Uvars = []

    for uvar in auxiliary_var_u:
        Uvars += uvar

    # 计算子句数量
    count_clause_num = 0
    count_clause_num = CountClausesInRoundFunction(TotalRound, count_clause_num)

    count_clause_num += TotalRound * 16 * 40  # 密钥 S 盒约束
    
    count_clause_num += TotalRound * 16 * 2   # 密钥等价约束
    
    count_clause_num += TotalRound * 16 * 4   # 密钥更新约束 1
    
    count_clause_num += TotalRound * 16 * 4   # 密钥更新约束 2
    
    count_clause_num += TotalRound * 16 * 4   # 密钥 XOR 约束
    
    count_clause_num += (TotalRound - 1) * 64 * 4  # 轮密钥加约束

    count_clause_num = CountClausesInSequentialEncoding(TotalRound, Wvars, Uvars, objLowerBound, objUpperBound, count_clause_num)

    # 生成 CNF 文件
    file = open("Problem-Round" + str(TotalRound) + "-Probability" + str(Probability) + "-RelatedKey.cnf", "w")
    file.write("p cnf " + str(count_var_num) + " " + str(count_clause_num) + "\n")

    GenRoundConstrain(TotalRound, xin, p, q, m, xout, file)
    GenKeyScheduleConstrain(TotalRound, key_in, key_out, key_p, key_q, key_m, file)
    GenAddRoundKeyConstrain(TotalRound, xin, xout, key_out, file)
    GenSequentialEncoding(TotalRound, Wvars, Uvars, objLowerBound, objUpperBound, file)
    file.close()

    time_start = time.time()

    # 【问题】Windows 特定路径，跨平台兼容性问题
    order = "d:/solver/cadical-master/build/cadical " + "Problem-Round" + str(TotalRound) + "-Probability" + str(Probability) + "-RelatedKey.cnf > Round" + str(TotalRound) + "-Probability" + str(Probability) + "-RelatedKey-solution.txt"
    os.system(order)
    time_end = time.time()

    (Result, Results) = ExtractionResults("Round" + str(TotalRound) + "-Probability" + str(Probability) + "-RelatedKey-solution.txt")

    # 记录结果
    fileResult = open("ProcessResult_RelatedKey.txt", "a")
    if (Result == "SATISFIABLE"):
        fileResult.write("\n Round:" + str(TotalRound) + "; Probability: " + str(Probability) + "; Sat; TotalCost: " + str(time_end - time_start) + " p: " + str(count_var_num) + " cnf: " + str(count_clause_num))
    else:
        fileResult.write("\n Round:" + str(TotalRound) + "; Probability: " + str(Probability) + "; Unsat; TotalCost: " + str(time_end - time_start) + " p: " + str(count_var_num) + " cnf: " + str(count_clause_num))
    fileResult.close()

    # 【问题】Windows 特定删除命令
    order = "del Problem-Round" + str(TotalRound) + "-Probability" + str(Probability) + "-RelatedKey.cnf"
    os.system(order)

    return (Result, count_var_num, count_clause_num, time_end - time_start)


# ==================== 主程序入口 ====================

if __name__ == '__main__':
    Total_var_num = 0
    Total_clause_num = 0
    Total_Solve_time = 0
    blockweightsize = 48  # 每轮活跃 S 盒位置数 (16*3)

    for totalround in range(SearchRoundStart, SearchRoundEnd + 1):
        count_var_num = 0
        count_clause_num = 0
        count_time = 0

        time_start = time.time()
        Result = "UNSATISFIABLE"
        
        # 【问题】ProbabilityBound[1] 初始为 0，导致概率计算错误
        ProbabilityBound[totalround] = ProbabilityBound[totalround - 1] + ProbabilityBound[1]

        while (Result == "UNSATISFIABLE"):
            objLowerBoundList = []
            objUpperBoundList = []
            objLowerBound = []
            objUpperBound = []

            for i in range(totalround * 48):
                objLowerBoundList.append(i)
                objUpperBoundList.append(i)
            
            # 使用多进程并行计算上下界
            pool = Pool()
            objLowerBound = pool.map(partial(AccurateLowerBound, TOTALROUND=totalround, MatsuiProbabilityBound=ProbabilityBound, BlockWeightSize=blockweightsize), objLowerBoundList)
            objUpperBound = pool.map(partial(AccurateUpperBound, TOTALROUND=totalround, MatsuiProbabilityBound=ProbabilityBound, BlockWeightSize=blockweightsize), objUpperBoundList)
            pool.close()
            pool.join()

            # 检查是否有不可行解
            if ("infeasible" in objLowerBound) or ("infeasible" in objUpperBound):
                ProbabilityBound[totalround] += 1
                continue
            
            (Result, var_num, clause_num, Time) = Decision(totalround, objLowerBound, objUpperBound)
            count_var_num += var_num
            count_clause_num += clause_num
            count_time += Time

            if (Result == "SATISFIABLE"):
                break
            ProbabilityBound[totalround] += 1

        Total_var_num += count_var_num
        Total_clause_num += count_clause_num
        Total_Solve_time += count_time

        # 记录运行时间统计
        file = open("RunTimeSummarise_RelatedKey.out", "a")
        resultseq = "Round: " + str(totalround) + "; Probability: " + str(ProbabilityBound[totalround]) + "; Runtime: " + str(count_time) + " count_var_num: " + str(count_var_num) + " count_clause_num: " + str(count_clause_num) + "\n"
        file.write(resultseq)
        file.close()

    print(Total_Solve_time)
    print(str(ProbabilityBound))
    file = open("RunTimeSummarise_RelatedKey.out", "a")
    resultseq = "Total Time of Solving SAT Model: " + str(Total_Solve_time) + " Total_var_num: " + str(Total_var_num) + " Total_clause_num" + str(Total_clause_num)
    file.write(resultseq)
    file.close()
