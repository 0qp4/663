from gurobipy import *
from functools import partial
from itertools import repeat
from multiprocessing import Pool,freeze_support
import os
import time
import random
import math

FullRound = 25

SearchRoundStart = 1
SearchRoundEnd = FullRound


ProbabilityBound = list([])
for i in range(FullRound+1):
    ProbabilityBound += [0]

def ExtractionResults(File):
    Result = "NoResult"
    Results = ""
    file = open(File,"rb")

    StopResult = 1
    StartResult = 0

    while StopResult:
        result = str(file.readline())
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
        
    if Result == "SATISFIABLE":

        Results = Results.replace("b'","")
        Results = Results.replace(" '","")
        Results = Results.replace("'","")
        Results = Results.replace("c ","")
        Results = Results.replace("v","")
        Results = Results.replace("s ","")
        Results = Results.replace("SATISFIABLE","")
        Results = Results.replace("UNSATISFIABLE ","")
        Results = Results.replace("\\n","")
        Results = Results.replace("\\r","")

        Results = Results.split(" ")
        del Results[0]
        del Results[len(Results)-1]

        for i in range(len(Results)):
            Results[i]= int(Results[i],10)
    return(Result,Results)

    
def GenerateAndCountVariables(Round,objLowerBound,objUpperBound):
    count_var_num = 0

    xin = []
    p = []
    q = []
    m = []
    xout = []

    key_in = []
    key_out = []
    key_p = []
    key_q = []
    key_m = []

    for i in range(Round):
        xin.append([])
        p.append([])
        q.append([])
        m.append([])
        for j in range(64):
            count_var_num += 1
            xin[i].append(count_var_num)
 
        for j in range(16):
            count_var_num += 1
            p[i].append(count_var_num) 
            count_var_num += 1
            q[i].append(count_var_num)
            count_var_num += 1
            m[i].append(count_var_num)
            

    for i in range(Round):
        xout.append([])
        for j in range(64):
            count_var_num += 1
            xout[i].append(count_var_num)

    for i in range(Round + 1):
        key_in.append([])
        for j in range(80):
            count_var_num += 1
            key_in[i].append(count_var_num)

    for i in range(Round):
        key_out.append([])
        for j in range(64):
            count_var_num += 1
            key_out[i].append(count_var_num)

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

    auxiliary_var_u = []
    for r in range(0,Round):
        auxiliary_var_u.append([])
        for i in range(48):
            if (r == (Round-1)) and (i ==47):
                continue
            auxiliary_var_u[r].append([])
            if(objLowerBound[(r)*(48)+i] == objUpperBound[(r)*(48)+i]):
                continue
            for j in range(objLowerBound[(r)*(48)+i],objUpperBound[(r)*(48)+i]):
                count_var_num += 1
                auxiliary_var_u[r][i].append(count_var_num)

    return(xin,xout,p,q,m,auxiliary_var_u,count_var_num,key_in,key_out,key_p,key_q,key_m)


def CountClausesInRoundFunction(Round, count_clause_num):

    for r in range(Round):
        for i in range(16):
            for j in range(40):
                count_clause_num += 1
    return count_clause_num

def GenRoundConstrain(TotalRound, xin,p,q,m,xout,file):

    for r in range(TotalRound):
        y = list([])
        P = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
            17, 18,19,20,21,22,23,24,25,26,27, 28, 29, 30, 31, 16,
            44, 45,46,47,32,33,34,35,36,37,38, 39, 40, 41, 42, 43,
            61, 62,63,48,49,50,51,52,53,54,55, 56, 57, 58, 59, 60]
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
        for i in range(64):
            y += [xout[r][P[i]]]
        for i in range(16):
            X = list([])
            X += [xin[r][i + 48]]
            X += [xin[r][i + 32]]
            X += [xin[r][i + 16]]
            X += [xin[r][i + 0]]

            X += [y[i + 48]]
            X += [y[i + 32]]
            X += [y[i + 16]]
            X += [y[i + 0]]
 
            X += [p[r][i]]
            X += [q[r][i]]
            X += [m[r][i]]

            for j in range(40):
                clauseseq = ""
                for k in range(11):
                    if (SymbolicCNFConstraintForSbox[j][k] == -1):
                        clauseseq += "-" + str(X[k]) + " "
                    if (SymbolicCNFConstraintForSbox[j][k] == 1):
                        clauseseq += str(X[k]) + " "
                clauseseq += "0" + "\n"
                file.write(clauseseq)

def GenKeyScheduleConstrain(TotalRound, key_in, key_out, key_p, key_q, key_m, file):
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

    for r in range(TotalRound):
        for i in range(16):
            X = list([])
            X += [key_in[r][i + 64]]
            X += [key_in[r][i + 48]]
            X += [key_in[r][i + 32]]
            X += [key_in[r][i + 0]]

            X += [key_out[r][i + 48]]
            X += [key_out[r][i + 32]]
            X += [key_out[r][i + 16]]
            X += [key_out[r][i + 0]]

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

    for r in range(TotalRound):
        for i in range(16):
            clauseseq = str(key_out[r][i]) + " -" + str(key_in[r][i + 16]) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(key_out[r][i]) + " " + str(key_in[r][i + 16]) + " 0\n"
            file.write(clauseseq)

    for r in range(TotalRound):
        for i in range(16):
            clauseseq = str(key_in[r+1][i+16]) + " -" + str(key_in[r][i+32]) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(key_in[r+1][i+16]) + " " + str(key_in[r][i+32]) + " 0\n"
            file.write(clauseseq)
            
            clauseseq = str(key_in[r+1][i+32]) + " -" + str(key_in[r][i+48]) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(key_in[r+1][i+32]) + " " + str(key_in[r][i+48]) + " 0\n"
            file.write(clauseseq)

    for r in range(TotalRound):
        for i in range(16):
            clauseseq = str(key_in[r+1][i+48]) + " -" + str(key_in[r][i+64]) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(key_in[r+1][i+48]) + " " + str(key_in[r][i+64]) + " 0\n"
            file.write(clauseseq)
            
            clauseseq = str(key_in[r+1][i+64]) + " -" + str(key_in[r][i]) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(key_in[r+1][i+64]) + " " + str(key_in[r][i]) + " 0\n"
            file.write(clauseseq)

    for r in range(TotalRound):
        for i in range(16):
            clauseseq = str(key_in[r+1][i]) + " -" + str(key_out[r][i+16]) + " -" + str(key_in[r][i+16]) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(key_in[r+1][i]) + " " + str(key_out[r][i+16]) + " -" + str(key_in[r][i+16]) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(key_in[r+1][i]) + " -" + str(key_out[r][i+16]) + " " + str(key_in[r][i+16]) + " 0\n"
            file.write(clauseseq)
            clauseseq = str(key_in[r+1][i]) + " " + str(key_out[r][i+16]) + " " + str(key_in[r][i+16]) + " 0\n"
            file.write(clauseseq)

def GenAddRoundKeyConstrain(TotalRound, xin, xout, key_out, file):
    for r in range(TotalRound - 1):
        for i in range(64):
            a = xin[r + 1][i]
            b = xout[r][i]
            c = key_out[r][i]
            clauseseq = "-" + str(a) + " -" + str(b) + " -" + str(c) + " 0\n"
            file.write(clauseseq)
            clauseseq = "-" + str(a) + " " + str(b) + " " + str(c) + " 0\n"
            file.write(clauseseq)
            clauseseq = str(a) + " -" + str(b) + " " + str(c) + " 0\n"
            file.write(clauseseq)
            clauseseq = str(a) + " " + str(b) + " -" + str(c) + " 0\n"
            file.write(clauseseq)

def CountClausesInSequentialEncoding(TotalRound,Wvars, Uvars, objLowerBound,objUpperBound, count_clause_num):
    if(len(Uvars[0]) > 0):
        count_clause_num += 1
    if (objLowerBound[0] == 0) and (objUpperBound[0] == 0):
        count_clause_num += 1
    if (objLowerBound[0] == 1) and (objUpperBound[0] == 1):
        count_clause_num += 1

    if len(Wvars) > 2:
        for i in range(1,len(Wvars)-1):
            l_i_1 = objLowerBound[i-1]
            m_i_1 = objUpperBound[i-1]
            
            l_i = objLowerBound[i]
            m_i = objUpperBound[i]
            
            if(m_i == 0):
                count_clause_num += 1
                continue

            if(l_i == 0):
                count_clause_num += 1
                if(l_i_1 < m_i_1):
                    count_clause_num += 1


            if m_i > max(1,l_i):
                for j in range(max(1,l_i),m_i):
                    if(j <= l_i_1):
                        count_clause_num += 1
                    if(  (j > l_i_1) and (j <= m_i_1)):
                        count_clause_num += 1
                    if( (j >= l_i_1) and (j <= m_i_1 - 1) ):
                        count_clause_num += 1
                
            
            if (l_i_1 == m_i):
                count_clause_num += 1
            if ((m_i_1 == m_i) and (l_i_1 < m_i)):
                count_clause_num += 1
    

    if len(Wvars) >= 2:
        i = len(Wvars) - 1
        l_i_1 = objLowerBound[i-1]
        m_i_1 = objUpperBound[i-1]
        l_i = objLowerBound[i]
        m_i = objUpperBound[i]
            
        if ( (l_i_1 == m_i)):
            count_clause_num += 1
        if ((m_i_1 == m_i) and (l_i_1 < m_i)):
            count_clause_num += 1
                
    return(count_clause_num)


def GenSequentialEncoding(TotalRound, Wvars, Uvars,objLowerBound,objUpperBound, file):
    if(len(Uvars[0]) > 0):
        clauseseq = "-" + str(Wvars[0]) + " " + str(Uvars[0][0]) + " 0" + "\n"
        file.write(clauseseq)
    if (objLowerBound[0] == 0) and (objUpperBound[0] == 0):
        clauseseq = "-" + str(Wvars[0]) +  " 0" + "\n"
        file.write(clauseseq)
    if (objLowerBound[0] == 1) and (objUpperBound[0] == 1):
        clauseseq =  str(Wvars[0]) +  " 0" + "\n"
        file.write(clauseseq)

    if len(Wvars) > 2:
        for i in range(1,len(Wvars)-1):
            l_i_1 = objLowerBound[i-1]
            m_i_1 = objUpperBound[i-1]
            
            l_i = objLowerBound[i]
            m_i = objUpperBound[i]
            
            if(m_i == 0):
                clauseseq = "-" + str(Wvars[i]) + " 0" + "\n"
                file.write(clauseseq)
                continue

            if(l_i == 0):
                clauseseq = "-" + str(Wvars[i]) + " " + str(Uvars[i][0]) + " 0" + "\n"
                file.write(clauseseq)
                if(l_i_1 < m_i_1):
                    clauseseq = "-" + str(Uvars[i-1][0]) + " " + str(Uvars[i][0]) + " 0" + "\n"
                    file.write(clauseseq)


            if m_i > max(1,l_i):
                for j in range(max(1,l_i),m_i):
                    if(j <= l_i_1):
                        clauseseq = "-" + str(Wvars[i]) + " " + str(Uvars[i][j - l_i]) + " 0\n"
                        file.write(clauseseq)
                    if(  (j > l_i_1) and (j <= m_i_1)):
                        clauseseq = "-" + str(Wvars[i]) + " " + "-" + str(Uvars[i-1][ j-1 - l_i_1]) + " " + str(Uvars[i][j - l_i]) + " 0\n"
                        file.write(clauseseq)
                    if( (j >= l_i_1) and (j <= m_i_1 - 1) ):
                        clauseseq =  "-" + str(Uvars[i-1][j - l_i_1]) + " "  + str(Uvars[i][j - l_i]) + " 0\n"
                        file.write(clauseseq)
                
     
            if (l_i_1 == m_i):
                clauseseq = "-" + str(Wvars[i]) +  " 0\n"
                file.write(clauseseq)
            if ((m_i_1 == m_i) and (l_i_1 < m_i)):
                clauseseq = "-" + str(Wvars[i]) + " " + "-" + str(Uvars[i-1][len(Uvars[i-1])-1]) + " 0\n" 
                file.write(clauseseq)
    

    if len(Wvars) >= 2:
        i = len(Wvars) - 1
        l_i_1 = objLowerBound[i-1]
        m_i_1 = objUpperBound[i-1]
        l_i = objLowerBound[i]
        m_i = objUpperBound[i]
            
        if ( (l_i_1 == m_i)):
            clauseseq = "-" + str(Wvars[i]) +  " 0" + "\n"
            file.write(clauseseq)
        if ((m_i_1 == m_i) and (l_i_1 < m_i)):
            clauseseq = "-" + str(Wvars[i]) + " " + "-" + str(Uvars[i-1][len(Uvars[i-1])-1]) + " 0" + "\n"
            file.write(clauseseq)

def AccurateLowerBound(obj,TOTALROUND,MatsuiProbabilityBound,BlockWeightSize):
    M = Model()
    M.Params.LogToConsole = 0

    wvariables = []
    for i in range(TOTALROUND):
        wvariables.append([])
        for j in range(BlockWeightSize):
            wvariables[i].append(M.addVar(vtype = GRB.BINARY))
    for e1 in range(TOTALROUND):
        for e2 in range(e1,max(TOTALROUND,e1+1)):
            constrain = LinExpr()
            for i in range(e1,e2+1):
                for j in range(BlockWeightSize):
                    constrain += wvariables[i][j]
            M.addConstr(constrain >= MatsuiProbabilityBound[e2-e1 +1])
    constrain = LinExpr()
    for i in range(TOTALROUND):
        for j in range(BlockWeightSize):
            constrain += wvariables[i][j]
    M.addConstr(constrain <= MatsuiProbabilityBound[TOTALROUND])

    wvar = []
    for var in wvariables:
        wvar+= var
    objconstrain = LinExpr()
    for i in range(obj+1):
        objconstrain += wvar[i]
    M.setObjective(objconstrain,GRB.MINIMIZE)
    M.optimize ()

    
    if (M.Status == 2) :
        return(round(M.objVal))
    else:
        return("infeasible")


def AccurateUpperBound(obj,TOTALROUND,MatsuiProbabilityBound,BlockWeightSize):
    M = Model()
    M.Params.LogToConsole = 0
    wvariables = []
    for i in range(TOTALROUND):
        wvariables.append([])
        for j in range(BlockWeightSize):
            wvariables[i].append(M.addVar(vtype = GRB.BINARY))
    for e1 in range(TOTALROUND):
        for e2 in range(e1,max(TOTALROUND,e1+1)):
            constrain = LinExpr()
            for i in range(e1,e2+1):
                for j in range(BlockWeightSize):
                    constrain += wvariables[i][j]
            M.addConstr(constrain >= MatsuiProbabilityBound[e2-e1 +1])
    constrain = LinExpr()
    for i in range(TOTALROUND):
        for j in range(BlockWeightSize):
            constrain += wvariables[i][j]
    M.addConstr(constrain <= MatsuiProbabilityBound[TOTALROUND])

    wvar = []
    for var in wvariables:
        wvar+= var
    objconstrain = LinExpr()
    for i in range(obj+1):
        objconstrain += wvar[i]
    M.setObjective(objconstrain,GRB.MAXIMIZE)
    M.optimize ()

    
    if (M.Status == 2) :
        return(round(M.objVal))
    else:
        return("infeasible")
            
def Decision(TotalRound,objLowerBound,objUpperBound):

    Probability = ProbabilityBound[TotalRound]
    count_var_num = 0
    count_clause_num = 0

    (xin,xout,p,q,m,auxiliary_var_u,count_var_num,key_in,key_out,key_p,key_q,key_m)= GenerateAndCountVariables(TotalRound,objLowerBound,objUpperBound)

    Wvars = []
    for r in range(TotalRound):
        for i in range(16):
            Wvars.append(p[r][i])
            Wvars.append(q[r][i])
            Wvars.append(m[r][i])
    Uvars = []

    for uvar in auxiliary_var_u:
        Uvars += uvar


    count_clause_num = 0
    count_clause_num = CountClausesInRoundFunction(TotalRound,count_clause_num)

    count_clause_num += TotalRound * 16 * 40
    
    count_clause_num += TotalRound * 16 * 2
    
    count_clause_num += TotalRound * 16 * 4
    
    count_clause_num += TotalRound * 16 * 4
    
    count_clause_num += TotalRound * 16 * 4
    
    count_clause_num += (TotalRound - 1) * 64 * 4

    count_clause_num = CountClausesInSequentialEncoding(TotalRound, Wvars, Uvars, objLowerBound,objUpperBound,count_clause_num)


    file = open("Problem-Round" + str(TotalRound) + "-Probability" + str(Probability) + "-RelatedKey.cnf", "w")
    file.write("p cnf " + str(count_var_num) + " " + str(count_clause_num) + "\n")

    GenRoundConstrain(TotalRound,xin,p,q,m,xout,file)
    GenKeyScheduleConstrain(TotalRound, key_in, key_out, key_p, key_q, key_m, file)
    GenAddRoundKeyConstrain(TotalRound, xin, xout, key_out, file)
    GenSequentialEncoding(TotalRound, Wvars, Uvars, objLowerBound,objUpperBound, file)
    file.close()
    

    time_start = time.time()

    order = "d:/solver/cadical-master/build/cadical " + "Problem-Round" + str(TotalRound) + "-Probability" + str(Probability) + "-RelatedKey.cnf > Round" + str(TotalRound) + "-Probability" + str(Probability) + "-RelatedKey-solution.txt"
    os.system(order)
    time_end = time.time()


    (Result,Results)=ExtractionResults( "Round" + str(TotalRound) + "-Probability" + str(Probability) + "-RelatedKey-solution.txt")
  



    fileResult = open("ProcessResult_RelatedKey.txt", "a")
    if (Result == "SATISFIABLE"):
        fileResult.write("\n Round:" + str(TotalRound) + "; Probability: " + str(Probability) + "; Sat; TotalCost: " + str(time_end - time_start)+ " p: " +str(count_var_num) +" cnf: " + str(count_clause_num))
    else:
        fileResult.write("\n Round:" + str(TotalRound) + "; Probability: " + str(Probability) + "; Unsat; TotalCost: " + str(time_end - time_start)+ " p: " +str(count_var_num) +" cnf: " + str(count_clause_num))
    fileResult.close()

    order = "del Problem-Round" + str(TotalRound) + "-Probability" + str(Probability) + "-RelatedKey.cnf"
    os.system(order)

    return(Result,count_var_num,count_clause_num,time_end-time_start)




if __name__ == '__main__':
    freeze_support()
    Total_var_num = 0
    Total_clause_num =0
    Total_Solve_time = 0
    blockweightsize = 48

    for totalround in range(SearchRoundStart, SearchRoundEnd+1):
        count_var_num = 0
        count_clause_num = 0
        count_time = 0

        time_start = time.time()
        Result = "UNSATISFIABLE"
        ProbabilityBound[totalround] = ProbabilityBound[totalround-1] + ProbabilityBound[1]

        while (Result == "UNSATISFIABLE"):
            objLowerBoundList = []
            objUpperBoundList = []
            objLowerBound = []
            objUpperBound = []

            for i in range(totalround*48):
                objLowerBoundList.append(i)
                objUpperBoundList.append(i)
            pool = Pool()
            objLowerBound = pool.map(partial(AccurateLowerBound,TOTALROUND = totalround,MatsuiProbabilityBound= ProbabilityBound,BlockWeightSize = blockweightsize),objLowerBoundList)
            objUpperBound = pool.map(partial(AccurateUpperBound,TOTALROUND = totalround,MatsuiProbabilityBound = ProbabilityBound,BlockWeightSize = blockweightsize),objUpperBoundList)
            pool.close()
            pool.join()
                
     
            if ("infeasible" in objLowerBound) or ("infeasible" in objUpperBound):
                ProbabilityBound[totalround] += 1
                continue
            (Result,var_num,clause_num,Time) = Decision(totalround,objLowerBound,objUpperBound)
            count_var_num += var_num
            count_clause_num += clause_num
            count_time += Time

            if (Result == "SATISFIABLE"):
                break
            ProbabilityBound[totalround] += 1

        Total_var_num += count_var_num
        Total_clause_num += count_clause_num
        Total_Solve_time += count_time

        file = open("RunTimeSummarise_RelatedKey.out", "a")
        resultseq = "Round: " + str(totalround) + "; Probability: " + str(ProbabilityBound[totalround]) + "; Runtime: " + str(count_time) + " count_var_num: " + str(count_var_num) + " count_clause_num: " + str(count_clause_num)  +"\n"
        file.write(resultseq)
        file.close()

    print(Total_Solve_time)
    print(str(ProbabilityBound))
    file = open("RunTimeSummarise_RelatedKey.out", "a")
    resultseq = "Total Time of Solving SAT Model: " + str(Total_Solve_time) + " Total_var_num: " + str(Total_var_num) + " Total_clause_num" + str(Total_clause_num)
    file.write(resultseq)
    file.close()
