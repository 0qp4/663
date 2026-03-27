import os
import time
import random

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

        Results = Results.split(" ")
        del Results[0]
        del Results[len(Results)-1]

        for i in range(len(Results)):
            Results[i]= int(Results[i],10)
    return(Result,Results)

def GenerateAndCountVariables(Round,TotalProbability,Probability):
    count_var_num = 0

    xin = []
    p = []
    q = []
    m = []
    xout = []


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
            

    for i in range(Round - 1):
        xout.append([])
        for j in range(64):
            xout[i].append(xin[i + 1][j])
    xout.append([])
    for i in range(64):
        count_var_num += 1
        xout[Round - 1].append(count_var_num)


    auxiliary_var_u = []
    for r in range(0,Round):
        auxiliary_var_u.append([])
        for i in range(48):
            if (r == (Round-1)) and (i ==47):
                continue
            auxiliary_var_u[r].append([])
            for j in range(Probability):
                count_var_num += 1
                auxiliary_var_u[r][i].append(count_var_num)

    return(xin,xout,p,q,m,auxiliary_var_u,count_var_num)


def CountClausesInRoundFunction(Round, count_clause_num):

    count_clause_num += 1

    for r in range(Round):
        for i in range(16):
            for j in range(40):
                count_clause_num += 1
    return count_clause_num

def GenRoundConstrain(TotalRound, xin,p,q,m,xout,file):

    clauseseq = ""
    for i in range(64):
        clauseseq += str(xin[0][i]) + " "
    clauseseq += "0" + "\n"
    file.write(clauseseq)

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

def CountClausesInSequentialEncoding(TotalRound, Probability,Wvars, Uvars, count_clause_num):
    if (Probability > 0):
        count_clause_num += 1
        for i in range(1, Probability):
            count_clause_num += 1

        for i in range(1, len(Wvars)-1):
            count_clause_num += 1
            count_clause_num += 1
            count_clause_num += 1
        for j in range(1, Probability):
            for i in range(1, len(Wvars)-1):
                count_clause_num += 1
                count_clause_num += 1
        count_clause_num += 1

    elif (Probability == 0):
        for i in range(len(Wvars)):
            count_clause_num += 1

    return(count_clause_num)
    
    
def GenSequentialEncoding(TotalRound, Probability, Wvars, Uvars, file):

    if (Probability > 0):
        clauseseq = "-" + str(Wvars[0]) + " " + str(Uvars[0][0]) + " 0" + "\n"
        file.write(clauseseq)
        for i in range(1, Probability):
            clauseseq = "-" + str(Uvars[0][i]) + " 0" + "\n"
            file.write(clauseseq)


        for i in range(1, len(Wvars)-1):
            clauseseq = "-" + str(Wvars[i]) + " " + str(Uvars[i][0]) + " 0" + "\n"
            file.write(clauseseq)
            clauseseq = "-" + str(Uvars[i-1][0]) + " " + str(Uvars[i][0]) + " 0" + "\n"
            file.write(clauseseq)
            clauseseq = "-" + str(Wvars[i]) + " " + "-" + str(Uvars[i-1][Probability-1]) + " 0" + "\n"
            file.write(clauseseq)
        for j in range(1, Probability):
            for i in range(1, len(Wvars)-1):
                clauseseq = "-" + str(Wvars[i]) + " " + "-" + str(Uvars[i-1][j-1]) + " " + str(Uvars[i][j]) + " 0" + "\n"
                file.write(clauseseq)
                clauseseq = "-" + str(Uvars[i-1][j]) + " " + str(Uvars[i][j]) + " 0" + "\n"
                file.write(clauseseq)
        clauseseq = "-" + str(Wvars[len(Wvars)-1]) + " " + "-" + str(Uvars[len(Wvars)-2][Probability-1]) + " 0" + "\n"
        file.write(clauseseq)

    elif (Probability == 0):
        for i in range(len(Wvars)):
            clauseseq = "-" + str(Wvars[i]) + " 0\n"
            file.write(clauseseq)

            
def CountClausesForMatsuiStrategy(Wvars,Uvars,Probability,left,right,m,count_clause_num):
    if (m > 0):
        if ((left == 0) and (right < len(Wvars)-1)):
            for i in range(1, right + 1):
                count_clause_num += 1
        if ((left > 0) and (right == len(Wvars)-1)):
            for i in range(0, Probability - m):
                count_clause_num += 1
            for i in range(0, Probability-m+1):
                count_clause_num += 1
        if ((left > 0) and (right < len(Wvars)-1)):
            for i in range(0, Probability-m):
                count_clause_num += 1
    if (m == 0):
        for i in range(left, right + 1):
            count_clause_num += 1
    return(count_clause_num)

def GenMatsuiConstraint(Wvars,Uvars,Probability,left,right,m,file):
    if (m > 0):
        if ((left == 0) and (right < len(Wvars)-1)):
            for i in range(1, right + 1):
                clauseseq = "-" + str(Wvars[i]) + " " + "-" + str(Uvars[i-1][m-1]) + " 0" + "\n"
                file.write(clauseseq)
        if ((left > 0) and (right == len(Wvars)-1)):
            for i in range(0, Probability - m):
                clauseseq = str(Uvars[left-1][i]) + " " + "-" + str(Uvars[right - 1][i+m]) + " 0" + "\n"
                file.write(clauseseq)
            for i in range(0, Probability-m+1):
                clauseseq = str(Uvars[left-1][i]) + " " + "-" + str(Uvars[right]) + " " + "-" + str(Uvars[right - 1][i+m-1]) + " 0" + "\n"
                file.write(clauseseq)
        if ((left > 0) and (right < len(Wvars)-1)):
            for i in range(0, Probability-m):
                clauseseq = str(Uvars[left-1][i]) + " " + "-" + str(Uvars[right][i+m]) + " 0" + "\n"
                file.write(clauseseq)
    if (m == 0):
        for i in range(left, right + 1):
            clauseseq = "-" + str(Wvars[i]) + " 0" + "\n"
            file.write(clauseseq)
            
def Decision(Round, MatsuiRoundIndex):
    Probability = ProbabilityBound[Round]
    TotalProbability = 16 * Round * 3
    count_var_num = 0;
 
    (xin,xout,p,q,m,auxiliary_var_u,count_var_num) = GenerateAndCountVariables(Round,TotalProbability,Probability)

    Wvars = []
    for r in range(Round):
        for i in range(16):
            Wvars.append(p[r][i])
            Wvars.append(q[r][i])
            Wvars.append(m[r][i])
    Uvars = []

    for uvar in auxiliary_var_u:
        Uvars += uvar


    count_clause_num = 0
    count_clause_num = CountClausesInRoundFunction(Round,  count_clause_num)

    count_clause_num = CountClausesInSequentialEncoding(Round, Probability, Wvars, Uvars,count_clause_num)


    if len(MatsuiRoundIndex) > 0:
        for matsuiroundindex in MatsuiRoundIndex:
            StartingRound = matsuiroundindex[0]
            EndingRound = matsuiroundindex[1]
            LeftNode = StartingRound * (48)
            RightNode = EndingRound * (48) - 1
            

            mm = Probability - ProbabilityBound[StartingRound] - ProbabilityBound[Round - EndingRound]
            count_clause_num = CountClausesForMatsuiStrategy( Wvars, Uvars,Probability,LeftNode,RightNode,mm,count_clause_num)



    file = open("Problem-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf", "w")
    file.write("p cnf " + str(count_var_num) + " " + str(count_clause_num) + "\n")

    GenRoundConstrain(Round, xin,p,q,m,xout,file)
    GenSequentialEncoding(Round, Probability,  Wvars, Uvars, file)
    if len(MatsuiRoundIndex) > 0:
        for matsuiroundindex in MatsuiRoundIndex:
            StartingRound = matsuiroundindex[0]
            EndingRound = matsuiroundindex[1]
            LeftNode = StartingRound * (48)
            RightNode = EndingRound * (48) - 1
            

            mm = Probability - ProbabilityBound[StartingRound] - ProbabilityBound[Round - EndingRound]
            GenMatsuiConstraint( Wvars, Uvars,Probability,LeftNode,RightNode,mm,file)
    file.close()


    time_start = time.time()

    order = "d:/solver/cadical-master/build/cadical " + "Problem-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf > Round" + str(Round) + "-Probability" + str(Probability) + "-solution.txt"
    os.system(order)
    time_end = time.time()


    (Result,Results)=ExtractionResults( "Round" + str(Round) + "-Probability" + str(Probability) + "-solution.txt")
  


    if (Result == "SATISFIABLE"):
        print("Round:" + str(Round) + "; Probability: " + str(Probability) + "; Sat; TotalCost: " + str(time_end - time_start))
    else:
        print("Round:" + str(Round) + "; Probability: " + str(Probability) + "; Unsat; TotalCost: " + str(time_end - time_start))


    fileResult = open("ProcessResult.txt", "a")
    if (Result == "SATISFIABLE"):
        fileResult.write("\n Round:" + str(Round) + "; Probability: " + str(Probability) + "; Sat; TotalCost: " + str(time_end - time_start)+ " p: " +str(count_var_num) +" cnf: " + str(count_clause_num))
    else:
        fileResult.write("\n Round:" + str(Round) + "; Probability: " + str(Probability) + "; Unsat; TotalCost: " + str(time_end - time_start)+ " p: " +str(count_var_num) +" cnf: " + str(count_clause_num))
    fileResult.close()

    order = "rm Problem-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf"
    os.system(order)

    return(Result,count_var_num,count_clause_num,time_end-time_start)
            

if __name__ == '__main__':

    Total_var_num = 0
    Total_clause_num =0
    Total_Solve_time = 0


    for totalround in range(SearchRoundStart, SearchRoundEnd+1):
        count_var_num = 0
        count_clause_num = 0
        count_time = 0

        Result = "UNSATISFIABLE"
        ProbabilityBound[totalround] = ProbabilityBound[totalround-1] + ProbabilityBound[1]

        MatsuiCount = 0
        MatsuiRoundIndex=[]
        for Round in range(1, totalround + 1):
            MatsuiRoundIndex.append([])
            MatsuiRoundIndex[MatsuiCount].append(0)
            MatsuiRoundIndex[MatsuiCount].append(Round)
            MatsuiCount += 1

        file = open("MatsuiCondition.out", "a")
        resultseq = "Round: " + str(totalround) + "; Partial Constraint Num: " + str(MatsuiCount) + "\n"
        file.write(resultseq)
        file.write(str(MatsuiRoundIndex) + "\n")
        file.close()
        
        while (Result == "UNSATISFIABLE"):
            (Result,var_num,clause_num,Time)  = Decision(totalround,MatsuiRoundIndex)

            count_var_num += var_num
            count_clause_num += clause_num
            count_time += Time

            if (Result == "SATISFIABLE"):
                break

            ProbabilityBound[totalround] += 1

     
        Total_var_num += count_var_num
        Total_clause_num += count_clause_num
        Total_Solve_time += count_time

        file = open("RunTimeSummarise.out", "a")
        resultseq = "Round: " + str(totalround) + "; Probability: " + str(ProbabilityBound[totalround]) + "; Runtime: " + str(count_time) + " count_var_num: " + str(count_var_num) + " count_clause_num: " + str(count_clause_num)  +"\n"
        file.write(resultseq)
        file.close()

    print(Total_Solve_time)
    print(str(ProbabilityBound))
    file = open("RunTimeSummarise.out", "a")
    resultseq = "Total Time of Solving SAT Model: " + str(Total_Solve_time) + " Total_var_num: " + str(Total_var_num) + " Total_clause_num" + str(Total_clause_num)
    file.write(resultseq)
    file.close()

