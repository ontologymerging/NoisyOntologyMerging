from owlready2.namespace import PREDEFINED_ONTOLOGIES
from pysat.examples.rc2 import RC2
from pysat.formula import WCNF

def PrintDict(d):
    for index,each in d.items():
        print(index, each)
def PrintLict(l):
    dem=0
    for each in l:
        dem+=1
        print(dem, each)

def GeneratingListOfVariables(NbVariable=4):
    ListOfVariables={}
    RCC5 = ["EQ","DR","PO","PP","PPi"]
    dem=0
    for i in range(NbVariable):
        for j in range(i+1,NbVariable):
            for each in RCC5:
                dem=dem+1
                ListOfVariables[dem]=[i,j,each]
    return ListOfVariables

def getID(ListOfVariables, ValueX):
    for index, value in ListOfVariables.items():
        if value == ValueX:
            return index
    return 0

def Generating_CNF_SoftClauses(ListOfSoftClauses,ListOfVariables):
    ListOfCNFs=[]
    for eachEdge in ListOfSoftClauses:
        DNF=[]
        for eachContent in eachEdge:
            DNF.append(getID(ListOfVariables, eachContent))
        ListOfCNFs.append(DNF)
    return ListOfCNFs
#------------------------------------------------------------
def Generating_CNF_ALO_HardClause(NbVariable,ListOfVariables):
    ListOfCNFs=[]
    RCC5 = ["EQ","DR","PO","PP","PPi"]
    for i in range(NbVariable):        
        for j in range(i+1,NbVariable):
            DNF=[]
            for eachRelation in RCC5:
                ValueX=[i,j,eachRelation]
                DNF.append(getID(ListOfVariables,ValueX))
            ListOfCNFs.append(DNF)
    return ListOfCNFs
#--------------------------------------------------------------
def Generating_CNF_AMO_HardClause(NbVariable,ListOfVariables):
    ListOfCNFs_ALO = Generating_CNF_ALO_HardClause(NbVariable,ListOfVariables)
    ListOfCNFs=[]
    for eachPair in ListOfCNFs_ALO:
        n=len(eachPair)
        for i in range(n):
            for j in range(i+1,n):
                ListOfCNFs.append([-eachPair[i],-eachPair[j]])
    return ListOfCNFs
#-------------------------------------------------------------
def Collecting_HardClauses(ListOfCNFs_ALO,ListOfCNFs_AMO,Triples,ListOf10C_Triples):
    ListOfHardClauses = []
    ListOfHardClauses.extend(ListOfCNFs_ALO)
    ListOfHardClauses.extend(ListOfCNFs_AMO)
    for eachTriple in Triples:
        FORD_Clauses = CollectingFORD_HardClauses(eachTriple,ListOf10C_Triples)
        ListOfHardClauses.extend(FORD_Clauses)
    return ListOfHardClauses 
#-------------------------------------------------------------
ListOf10C_Triples=[
    [["EQ","PP"],["EQ","PP"],["DR","PO","PPi"]],
    [["EQ","PPi"],["PO","PPi"],["EQ","DR","PP"]],
    [["DR","PP"],["EQ","PO","PP"],["EQ","PPi"]],
    [["PO","PPi"],["EQ","DR","PPi"],["EQ","PP"]],
    [["EQ","PP"],["DR"],["EQ","PO","PP","PPi"]],
    [["EQ","DR","PPi"],["EQ","PPi"],["PO","PP"]],
    [["PO"],["EQ","PP"],["EQ","DR","PPi"]],
    [["DR"],["PPi"],["EQ","PO","PP","PPi"]],
    [["PPi"],["EQ","PO","PP","PPi"],["DR"]],
    [["EQ"],["PO","PP"],["EQ","DR","PPi"]],    
]
def CollectingFORD_HardClauses(ATriple,ListOf10C_Triples):
    LT = [[ATriple[0],ATriple[1]],[ATriple[1],ATriple[2]],[ATriple[0],ATriple[2]]]
    RCC5 = ["EQ","DR","PO","PP","PPi"]
    RCC5 = set(RCC5)
    ListOfCNFs=[]

    for eachTriple in ListOf10C_Triples:
        dem=0
        DNF=[]
        for eachEdge in eachTriple:            
            if len(eachEdge)==1:
                ValueX=[LT[dem][0],LT[dem][1],eachEdge[0]]
                DNF.append(-getID(ListOfVariables,ValueX))
            else:
                RemainingRCC5 = RCC5.difference(set(eachEdge))
                for eachRelation in RemainingRCC5:
                    ValueX=[LT[dem][0],LT[dem][1],eachRelation]
                    DNF.append(getID(ListOfVariables,ValueX))
            dem+=1
        ListOfCNFs.append(DNF)
    return ListOfCNFs
#-------------------------------------------------------------
def MakeFile_DMancs(FileName, SoftClauses, HardClauses,ListOfVariables):
    nb_Clauses = len(SoftClauses) + len(HardClauses)
    nb_Variable = len(ListOfVariables)
    soft=5
    hard=3
    threshold=3
    with open(FileName, 'w') as f:
        if threshold>0:
            f.writelines("p wcnf {0} {1} {2}\n".format(nb_Variable,nb_Clauses,threshold))
        else:
            f.writelines("p wcnf {0} {1}\n".format(nb_Variable,nb_Clauses))
            
        for eachDNF in SoftClauses:
            DNF=""
            for eachLine in eachDNF:
                DNF = "{0} {1}".format(DNF,eachLine)
            f.writelines("{0} {1} {2}\n".format(soft,DNF.lstrip(),0))
        for eachDNF in HardClauses:
            DNF=""
            for eachLine in eachDNF:
                DNF = "{0} {1}".format(DNF,eachLine)
            f.writelines("{0} {1} {2}\n".format(hard,DNF.lstrip(),0))

#-------------------------------------------------------------

NbVariable=4
ListOfVariables = GeneratingListOfVariables(NbVariable)
PrintDict(ListOfVariables)
print("-------------------------")
#ListOfSoftClauses=[
#    [[0,1,"EQ"],[0,1,"PO"]],
#    [[0,2,"EQ"],[0,2,"PP"]],
#    [[1,3,"DR"],[1,3,"PPi"]],
#    [[2,3,"PP"]]
#]
ListOfSoftClauses=[
    [[0,1,"PPi"],[0,1,"EQ"]],
    [[0,2,"DR"],[0,2,"PP"],[0,2,"PO"]],
    [[0,3,"DR"]],
    [[1,2,"PP"],[1,2,"EQ"]],
    [[1,3,"DR"],[1,3,"PO"],[1,3,"PP"],[1,3,"PPi"],[1,3,"EQ"]],
    [[2,3,"PP"],[2,3,"EQ"],[2,3,"PO"],[2,3,"PPi"]]
]
ListOfCNFs_SoftClauses = Generating_CNF_SoftClauses(ListOfSoftClauses,ListOfVariables)
PrintLict(ListOfCNFs_SoftClauses)
#----------------------------------------
Triples=[[0,1,2],[1,2,3],[0,1,3],[0,2,3]]
print("----------------------------")
ListOfCNFs_ALO = Generating_CNF_ALO_HardClause(NbVariable,ListOfVariables)
ListOfCNFs_AMO = Generating_CNF_AMO_HardClause(NbVariable,ListOfVariables)
ListOfCNFs_HardClauses = Collecting_HardClauses(ListOfCNFs_ALO,ListOfCNFs_AMO,Triples,ListOf10C_Triples)
#PrintLict(ListOfCNFs_HardClauses)
MakeFile_DMancs("Dataset1.cnf",ListOfCNFs_SoftClauses, ListOfCNFs_HardClauses,ListOfVariables)
print("Done!")

#--------------------------------------------

print("-----------------------------")
wcnf = WCNF(from_file="Dataset1.cnf")
print("Hard: ",wcnf.hard)
print("Soft: ",wcnf.soft)
print("Weight: ",wcnf.wght)
rc2 = RC2(wcnf)
#model1 = rc2.compute()
dem=0

print("------- Result ----------")
Res_RCC5=[]
for model in rc2.enumerate():
    dem=dem+1
    #print(dem,model, rc2.cost)
    Res=[]
    for each in model:
        if each>0:
            Res.append(ListOfVariables.get(each))
    print(dem,". ",Res,rc2.cost)
    Res_RCC5.append(Res)
print(rc2.oracle_time())
#print(rc2.minimize_core())
#print(rc2.get_core())