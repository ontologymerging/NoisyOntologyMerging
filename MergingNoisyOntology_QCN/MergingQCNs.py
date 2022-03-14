import sys
sys.path.insert(0, './PyRCC8')
from glob import setGlobals
from bitcoding import EQ, DALL
from iconsistency import iconsistency
from consistency import consistency
from assignment import staticUnassignedVars
from parsecsp import parsecsp
from parsecsp import parsecsp_Array
from optparse import OptionParser
from printm import printMatrix
from array import array
from PyRCC8.counters import conCount, arcCount, nodeCount
from printm import ChangeMatrixToList
from Translation_Between_EL_RCC5 import Tranlation_From_RCC5_To_EL
from Translation_Between_EL_RCC5 import Translation_From_EL_To_RCC5_SetOfOntologies
import itertools
BasicRelationRCC5 = ["DR","PO","PP","PPI","EQ"]
Concepts=[""]
ListOfConcepts=["T","P","B","D"]

#'''
Source1=[["P","is-a","T"],["T","dj","D"],["P","is-a","B"],["P","dj","D"],["B","dj","D"]]
Source2=[["P","is-a","T"],["T","is-a","B"],["D","is-a","B"],["D","is-a","P"]]
Source3=[["P","is-a","T"],["B","is-a","D"],["D","is-a","P"],["D","is-a","T"]]
Source4=[["D","dj","P"],["P","is-a","T"],["B","is-a","D"],["T","dj","B"],["T","dj","D"]]
ListOfOntologies=[Source1,Source2,Source3,Source4]
ListOfSources = Translation_From_EL_To_RCC5_SetOfOntologies(ListOfOntologies,ListOfConcepts)

ABox_Source1={"T":["t","p"],"P":["p"],"D":["d"],"B":["p","b"]}
ABox_Source2={"T":["t","p","d"],"P":["p","d"],"D":["d"],"B":["p","t","b","d"]}
ABox_Source3={"T":["t","p","b","d"],"P":["p","b","d"],"D":["b","d"],"B":["b"]}
ABox_Source4={"T":["p","t"],"P":["p"],"D":["b","d"],"B":["b"]}
ListOfAboxes = [ABox_Source1,ABox_Source2,ABox_Source3,ABox_Source4]
Distionary_Of_Distance={"DR":1, "PO":2,"PP":3,"PPI":3, "EQ":4}


#==================================================================
def PrintList(l):
    count=0
    for each in l:
        count+=1
        print("|",count, each)
def PrintDict(dict):
    for index, each in dict.items():
        print("|",index,": ", each)
#==================================================================
#-------------Fundamention Functions-----------------
#Dictionary to List
def Dictionary_to_List(Dictionary):
    ListOfConstraints = []
    for index, eachRelation in Dictionary.items():
        Name1 = "{0}".format(index[0])
        Name2 = "{0}".format(index[1])
        ListOfConstraints.append([Name1,eachRelation,Name2])
    return ListOfConstraints
#List to Distionary
def List_To_Dictionary(List):
    #Since the constraints are of the form ["NAME1",[RELATION],"NAME2"]
    #==> NAME1NAME2: [RELATION]
    Dictionary_Constraints={}
    for each in List:
        Name="{0}{1}".format(each[0],each[2])
        Dictionary_Constraints[Name] = each[1]
    return Dictionary_Constraints
#==================================================================
#------------------------------------------------------------------
# Computing Distances
#------------------------------------------------------------------
def ComputingDistance_BetweenTwoBasicRelations(BasicRelation1,BasicRelation2, Distionary_Of_Distance):
    if (BasicRelation1=="PP" and BasicRelation2=="PPI") or \
            BasicRelation1 == "PPI" and BasicRelation2 == "PP":
        return 2
    else:
        dist = abs(Distionary_Of_Distance.get(BasicRelation1) -Distionary_Of_Distance.get(BasicRelation2))
    return dist

def ComputingDistance_FromBasicRelationToConstraint(BasicRelation, Constraint, DistanceDistionary):
    ListOfDistance = []
    for eachBasicRelation in Constraint:
        dist = ComputingDistance_BetweenTwoBasicRelations(BasicRelation,eachBasicRelation,DistanceDistionary)
        ListOfDistance.append(dist)
    return min(ListOfDistance)

def ComputingDistance_FromBasicRelationToProfileConstraints(BasicRelation, ProfileConstraints, DistanceDistionary):
    ListOfDistance = []
    for Constraint in ProfileConstraints:
        dist = ComputingDistance_FromBasicRelationToConstraint(BasicRelation,Constraint,DistanceDistionary)
        ListOfDistance.append(dist)
    return sum(ListOfDistance)

def ComputingDistance_FromSetOfBasicReationsToProfileConstraints(SetOfBasicRelations, ProfileConstraints, DistanceDistionary):
    ListOfDistances=[]
    for eachBasicRelation in SetOfBasicRelations:
        dist = ComputingDistance_FromBasicRelationToProfileConstraints(eachBasicRelation,ProfileConstraints,DistanceDistionary)
        ListOfDistances.append(dist)
    return ListOfDistances

def Distionary_OfDistances_FromBtoSetOfConstraintProfiles(SetOfBasicRelations,SetOfConstraintProfiles,DistanceDistionary):
    ListOfDistances={}
    for eachConstraintProfileName, Constraints in SetOfConstraintProfiles.items():
        #print(eachConstraintProfileName,"-",Constraints)
        ListOfDists = ComputingDistance_FromSetOfBasicReationsToProfileConstraints(SetOfBasicRelations, Constraints, DistanceDistionary)
        ListOfDistances[eachConstraintProfileName] =ListOfDists
    return ListOfDistances
#==================================================================
#------------------------------------------------------------------
# Collecting Constraints from input sources
#------------------------------------------------------------------
def Normalization_Constraints(ListOfConcepts,Source,BasicRelationRCC5):
    ListOfConceptPair = list(itertools.combinations(ListOfConcepts,2))
    DistionaryOfSource = {}
    for eachConceptOfSource in Source:
        newName = "{0}{1}".format(eachConceptOfSource[0],eachConceptOfSource[2])
        DistionaryOfSource[newName]=eachConceptOfSource[1]
    NormalizationConstraints={}
    for eachPair in ListOfConceptPair:
        eachPairName = "{0}{1}".format(eachPair[0], eachPair[1])
        eachPairName_Inversely = "{0}{1}".format(eachPair[0], eachPair[1])
        if eachPairName in DistionaryOfSource.keys() or eachPairName_Inversely in DistionaryOfSource.keys():
            NormalizationConstraints[eachPairName]= DistionaryOfSource.get(eachPairName)
        else:
            NormalizationConstraints[eachPairName] = BasicRelationRCC5
    return NormalizationConstraints


def CollectingConstraints_FromInputSources(ListOfSources,BasicRelationRCC5):
    ListOfSetOfConstraint ={}
    ListOfConceptPair = list(itertools.combinations(ListOfConcepts, 2))
    Constraint_Sources=[]
    for eachSource in ListOfSources:
        Constraint_Sources.append(Normalization_Constraints(ListOfConcepts, eachSource, BasicRelationRCC5))
    for eachPair in ListOfConceptPair:
        eachPairName = "{0}{1}".format(eachPair[0], eachPair[1])
        ListOfSetOfConstraint[eachPairName] = []
        for eachSource in Constraint_Sources:
            ListOfSetOfConstraint[eachPairName].append(eachSource.get(eachPairName))
    return ListOfSetOfConstraint

def Standarding_NamesOfConstraints_toCheckConsistency(ListOfSetOfConstraint_Dict,ListOfConcepts):
    List_Constraints_StandardingNames=[]
    for eachName, constraint in ListOfSetOfConstraint_Dict.items():
        ListNames = ["{0}".format(ListOfConcepts.index(eachName[0])),"{0}".format(ListOfConcepts.index(eachName[1]))]
        for eRelation in constraint:
            if eRelation == "PPI":
                ListNames.extend(["NTPPI","TPPI"])
            if eRelation == "PP":
                ListNames.extend(["NTPP","TPP"])
            if eRelation == "DR":
                ListNames.extend(["DC","EC"])
            if eRelation == "PO":
                ListNames.extend(["PO"])
            if eRelation == "EQ":
                ListNames.extend(["EQ"])
        List_Constraints_StandardingNames.append(ListNames)
    return List_Constraints_StandardingNames

def Standarding_RCC8_To_RCC5(ListOfSetOfConstraint,ListOfConcepts):
    RCC8_To_RCC5={}
    for constraint in ListOfSetOfConstraint:
        name ="{0}{1}".format(ListOfConcepts[constraint[0]],ListOfConcepts[constraint[1]])
        ListNames=[]
        for eRelation in constraint[2]:
            if eRelation == "TPPI":
                ListNames.extend(["PPI"])
            if eRelation == "TPP":
                ListNames.extend(["PP"])
            if eRelation == "DC":
                ListNames.extend(["DR"])
            if eRelation == "PO":
                ListNames.extend(["PO"])
            if eRelation == "EQ":
                ListNames.extend(["EQ"])
        RCC8_To_RCC5[name] = ListNames
    return RCC8_To_RCC5

#===================================================================
#----------Check Consistency-----------------
def init_CheckConsistency(Array_Constraints):
    Vars = 4 #The number of Variable
    TypeId="Example"
    ConMatrix = tuple([array('B',[DALL if i != j else EQ for i in range(Vars)]) for j in range(Vars)])
    parsecsp_Array(ConMatrix,Array_Constraints)
    return TypeId, ConMatrix

def CheckInconsistency(Array_Constraints):
    TypeId, ConMatrix = init_CheckConsistency(Array_Constraints)
    Consistent=True
    setGlobals('split', 1)
    setGlobals('pcheuristic', 1)
    setGlobals('valheuristic', 1)
    setGlobals('varheuristic', 1)
    setGlobals('scope',0)
    setGlobals('process', 1)
    solution = consistency(ConMatrix)
    if solution == None:
        Consistent=False
        result=[]
    else:
        result = ChangeMatrixToList(solution)
    return result,Consistent
#===========================================

#==================================================================

print("-----------------------")
def Selection_RelationsForConstraints(BasicRelationRCC5,ListOfProfileDistances,ListOfConcepts):
    #Note: Since RCC5, the dimension of a set of constraint profile distances will also be 5.
    #In other words, each column of a set of constraint profile distances is corresponding to each constraint
    Collection_Constraints={}
    Array_Min=[]
    Array_Max = []
    for eachName, eachConstraintProfile in ListOfProfileDistances.items():
        Array_Max.append(max(eachConstraintProfile))
        Array_Min.append(min(eachConstraintProfile))
    while(True):
        indexMIN =0
        for eachName, eachConstraintProfile in ListOfProfileDistances.items():
            Collection_Constraints[eachName]=[]
            for index in range(len(eachConstraintProfile)):
                if Array_Min[indexMIN] >= eachConstraintProfile[index]:
                    Collection_Constraints[eachName].append(BasicRelationRCC5[index])
            indexMIN+=1
        # Check Inconsistent
        List_Constraints_StandardingNames = Standarding_NamesOfConstraints_toCheckConsistency(Collection_Constraints, ListOfConcepts)
        solution, Consistent = CheckInconsistency(List_Constraints_StandardingNames)
        if Consistent == 1:
            solution = Standarding_RCC8_To_RCC5(solution,ListOfConcepts)
            return solution
        else:
            CheckArray_Min = list(Array_Min)
            while(True):
                MaxOfMin = max(CheckArray_Min)
                if MaxOfMin != Array_Max[CheckArray_Min.index(MaxOfMin)]:
                    break
                if MaxOfMin == CheckArray_Min[CheckArray_Min.index(MaxOfMin)]:
                    CheckArray_Min.pop(CheckArray_Min.index(MaxOfMin))

            if MaxOfMin < Array_Max[Array_Min.index(MaxOfMin)]:
                Array_Min[Array_Min.index(MaxOfMin)]= Array_Min[Array_Min.index(MaxOfMin)]+1

#==========================================================================
#Spliting the merged QCN into quasi-atomic QCNs
def Spliting_QCN_to_QuasiAtomicQCN(SetOfConstraints):
    TranslatedConstraints=[["PP"],["PP","EQ"],["DR"],["PO"],["EQ"],["PPI"],["PPI","EQ"]]
    CollectingConstraints =[]
    SaveIndex=[]
    index=0
    for eachConstraint in SetOfConstraints:
        if eachConstraint[1] in TranslatedConstraints:
            index+=1
            SaveIndex.append(["%s"%index])
            CollectingConstraints.append(eachConstraint)
        else:
            TempIndex=[]
            for eachRCC in eachConstraint[1]:
                index+=1
                TempIndex.append("%s"%index)
                RCC5Constraint = [eachConstraint[0],[eachRCC],eachConstraint[2]]
                CollectingConstraints.append(RCC5Constraint)
            SaveIndex.append(TempIndex)

    CollectingQCNIndexes=[SaveIndex[0]]
    for i in range(1,len(SaveIndex)):
        K=[]
        for eachCollectingQCNIndexes in CollectingQCNIndexes:
            if len(SaveIndex[i])>1:
                for e in SaveIndex[i]:
                    Temp=[]
                    Temp = list(eachCollectingQCNIndexes)
                    Temp.append(e)
                    K.append(Temp)
            else:
                for e in SaveIndex[i]:
                    Temp = []
                    Temp = list(eachCollectingQCNIndexes)
                    Temp.extend(SaveIndex[i])
                    K.append(Temp)
        CollectingQCNIndexes = list(K)

    AllQuasi_AtomicQCNs=[]
    for eachQCNIndex in CollectingQCNIndexes:
        Temp=[]
        for eachConstraintIndex in eachQCNIndex:
            Temp.append(CollectingConstraints[int(eachConstraintIndex)-1])
        AllQuasi_AtomicQCNs.append(Temp)
    return AllQuasi_AtomicQCNs

#============================================================================
#============================================================================
def ComputingDistanceBetween_Constraint_ABox(AnABox,AConstraint):
    ABox_Concept1 = AnABox.get(AConstraint[0])
    Relation = AConstraint[1]
    ABox_Concept2 = AnABox.get(AConstraint[2])
    if Relation in [["PP"],["PP","EQ"]]:
        return len(set(ABox_Concept1).difference(ABox_Concept2))
    if Relation in [["PPI"], ["PPI", "EQ"]]:
        return len(set(ABox_Concept2).difference(ABox_Concept1))
    if Relation == ["PO"]:
        Left = len(set(ABox_Concept1).difference(ABox_Concept2))
        Right = len(set(ABox_Concept2).difference(ABox_Concept1))
        Middle = len(set(ABox_Concept2).intersection(ABox_Concept1))
        return max(Left,Right,Middle) - min(Left,Right,Middle)
    if Relation == ["EQ"]:
        Left = len(set(ABox_Concept1).difference(ABox_Concept2))
        Right = len(set(ABox_Concept2).difference(ABox_Concept1))
        return max(Left-Right,Right-Left)
    if Relation == ["DR"]:
        return len(set(ABox_Concept2).intersection(ABox_Concept1))

def ComputingDistanceBetween_AConstraint_SetOfABoxes(SetOfAboxes,AConstraint):
    Sum_Dist = 0
    for eachABox in SetOfAboxes:
        Sum_Dist+=ComputingDistanceBetween_Constraint_ABox(eachABox,AConstraint)
        #print(AConstraint,"--",ComputingDistanceBetween_Constraint_ABox(eachABox,AConstraint))
    #print("SUM:",Sum_Dist)
    #print("----------------------------")
    return Sum_Dist
def ComputingDistanceBetween_AQuasiAtomicQCN_SetOfABoxes(SetOfAboxes,AQuasiAtomicQCN):
    Sum_Dist = 0
    for eachConstraint in AQuasiAtomicQCN:
        Sum_Dist+=ComputingDistanceBetween_AConstraint_SetOfABoxes(SetOfAboxes,eachConstraint)
        #print("SUM:",Sum_Dist)

    return Sum_Dist
def ComputingDistanceBetween_SetOfQuasioAtomicQCNs_SetOfABoxes(SetOfAboxes, SetOfQuasiAtomicQCNs):
    ListofScenariosAndDistances=[]
    for Scenario in SetOfQuasiAtomicQCNs:
        ListofScenariosAndDistances.append([Scenario,ComputingDistanceBetween_AQuasiAtomicQCN_SetOfABoxes(SetOfAboxes,Scenario)])
    return ListofScenariosAndDistances

def Finding_Quasi_AtomicQCNs_with_ASetOfABox(ListOfAboxes,SetofQuasi_AtomicQCNs):
    AFinalQCN = []
    ListofScenariosAndDistances = ComputingDistanceBetween_SetOfQuasioAtomicQCNs_SetOfABoxes(ListOfAboxes, SetofQuasi_AtomicQCNs)
    #PrintList(ListofScenariosAndDistances)
    Min_Dist = min([each[1] for each in ListofScenariosAndDistances])
    for [eachScenario, dist] in ListofScenariosAndDistances:
        if Min_Dist == dist:
            AFinalQCN.append(eachScenario)
    if len(AFinalQCN)==1:
        return AFinalQCN[0]
    else:
        return AFinalQCN
#========================================================================================
#========================================================================================
SetOfConstraintProfiles=CollectingConstraints_FromInputSources(ListOfSources,BasicRelationRCC5)
ListOfProfileDistances = Distionary_OfDistances_FromBtoSetOfConstraintProfiles(BasicRelationRCC5,SetOfConstraintProfiles,Distionary_Of_Distance)
Result_MergedQCN = Selection_RelationsForConstraints(BasicRelationRCC5,ListOfProfileDistances,ListOfConcepts)
SetofQuasi_AtomicQCNs = Spliting_QCN_to_QuasiAtomicQCN(Dictionary_to_List(Result_MergedQCN))
AFinalQCN = Finding_Quasi_AtomicQCNs_with_ASetOfABox(ListOfAboxes,SetofQuasi_AtomicQCNs)
#-------------------------------------------------------------------------------
print("=====================================")
print("| The input Sources (Ontologies):")
PrintList(ListOfOntologies)
print("|--------------------\n|")
print("| The input Sources (QCNs):|")
PrintList(ListOfSources)
print("=====================================")
print("| The final merged QCN result:")
PrintList(AFinalQCN)
#print("--------------------")
#PrintDict(List_To_Dictionary(AFinalQCN))
print("-------Ontology---------")
PrintList(Tranlation_From_RCC5_To_EL(AFinalQCN))
print("\nNote: is-a: subsumption, dj: disjoint With")



#----------------------appendix--------------------------

'''
#---------------------------------
Source1 = [["T",["PPI","EQ"],"P"],["P",["DR"],"D"],["P",["PP","EQ"],"B"],["T",["DR"],"D"],["B",["DR"],"D"]]
Source2 = [["T",["PP","EQ"],"B"],["B",["PPI","EQ"],"D"],["T",["PPI","EQ"],"P"],["P",["PPI","EQ"],"D"]]
Source3 = [["T",["PPI","EQ"],"P"],["T",["PPI","EQ"],"D"],["B",["PP","EQ"],"D"],["P",["PPI","EQ"],"D"]]
Source4 = [["T",["PPI","EQ"],"P"],["T",["DR"],"D"],["T",["DR"],"B"],["P",["DR"],"D"],["B",["PP","EQ"],"D"]]
ListOfSources=[Source1,Source2,Source3,Source4]
#'''
'''
ABox_Source1={"T":["t","p"],"P":["p"],"D":["d"],"B":["p","b"]}
ABox_Source2={"T":["t","p"],"P":["p","d"],"D":["d"],"B":["p","b"]}
ABox_Source3={"T":["t","p"],"P":["p"],"D":["d"],"B":["b"]}
ABox_Source4={"T":["p","t"],"P":["p"],"D":["b","d"],"B":["b"]}
'''