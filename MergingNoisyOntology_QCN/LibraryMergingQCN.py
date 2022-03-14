import sys
sys.path.insert(0, './PyRCC8')
from glob1 import setGlobals
from bitcoding import EQ, DALL
from iconsistency import iconsistency
from consistency import consistency
from assignment import staticUnassignedVars
from parsecsp import parsecsp
from parsecsp import parsecsp_Array
from optparse import OptionParser
from printm import printMatrix
from array import array
from counters import conCount, arcCount, nodeCount
from printm import ChangeMatrixToList
from Translation_Between_EL_RCC5 import Tranlation_From_RCC5_To_EL
from Translation_Between_EL_RCC5 import Translation_From_EL_To_RCC5_SetOfOntologies
from Translation_Between_EL_RCC5 import ClosureOfABoxComplyingWithTBox
from Translation_Between_EL_RCC5 import  ClosureOfSetOfABoxes_ComplyingWith_TBoxes
import ast
import itertools

#==============================================
BasicRelationRCC5 = ["DR","PO","PP","PPI","EQ"]
Distionary_Of_Distance={"DR":1, "PO":2,"PP":3,"PPI":3, "EQ":4}
#==========================================
# 3 pieces of important information: List of Concepts, Input Ontologies(List Of TBoxes, List Of ABoxes)
def Read_TBox_ABox(LinkTBox,LinkABox):
    ListOfTBoxes = []
    ListOfABoxes = []
    ListOfConcepts=[]
    index=0
    with open(LinkTBox) as file:
        for line in file:
            if index==0:
                ListOfConcepts = ast.literal_eval(line)
                index=1
            else:
                ListOfTBoxes.append(ast.literal_eval(line))
    with open(LinkABox) as file:
        for line in file:
            ListOfABoxes.append(ast.literal_eval(line))
    return ListOfConcepts, ListOfTBoxes,ListOfABoxes
#==================================================================
def PrintList(l):
    count=0
    for each in l:
        count+=1
        print("|",count, each)
def PrintDict(dict):
    for index, each in dict.items():
        print("|",index,"        \t: ", each)
#==================================================================
#-------------Fundamention Functions-----------------
#Dictionary to List
def Dictionary_to_List(Dictionary):
    ListOfConstraints = []
    for index, eachRelation in Dictionary.items():
        Name1 = "{0}".format(index[:index.find("+")])
        Name2 = "{0}".format(index[index.find("+")+1:])
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
# Computing Distance from basic relation (DR,PO,PP,PPi,EQ) to Constraints Of profiles
def Distionary_OfDistances_FromBtoSetOfConstraintProfiles(SetOfBasicRelations,SetOfConstraintProfiles,DistanceDistionary):
    ListOfDistances={}
    for eachConstraintProfileName, Constraints in SetOfConstraintProfiles.items():
        #print(eachConstraintProfileName,+,Constraints)
        ListOfDists = ComputingDistance_FromSetOfBasicReationsToProfileConstraints(SetOfBasicRelations, Constraints, DistanceDistionary)
        ListOfDistances[eachConstraintProfileName] =ListOfDists
    return ListOfDistances
#==================================================================
#------------------------------------------------------------------
# Collecting Constraints from input sources
#------------------------------------------------------------------
#Translating DL -> RCC5
def Normalization_Constraints(ListOfConcepts,Source,BasicRelationRCC5):
    ListOfConceptPair = list(itertools.combinations(ListOfConcepts,2))
    DistionaryOfSource = {}
    for eachConceptOfSource in Source:
        newName = "{0}+{1}".format(eachConceptOfSource[0],eachConceptOfSource[2])
        DistionaryOfSource[newName]=eachConceptOfSource[1]
    NormalizationConstraints={}
    for eachPair in ListOfConceptPair:
        eachPairName = "{0}+{1}".format(eachPair[0], eachPair[1])
        eachPairName_Inversely = "{1}+{0}".format(eachPair[0], eachPair[1])
        if eachPairName in DistionaryOfSource.keys() or eachPairName_Inversely in DistionaryOfSource.keys():
            NormalizationConstraints[eachPairName]= DistionaryOfSource.get(eachPairName)
        else:
            NormalizationConstraints[eachPairName] = BasicRelationRCC5
    return NormalizationConstraints

#Collecting All of constraints from input sources
def CollectingConstraints_FromInputSources(ListOfSources,BasicRelationRCC5,ListOfConcepts):
    ListOfSetOfConstraint ={}
    ListOfConceptPair = list(itertools.combinations(ListOfConcepts, 2))
    Constraint_Sources=[]
    for eachSource in ListOfSources:
        Constraint_Sources.append(Normalization_Constraints(ListOfConcepts, eachSource, BasicRelationRCC5))
    for eachPair in ListOfConceptPair:
        eachPairName = "{0}+{1}".format(eachPair[0], eachPair[1])
        ListOfSetOfConstraint[eachPairName] = []
        for eachSource in Constraint_Sources:
            ListOfSetOfConstraint[eachPairName].append(eachSource.get(eachPairName))
    return ListOfSetOfConstraint

#-------------transform between RCC-5 and RCC-8 to use library PyRCC8
def Standarding_NamesOfConstraints_toCheckConsistency(ListOfSetOfConstraint_Dict,ListOfConcepts):
    List_Constraints_StandardingNames=[]
    for eachName, constraint in ListOfSetOfConstraint_Dict.items():
        ListNames = ["{0}".format(ListOfConcepts.index(eachName[:eachName.find("+")])),"{0}".format(ListOfConcepts.index(eachName[eachName.find("+")+1:]))]
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
        name ="{0}+{1}".format(ListOfConcepts[constraint[0]],ListOfConcepts[constraint[1]])
        ListNames=[]
        for eRelation in constraint[2]:
            if eRelation == "TPPI": #TPPI and NTPPI --> PPI
                ListNames.extend(["PPI"])
            if eRelation == "TPP": #TPP and NTPP --> PP
                ListNames.extend(["PP"])
            if eRelation == "DC": # DC and EC  --> DR
                ListNames.extend(["DR"])
            if eRelation == "PO":
                ListNames.extend(["PO"])
            if eRelation == "EQ":
                ListNames.extend(["EQ"])
        RCC8_To_RCC5[name] = ListNames
    return RCC8_To_RCC5

#===================================================================
#Using PyRCC8 library
#----------Check Consistency-----------------
def init_CheckConsistency(Array_Constraints,ListOfConcepts):
    Vars = len(ListOfConcepts) #The number of Variable: 4
    #TypeId="Example"
    ConMatrix = tuple([array('B',[DALL if i != j else EQ for i in range(Vars)]) for j in range(Vars)])
    parsecsp_Array(ConMatrix,Array_Constraints)
    return ConMatrix#TypeId, ConMatrix

def CheckInconsistency(Array_Constraints,ListOfConcepts):
    ConMatrix = init_CheckConsistency(Array_Constraints,ListOfConcepts)
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
#==================================================================
#==================================================================
#Selecting the constraints from the MERGED QCN.
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
        solution, Consistent = CheckInconsistency(List_Constraints_StandardingNames,ListOfConcepts)
        #print("TEST",List_Constraints_StandardingNames)
        print("Min:",Array_Min)
        print("Max:",Array_Max)
        print("-----------------")
        if Consistent == 1:
            solution = Standarding_RCC8_To_RCC5(solution,ListOfConcepts)
            return solution
        else:

            CheckArray_Min = list(Array_Min)
            CheckArray_Max = list(Array_Max)
            print("CHECK:", CheckArray_Min)
            while(True):
                print("--->MIN:",CheckArray_Min)
                print("--->MAX:", CheckArray_Max)
                MaxOfMin = max(CheckArray_Min)
                print("MaxOfMin: ==>", MaxOfMin)
                print("ArrayMax: ==>", CheckArray_Max[CheckArray_Min.index(MaxOfMin)])
                if MaxOfMin != CheckArray_Max[CheckArray_Min.index(MaxOfMin)]:
                    break
                if MaxOfMin == CheckArray_Max[CheckArray_Min.index(MaxOfMin)]:
                    CheckArray_Min.pop(CheckArray_Min.index(MaxOfMin))
                    CheckArray_Max.pop(CheckArray_Max.index(MaxOfMin))

            if MaxOfMin < Array_Max[Array_Min.index(MaxOfMin)]:
                Array_Min[Array_Min.index(MaxOfMin)]= Array_Min[Array_Min.index(MaxOfMin)]+1

            #if MaxOfMin < Array_Max[Array_Min.index(MaxOfMin)]:
            #    Array_Min[Array_Min.index(MaxOfMin)]= Array_Min[Array_Min.index(MaxOfMin)]+1

def Selection_RelationsForConstraints1(BasicRelationRCC5,ListOfProfileDistances,ListOfConcepts):
    #Note: Since RCC5, the dimension of a set of constraint profile distances will also be 5.
    #In other words, each column of a set of constraint profile distances is corresponding to each constraint
    Collection_Constraints={}
    Dict_ListOfProfileDistances_Computing ={}
    ListOfMin={}
    ListOfMax = {}
    for name,Array in ListOfProfileDistances.items():
        order = sorted(Array)
        Dict_ListOfProfileDistances_Computing[name] = order
        ListOfMin[name]=order[0]
        ListOfMax[name] = (order[len(order)-1])
    #Note: Decreasing with the first element and increasing with the last element
    Dict_ListOfProfileDistances_Computing =  dict(sorted(Dict_ListOfProfileDistances_Computing.items(), key=lambda x: (-x[1][0],x[1][len(BasicRelationRCC5)-1])))
    PrintDict(Dict_ListOfProfileDistances_Computing)
    while(True):
        #print("========================================================================================================")
        for name, Distances in ListOfProfileDistances.items():
            Collection_Constraints[name] = []
            index=0
            for eachD in Distances:
                if eachD <= ListOfMin.get(name):
                    Collection_Constraints[name].append(BasicRelationRCC5[index])
                index += 1
        List_Constraints_StandardingNames = Standarding_NamesOfConstraints_toCheckConsistency(Collection_Constraints, ListOfConcepts)
        solution, Consistent = CheckInconsistency(List_Constraints_StandardingNames,ListOfConcepts)
        #print("---------------------------------------------------------------")
        #PrintDict(Collection_Constraints)
        #print("------Min-----")
        #print(ListOfMin)
        #print("------Max-----")
        #print(ListOfMax)
        if Consistent == 1:
            solution = Standarding_RCC8_To_RCC5(solution, ListOfConcepts)
            #print("Consistent")
            return solution
        else:
            for name, Dict in Dict_ListOfProfileDistances_Computing.items():
                if ListOfMin.get(name) < ListOfMax.get(name):
                    Temp={}
                    Temp[name] = ListOfMin.get(name)+1
                    ListOfMin.update(Temp)
                    break

#==========================================================================

#==========================================================================
#Spliting the merged QCN into quasi-atomic QCNs
def Spliting_QCN_to_QuasiAtomicQCN(SetOfConstraints):
    TranslatedConstraints=[["PP"],["PP","EQ"],["DR"],["PO"],["EQ"],["PPI"],["PPI","EQ"]]
    CollectingConstraints =[]
    SaveIndex=[]
    index=0
    #Indicate Index to splitting QCN into scenarios
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
    CollectingQCNIndexes=[]
    for element in itertools.product(*SaveIndex):
        CollectingQCNIndexes.append(element)
    #print("==>",CollectingQCNIndexes)
    AllQuasi_AtomicQCNs=[]
    for eachQCNIndex in CollectingQCNIndexes:
        Temp=[]
        for eachConstraintIndex in eachQCNIndex:
            Temp.append(CollectingConstraints[int(eachConstraintIndex)-1])
        AllQuasi_AtomicQCNs.append(Temp)
    return AllQuasi_AtomicQCNs

#============================================================================
# Using ABox Assertions to select the Quasi-atomic QCN
#============================================================================
#Computing Distances
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
        #print(eachConstraint,"Dist",ComputingDistanceBetween_AConstraint_SetOfABoxes(SetOfAboxes,eachConstraint))

    return Sum_Dist
def ComputingDistanceBetween_SetOfQuasioAtomicQCNs_SetOfABoxes(SetOfAboxes, SetOfQuasiAtomicQCNs):
    ListofScenariosAndDistances=[]
    for Scenario in SetOfQuasiAtomicQCNs:
        ListofScenariosAndDistances.append([Scenario,ComputingDistanceBetween_AQuasiAtomicQCN_SetOfABoxes(SetOfAboxes,Scenario)])
        #print("-------------------")
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
        return 1, AFinalQCN[0]
    else:
        return len(AFinalQCN), AFinalQCN

#===========================================================================
#===========================================================================
