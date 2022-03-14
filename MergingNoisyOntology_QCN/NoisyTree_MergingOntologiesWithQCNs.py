import sys
sys.path.insert(0, './PyRCC8')
from owlready2 import *
from zss import simple_distance, Operation, distance  # , Node
from pqgrams import Profile
import random
from operator import itemgetter
from simple_tree import Node
from asciitree import draw_tree
from FuncOfTree import Enumerating_InforOfTree_ByFC
from FuncOfTree import List_FromLeavesToRoot_byFC
from FuncOfTree import FindRoot
from FuncOfTree import CreateTree
from FuncOfTree import Swap_TwoNodes_CreateSemanticConflict
from FuncOfTree import CreateSemanticConflict_TwoNodes_Father
from FuncOfTree import CreateSemanticConflict_TwoNodes_Child
from FuncOfTree import CreateSemanticConflict_TwoNodes_Child_Itself
from FuncOfTree import CreateLogicalConflicts_TwoNodes_Father
from FuncOfTree import CreateLogicalConflicts_TwoNodes_Child
from FuncOfTree import CreateLogicalConflicts_TwoNodes_UnDeletion
from FuncOfTree import Swap_TwoNodes
from FuncOfTree import FindFather
from FuncOfTree import IdentifyFatherAndChild
from FuncOfTree import DeleteNode
from FuncOfTree import InsertNode
from FuncOfTree import Swap_TwoNodes
from FuncOfTree import FindNode
import copy
import time
import ast
# ============================
# =======================Merging ===========================
from LibraryMergingQCN import Translation_From_EL_To_RCC5_SetOfOntologies
from LibraryMergingQCN import CollectingConstraints_FromInputSources
from LibraryMergingQCN import BasicRelationRCC5
from LibraryMergingQCN import Distionary_OfDistances_FromBtoSetOfConstraintProfiles
from LibraryMergingQCN import Selection_RelationsForConstraints
from LibraryMergingQCN import Distionary_Of_Distance
from LibraryMergingQCN import Read_TBox_ABox
from LibraryMergingQCN import Standarding_NamesOfConstraints_toCheckConsistency
from LibraryMergingQCN import CheckInconsistency
from LibraryMergingQCN import Standarding_RCC8_To_RCC5
from LibraryMergingQCN import Selection_RelationsForConstraints1
from LibraryMergingQCN import Spliting_QCN_to_QuasiAtomicQCN
from LibraryMergingQCN import Dictionary_to_List
from LibraryMergingQCN import ClosureOfSetOfABoxes_ComplyingWith_TBoxes
from LibraryMergingQCN import Finding_Quasi_AtomicQCNs_with_ASetOfABox
from LibraryMergingQCN import Tranlation_From_RCC5_To_EL

# ============================

def PrintList(l):
    count = 0
    for each in l:
        count += 1
        print(count, each)

def PrintDict(dict):
    for index, each in dict.items():
        print(index, "         \a    \t:\t", each)

def GetConceptNameFromConcept(Concept):
    eachClassString = "{0}".format(Concept)
    LetterForSplitting = "."
    Position = eachClassString.index(LetterForSplitting)
    eachClassString = eachClassString[Position + len(LetterForSplitting):len(eachClassString)]
    return eachClassString


# PrintList(ListOfConcept_Source1)

def Collect_Father_Children_FromOntology(ListOfConcept_Source1):
    ListFC = []
    for eachClass in ListOfConcept_Source1:
        eachFatherString = GetConceptNameFromConcept(eachClass)
        for Child in list(onto1[eachFatherString].subclasses()):
            eachChildString = GetConceptNameFromConcept(Child)
            ListFC.append([eachChildString, eachFatherString])
        # Add the Father is "Thing"
        if len(list(onto1[eachFatherString].ancestors())) == 2:
            ListFC.append([eachFatherString, "Thing"])
    return ListFC


def AddThingIntoFC(ListFC, Root):
    TempListFC = list(ListFC)
    ArrayRoot = []
    for each in Root:
        ArrayRoot.append([each, "Thing"])
    TempListFC.extend(ArrayRoot)
    return TempListFC


def GetAShortName_ForArray(Arr):
    List_ShortNames = []
    for each in Arr:
        eachName = GetConceptNameFromConcept(each)
        List_ShortNames.append(eachName)
    return List_ShortNames


# ==================================
# -----------------------------
def Collecting_AtomicConceptsFrom_AllSources(ListOfSources):
    ListOfAtomicConcepts=[]
    #Relation=[["->"],["<-"],["="]]
    Relation = ["is-a","dj","->","<-","="]
    for eachSource in ListOfSources:
        for eachAxiom in eachSource:
            for eachConcept in eachAxiom:
                if eachConcept not in Relation:
                    ListOfAtomicConcepts.append(eachConcept)
    ListOfAtomicConcepts = list(dict.fromkeys(ListOfAtomicConcepts))
    return ListOfAtomicConcepts
def RemoveSymmetricalDuplicate(Arr):
    Temp = []
    for each in Arr:
        Temp.append(sorted(each))
    ListOfClasses = []
    for each in Temp:
        if each not in ListOfClasses:
            ListOfClasses.append(each)
    return ListOfClasses

def RemoveDuplicate(Arr):
    ListOfClasses = []
    for each in Arr:
        if each not in ListOfClasses:
            ListOfClasses.append(each)
    return ListOfClasses

def GetDisjointClasses(onto1):
    for each in list(onto1.disjoint_classes()):
        print(each)

def GetDisjointClasses_Selected(ListOfSelectedClasses):
    # PrintList(ListOfSelectedClasses)
    ListOfDisjointClasses_Selected = []
    ClassesForLogicalConflicts = []
    for eachSelectedClass in ListOfSelectedClasses:
        for each in list(onto1.disjoint_classes()):
            eachDisjointClass = GetAShortName_ForArray(each.entities)
            if eachSelectedClass in eachDisjointClass:
                ListOfDisjointClasses_Selected.append(eachDisjointClass)
                ClassesForLogicalConflicts.append(eachSelectedClass)

    ClassesForLogicalConflicts = list(set(ClassesForLogicalConflicts))
    ClassesForSemanticConflicts = list(set(ListOfSelectedClasses).difference(set(ClassesForLogicalConflicts)))
    return RemoveSymmetricalDuplicate(
        ListOfDisjointClasses_Selected), ClassesForLogicalConflicts, ClassesForSemanticConflicts

def Get_All_DisjointClasses(onto1):
    ListOfDisjointClasses=[]
    for each in list(onto1.disjoint_classes()):
        eachDisjointClass = GetAShortName_ForArray(each.entities)
        ListOfDisjointClasses.append(eachDisjointClass)
    return ListOfDisjointClasses

 #==================================================================================================================

def TakingLabels_FromNode(ListNode):
    ListOfLabels = []
    for each in ListNode:
        ListOfLabels.append(each.label)
    return ListOfLabels


def Collect_Nodes_AtEachLevel(Root, Tree):
    ArrayLevel = [Tree.get(Root[0])]
    count = 1
    ListOfNodes_AtEachLevel = {}
    ListOfNodes_AtEachLevel[count] = ArrayLevel
    while (len(ArrayLevel) > 0):
        Temp_Level = []
        for each in ArrayLevel:
            if len(each.children) > 0:
                Temp_Level.extend(each.children)
        ArrayLevel = list(Temp_Level)
        count += 1
        if len(Temp_Level) > 0:
            ListOfNodes_AtEachLevel[count] = Temp_Level
    return ListOfNodes_AtEachLevel



# ================================================
# ================= New Version ====================
# ================================================

def isFather(Node1, Node2, Tree):
    FatherNode2 = FindFather(Node(Node2.label), Tree)
    if Node1.label == FatherNode2.label:
        return True
    return False
# =================================================
# --------------------------

def Delecting_Duplication_Interpretation(Array):
    result = []
    for x in Array:
        if x not in result:
            result.append(x)
    return result


def FindLevelOfNode(Node, Root, Tree):
    Dict_Nodes_EachLevel = Collect_Nodes_AtEachLevel(Root, Tree)
    for name, ListOfNodes in Dict_Nodes_EachLevel.items():
        if Node in ListOfNodes:
            return name
    return -1


def isSubTree(ListOfNodes, Root, Tree):
    ListOfSeletion = []
    ListOfNodesNew = Delecting_Duplication_Interpretation(ListOfNodes)
    if len(ListOfNodes) == len(ListOfNodesNew):
        for eachNode in ListOfNodes:
            levelNode = FindLevelOfNode(eachNode, Root, Tree)
            ListOfSeletion.append([eachNode, levelNode])
        # print("+++>")
        # PrintList(ListOfSeletion)
        # print("============")
        ListOfSeletion = sorted(ListOfSeletion, key=itemgetter(1), reverse=True)
        PrintList(ListOfSeletion)
        print("------------")
        for i in range(0, len(ListOfSeletion) - 1):
            Flag = False
            for each in ListOfSeletion:
                if (each[1] == ListOfSeletion[i][1] - 1):
                    if FindFather(Node(ListOfSeletion[i][0]).label, Tree).label == each[0].label:
                        Flag = True
                        break

            if Flag == False:
                print("----------------")
                print("It is not a subtree")
                print("----------------")
                return False
        return True

    else:
        return False
    return False



def TranslatingFromStringToNode_List(ListOfNodesString):
    ListOfNodes = []
    for each in ListOfNodesString:
        ListOfNodes.append(Node(each))
    return ListOfNodes


def CollectingAxioms(ListOfNodes, Tree):
    ListOfAxioms = []
    for i in range(0, len(ListOfNodes)):
        for j in range(0, len(ListOfNodes)):
            if ListOfNodes[i] != ListOfNodes[j] and isFather(ListOfNodes[i], ListOfNodes[j], Tree) == True:
                #ListOfAxioms.append([ListOfNodes[j].label, "->", ListOfNodes[i].label])
                ListOfAxioms.append([ListOfNodes[j].label, "is-a", ListOfNodes[i].label])
    return ListOfAxioms


def RandomSelection(ListOfNeihborhoodNodes, NbrConcept):
    IndexSelection = random.sample(range(len(ListOfNeihborhoodNodes)), NbrConcept)
    ListOfNodes = []
    for each in IndexSelection:
        ListOfNodes.append(ListOfNeihborhoodNodes[each])
    return ListOfNodes

# ================Version 4========================

def Collect_ListOfNodes(Node1, Ontology):
    ListOfCollectingNodes = []
    if Node1.label != "Thing":
        ListOfChildrenOfNode = Ontology.search(subclass_of=Ontology[Node1.label])
        for each in ListOfChildrenOfNode:
            eachName = GetConceptNameFromConcept(each)
            ListOfCollectingNodes.append(eachName)
    return ListOfCollectingNodes


def DeleteInsertNode_new(OriginalTree, Node1, Node2):
    T2 = copy.deepcopy(OriginalTree)
    T2 = DeleteNode(Node1, T2)
    Temp = FindNode(Node2, T2)
    T2 = InsertNode(Node(Node1.label), T2, Node2, 1, len(Temp.children))
    return T2

def DeleteInsertNode(OriginalTree, Node1, Node2):
    T2 = copy.deepcopy(OriginalTree)
    T2 = DeleteNode(Node1, T2)
    T2 = InsertNode(Node(Node1.label), T2, Node2, 1, 0)
    return T2

def ModifyTree1(Tree, Node1, Node2):
    List_ModifiedTrees = []
    NewTree = DeleteInsertNode(Tree, Node(Node1.label), Node(Node2.label))
    List_ModifiedTrees.append(NewTree)
    NewTree = DeleteInsertNode(Tree, Node(Node2.label), Node(Node1.label))
    List_ModifiedTrees.append(NewTree)
    #print("AAAAA=====>:",List_ModifiedTrees)
    return List_ModifiedTrees


def NoisyTree1(OriginalTree, NodeA, Ontology, NbrTree=100,TypeOfDistance=0):
    #TypeOfDistance: 0:SimpleDistance(TED), 1: pq-grams Distance
    ListOfClosestTrees = []

    # -------------------------
    ListOfNeighborhoodNodes = Collect_ListOfNodes(NodeA, Ontology)
    ListOfPairNode = itertools.combinations(ListOfNeighborhoodNodes, 2)
    ListOfPairNode1 = copy.deepcopy(ListOfPairNode)
    ListOfPairNode1 = sorted(ListOfPairNode1, key=itemgetter(0))
    # PrintList(ListOfPairNode1)
    print("-----------------------")
    for eachPair in ListOfPairNode1:
        if eachPair[0] != "Thing" and eachPair[1] != "Thing":
            # print(eachPair)
            List_ModifiedTrees = ModifyTree1(OriginalTree, Node(eachPair[0]), Node(eachPair[1]))
            for eachTree in List_ModifiedTrees:
                if TypeOfDistance==0:
                    Dist = simple_distance(eachTree, OriginalTree)
                else:
                    Dist = Profile(eachTree).edit_distance(Profile(OriginalTree))
                if Dist > 0:
                    ListOfClosestTrees.append([eachTree, Dist])
    if len(ListOfClosestTrees) <= NbrTree:
        NbrTree = len(ListOfClosestTrees)
    ListOfClosestTrees = sorted(ListOfClosestTrees, key=itemgetter(1))
    ListOfClosestTrees = ListOfClosestTrees[0:NbrTree]
    PrintList(ListOfClosestTrees)
    return ListOfClosestTrees, ListOfNeighborhoodNodes


def Sorting_Nodes(ListofNodes):
    for i in range(len(ListofNodes)):
        for j in range(len(ListofNodes)):
            if ListofNodes[i].label < ListofNodes[j].label:
                Temp = ListofNodes[i]
                ListofNodes[i] = ListofNodes[j]
                ListofNodes[j] = Temp

    return ListofNodes


def ProfileSelection1(OriginalTree, NodeA, NbrConcept, NbrProfile, Ontology, NbrOriginalOntology=0, NbrTree=30,TypeOfDistance=0):
    ProfileMerging = []
    ListOfTreeProfile = []
    #(NbrTree - NbrOriginalOntology) : since adding the original Ontologies
    ListOfClosestTrees, ListOfNeighborhoodNodes = NoisyTree1(OriginalTree, NodeA, Ontology, NbrTree-NbrOriginalOntology,TypeOfDistance)
    ListOfNodes = []

    count = 0
    while True:
        if NbrConcept >= len(ListOfNeighborhoodNodes):
            NbrConcept = len(ListOfNeighborhoodNodes)
        ListOfNodes = RandomSelection(ListOfNeighborhoodNodes, NbrConcept)
        ListOfNodes = TranslatingFromStringToNode_List(ListOfNodes)
        if isSubTree(ListOfNodes, Root, OriginalTree) == True:
            break
        count += 1
        if count == 10000:
            break
    print("---Selecting {0} concepts---".format(NbrConcept))
    print(ListOfNodes)
    ListOfNodes = Sorting_Nodes(ListOfNodes)
    PrintList(ListOfNodes)
    print("------Before------", len(ListOfClosestTrees))
    for i in range(1, NbrOriginalOntology + 1):
        ListOfClosestTrees.insert(0, [OriginalTree, 0])

    PrintList(ListOfClosestTrees)
    print("-------After------", len(ListOfClosestTrees))
    # print(draw_tree(ListOfClosestTrees[0][0]))
    NbrProfile = NbrProfile + NbrOriginalOntology
    ListOfDisjointClasses = Get_All_DisjointClasses(onto1)
    count = 0
    if NbrProfile <= len(ListOfClosestTrees) and len(ListOfNodes) > 0:
        # for i in range(3,NbrProfile):
        for i in range(NbrProfile):
            count += 1
            # print(ListOfClosestTrees[i][0])
            ListOfAxioms = CollectingAxioms(ListOfNodes, ListOfClosestTrees[i][0])
            #Add Disjoint Relation
            for [each1, each2] in ListOfDisjointClasses:
                #if any(each1 in x for x in ListOfAxioms) and any(each2 in x for x in ListOfAxioms)\
                #        and not ([each1, "is-a", each2] in ListOfAxioms or [each2, "is-a", each1] in ListOfAxioms):
                #    ListOfAxioms.append([each1,"dj",each2]) ##print("New:",[each1,"dj",each2])
                #'''
                if any(each1 in x for x in ListOfAxioms) and any(each2 in x for x in ListOfAxioms):
                    ListOfAxioms.append([each1,"dj",each2]) ##print("New:",[each1,"dj",each2])
                if ([each1, "is-a", each2] in ListOfAxioms or [each2, "is-a", each1] in ListOfAxioms):
                    if [each1, "is-a", each2] in ListOfAxioms:
                        ListOfAxioms.remove([each1, "is-a", each2])
                        print("==>>>XOA:",[each1, "is-a", each2])
                    else:
                        ListOfAxioms.remove([each2, "is-a", each1])
                        print("==>>>XOA:", [each2, "is-a", each1])
                #'''
            #print("-->",ListOfAxioms)
            ProfileMerging.append(ListOfAxioms)
            ListOfTreeProfile.append(ListOfClosestTrees[i][0])
            print("-------------------------")
            print("*****{0}**********".format(count))
            print(ListOfAxioms)
            print("-------------------------")
    print("-------------")
    print("Nbr Of Concept:", NbrConcept)
    print("Nbr Of Trees (A profile):", NbrProfile)
    print("-------------")
    # PrintList(ProfileMerging)
    return ProfileMerging, ListOfTreeProfile


#---------------------------------------------------------------------------------------
def Generating_Pseudo_ABoxesFrom_ListOfSources(ListOfSources, ListOfConcepts):
    List_ABoxes=[]
    individual=97
    TempDict = {}
    for each in ListOfConcepts:
        TempDict[each] = ["{0}".format(chr(individual))]
        individual+=1
    for each in ListOfSources:
        List_ABoxes.append(TempDict)
    return List_ABoxes

#=============================================================================================================
#=============================================================================================================
def RemovingConstraints_FullBasicRelations(Result_MergedQCN):
    FinalResult_MergedQCN = {}
    for name, constraint in Result_MergedQCN.items():
        if len(constraint)<5:
            FinalResult_MergedQCN[name] = constraint
    return FinalResult_MergedQCN
#=============================================================================================================
#=============================================================================================================

start_time_allprograms = time.time()
#onto1 = get_ontology("C:\\Thanh\\Code\\Owlready2\\Dataset\\conference\\sigkdd.owl")
onto1 = get_ontology("C:\\Thanh\\Code\\Owlready2\\Dataset\\conference\\ConferenceF.owl")
#onto1 = get_ontology("C:\Thanh\Code\Owlready2\Dataset\Rim\Rim_Ontofarm\edas.owl")
#onto1 = get_ontology("C:\Thanh\Code\Owlready2\Dataset\Rim\Rim_Ontofarm\ekaw.owl")
#onto1 = get_ontology("C:\\Thanh\\Code\\Owlready2\\Dataset\\conference\\cmt.owl")
onto1.load()
ListOfConcept_Source1 = list(onto1.classes())
# -------------------------------------------
# ===========================================
ListFC = Collect_Father_Children_FromOntology(ListOfConcept_Source1)
ListOfFathers, ListOfChildren, ListOfLeaves, ListOf_IntermediateNodes, Root = Enumerating_InforOfTree_ByFC(ListFC)
ListFC = sorted(ListFC, key=itemgetter(0))
ListOfChildToRoot = List_FromLeavesToRoot_byFC(ListFC)

ListOfChildToRoot = sorted(ListOfChildToRoot, key=itemgetter(0))
# print(ListOfChildToRoot)
T2 = CreateTree(ListOfChildToRoot)
# print(draw_tree(T2))
ListOfDisjointClasses = Get_All_DisjointClasses(onto1)
# ====================================================
#Node1 = Node("Organisation")
#Node1 = Node("Scientific_Event")
Node1 = Node("Person")
#Node1 = Node("Written_contribution")
#Node1 = Node("Document")
ProfileMerging, ListOfTreeProfile = ProfileSelection1(T2, Node1,30, 5, onto1, NbrOriginalOntology=3,NbrTree=30,TypeOfDistance=0) #0:TED, 1: PQGRAM
print("-------------------------------")
#PrintList(ListOfDisjointClasses)
PrintList(ProfileMerging)
ListOfConcepts = Collecting_AtomicConceptsFrom_AllSources(ProfileMerging)
print(ListOfConcepts)
#'''
#======================================================================
#======================--Merging Ontologies--==========================
#======================================================================

print("-----------------------------------------")
ListOfOntologies = ProfileMerging
#ListOfConcepts, ListOfOntologies, ListOfAboxes = Read_TBox_ABox("./Dataset/TBox","./Dataset/ABox")
ListOfSources = Translation_From_EL_To_RCC5_SetOfOntologies(ListOfOntologies,ListOfConcepts)
SetOfConstraintProfiles=CollectingConstraints_FromInputSources(ListOfSources,BasicRelationRCC5,ListOfConcepts)
ListOfProfileDistances = Distionary_OfDistances_FromBtoSetOfConstraintProfiles(BasicRelationRCC5,SetOfConstraintProfiles,Distionary_Of_Distance)
print("-------------------------")
PrintDict(ListOfProfileDistances)
print("-------------------------")
Result_MergedQCN = Selection_RelationsForConstraints1(BasicRelationRCC5,ListOfProfileDistances,ListOfConcepts)
#PrintDict(Result_MergedQCN)
print("===============Result - QCNs====================")
PrintDict(Result_MergedQCN)
print("-------------*Extend - Remove*------------")
Result_MergedQCN = RemovingConstraints_FullBasicRelations(Result_MergedQCN)
print("===============--Split Quasi-Atomic QCNs====================")
SetofQuasi_AtomicQCNs = Spliting_QCN_to_QuasiAtomicQCN(Dictionary_to_List(Result_MergedQCN))
print("--------------{0} Quasi-Atomic QCNs------------".format(len(SetofQuasi_AtomicQCNs)))
#PrintList(SetofQuasi_AtomicQCNs)
print("----------------------------------")
List_Pseudo_ABoxes = Generating_Pseudo_ABoxesFrom_ListOfSources(ListOfOntologies,ListOfConcepts)
ListOfAboxes = ClosureOfSetOfABoxes_ComplyingWith_TBoxes(ListOfOntologies,List_Pseudo_ABoxes)
#PrintList(ListOfAboxes)
print("-------------RESULT - ONTOLOGY---------------")
NbrOfQCN, AFinalQCN = Finding_Quasi_AtomicQCNs_with_ASetOfABox(ListOfAboxes,SetofQuasi_AtomicQCNs)
if NbrOfQCN==1:
    print("-------Result: QCN--------")
    PrintList(AFinalQCN)
    print("-------Result: Ontology--------")
    PrintList(Tranlation_From_RCC5_To_EL(AFinalQCN))
else:
    PrintList(AFinalQCN)
#'''

#print(draw_tree(T2))
#Node1=Node("Accepted_contribution")
#Node2=Node("Submitted_contribution")
#Node3=Node("Camera_ready_contribution")
#Node4=Node("Reviewed_contribution")
#TNew = DeleteInsertNode(T2, Node1, Node2)
#TNew = DeleteInsertNode_new(T2, Node3, Node4)
#print(draw_tree(TNew))

#Alphabet = list(string.ascii_lowercase)