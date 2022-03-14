from owlready2 import *
#import rdflib
import numpy as np
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
import copy
import time
# =======================Merging ===========================
from ModelBasedMerging import Collecting_AtomicConceptsFrom_AllSources
from ModelBasedMerging import GeneratingAllInterpretation_AllCombination_Level
from ModelBasedMerging import Computing_Distance_From_Multi_Sources
from ModelBasedMerging import Selecting_InterpretationResults
from ModelBasedMerging import SIFAlgorithm
from ModelBasedMerging import Print_InitialInterpretation
from ModelBasedMerging import Finding_SyntacticResult
from ModelBasedMerging import Generating_AllInterpretation
from ModelBasedMerging import GeneratingInterpretation
from ModelBasedMerging import Collecting_AtomicConceptsFrom_OneSources
import ast
import networkx
import multiprocessing
from multiprocessing import Pool, freeze_support


# ============================

def PrintList(l):
    count = 0
    for each in l:
        count += 1
        print(count, each)


def PrintDict(dict):
    for index, each in dict.items():
        print(index, ": ", each)


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


def RandomlyChooseConcepts(ListOfConcepts, NbrSelection):
    # print("Nbr Of Conepts:", len(ListOfConcepts))
    ListRandomlySelectedConcept = random.choices(ListOfConcepts, k=NbrSelection)
    while (len(set(ListRandomlySelectedConcept)) < NbrSelection):
        NbrRemain = NbrSelection - len(set(ListRandomlySelectedConcept))
        Temp = random.choices(ListOfConcepts, k=NbrRemain)
        ListRandomlySelectedConcept = list(set(ListRandomlySelectedConcept))
        ListRandomlySelectedConcept.extend(Temp)
    return GetAShortName_ForArray(ListRandomlySelectedConcept)

def powerset(iterable):
    "powerset([1,2,3]) --> (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return list(chain.from_iterable(itertools.combinations(s, r) for r in range(len(s)+1)))[1:]
# ==================================
# -----------------------------

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


# ==================================================================================================================

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
                ListOfAxioms.append([ListOfNodes[j].label, "->", ListOfNodes[i].label])
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


def Collect_ListOfNodes_IncludingThing(Node1, Ontology):
    ListOfCollectingNodes = []
    if Node1.label == "Thing":
        for each in list(Ontology.classes()):
            eachName = GetConceptNameFromConcept(each)
            ListOfCollectingNodes.append(eachName)
    else:
        ListOfChildrenOfNode = Ontology.search(subclass_of=Ontology[Node1.label])
        for each in ListOfChildrenOfNode:
            eachName = GetConceptNameFromConcept(each)
            ListOfCollectingNodes.append(eachName)
    return ListOfCollectingNodes


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
    return List_ModifiedTrees


def NoisyTree1(OriginalTree, NodeA, Ontology, NbrTree=100, TypeOfDistance=0):
    # TypeOfDistance: 0:SimpleDistance(TED), 1: pq-grams Distance
    ListOfClosestTrees = []

    # -------------------------
    ListOfNeighborhoodNodes = Collect_ListOfNodes_IncludingThing(NodeA, Ontology)

    # ListOfNeighborhoodNodes = Collect_ListOfNodes(NodeA, Ontology)
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
                if TypeOfDistance == 0:
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


def ProfileSelection1(OriginalTree, NodeA, NbrConcept, NbrProfile, Ontology, NbrOriginalOntology=0, NbrTree=30,
                      TypeOfDistance=0):
    ProfileMerging = []
    ListOfTreeProfile = []
    # (NbrTree - NbrOriginalOntology) : since adding the original Ontologies
    ListOfClosestTrees, ListOfNeighborhoodNodes = NoisyTree1(OriginalTree, NodeA, Ontology,
                                                             NbrTree - NbrOriginalOntology, TypeOfDistance)
    ListOfNodes = []
    count = 0
    # if NodeA.label=="Thing":
    while True:
        if NbrConcept >= len(ListOfNeighborhoodNodes):
            NbrConcept = len(ListOfNeighborhoodNodes)
        ListOfNodes = RandomSelection(ListOfNeighborhoodNodes, NbrConcept)
        ListOfNodes = TranslatingFromStringToNode_List(ListOfNodes)
        print("-->", len(ListOfNodes), "---", NbrConcept, "---", ListOfNodes, )
        if isSubTree(ListOfNodes, Root, OriginalTree) == True:
            break
        count += 1
        if count == 1000:
            break
    #print("---Selecting {0} concepts---".format(NbrConcept))
    #print(ListOfNodes)
    ListOfNodes = Sorting_Nodes(ListOfNodes)
    PrintList(ListOfNodes)
    #print("------Before------", len(ListOfClosestTrees))
    for i in range(1, NbrOriginalOntology + 1):
        ListOfClosestTrees.insert(0, [OriginalTree, 0])

    #PrintList(ListOfClosestTrees)
    #print("-------After------", len(ListOfClosestTrees))
    # print(draw_tree(ListOfClosestTrees[0][0]))
    NbrProfile = NbrProfile + NbrOriginalOntology
    count = 0
    if NbrProfile <= len(ListOfClosestTrees) and len(ListOfNodes) > 0:
        # for i in range(3,NbrProfile):
        for i in range(NbrProfile):
            count += 1
            # print(ListOfClosestTrees[i][0])
            ListOfAxioms = CollectingAxioms(ListOfNodes, ListOfClosestTrees[i][0])
            ProfileMerging.append(ListOfAxioms)
            ListOfTreeProfile.append(ListOfClosestTrees[i][0])
            #print("-------------------------")
            #print("*****{0}**********".format(count))
            #print(ListOfAxioms)
            #print("-------------------------")
    #print("-------------")
    #print("Nbr Of Concept:", NbrConcept)
    #print("Nbr Of Trees (A profile):", NbrProfile)
    #print("-------------")
    # PrintList(ProfileMerging)
    return ProfileMerging, ListOfTreeProfile


def ReadFile_address(address):
    Array_ReadFile = []
    with open(address) as FileObj:
        for lines in FileObj:
            if len(lines) > 0 and lines != "\n":
                TempArray = ast.literal_eval(lines[:-1])
                Array_ReadFile.append(TempArray)
    return Array_ReadFile


def CollectingListOfAllInterpretations_FromFile(primaryConcept):
    n = len(primaryConcept)
    address = "Interpretation/Interpretations_{0}.txt".format(n)
    return ReadFile_address(address)


# ==================================================
# ==================================================

def CollectingListOfAxiomsFromOriginalOntologies(SetOfOntologies):
    ListOfAxioms = []
    for each in SetOfOntologies:
        ListOfAxioms.extend(each)
    ListOfAxioms = RemoveDuplicate(ListOfAxioms)
    return ListOfAxioms


def CheckConceptInAxioms(primaryConcept, Axiom):
    for each in primaryConcept:
        if each not in chain(*Axiom):
            return False
    return True


def GeneratingInterpretation_FromOntologies_ver2(SetOfOntologies):
    ListOfAxioms_From_InputOntologies = CollectingListOfAxiomsFromOriginalOntologies(SetOfOntologies)
    primaryConcept = Collecting_AtomicConceptsFrom_AllSources(SetOfOntologies)
    print("------------------")
    PrintList(ListOfAxioms_From_InputOntologies)
    print("------------------")
    print("Nodes (", len(primaryConcept), "): ", primaryConcept)
    print("------------------")
    ListOfAllInterpretations_Array = []
    NumberFlag = -1

    for i in range(1, len(ListOfAxioms_From_InputOntologies) + 1):
        ListOfCombinations = list(itertools.combinations(ListOfAxioms_From_InputOntologies, i))
        print(i)
        # PrintList(ListOfCombinations)
        start_time = time.time()
        ListOfInterpretations_Array = []
        for each in ListOfCombinations:
            if CheckConceptInAxioms(primaryConcept, each):
                Interpretation = Print_InitialInterpretation(primaryConcept)
                for iTemp in range(2):
                    for eachAxioms in each:
                        Interpretation = GeneratingInterpretation(eachAxioms, primaryConcept, Interpretation)
                ListOfInterpretations_Array.append(list(Interpretation.values()))
        print("Time:", (time.time() - start_time))
        # ListOfInterpretations_Array = RemoveDuplicate(ListOfInterpretations_Array)
        print("---------------")
        start_time = time.time()
        # ListOfAllInterpretation_Dictionary, ListOfInterpretations_Array = Generating_AllInterpretation(ListOfCombinations_FullConcepts, primaryConcept)

        SetOfDifferences = DeletingBetweenTwoArray(ListOfInterpretations_Array, ListOfAllInterpretations_Array)
        ListOfAllInterpretations_Array.extend(SetOfDifferences)
        print("Kich Thuoc", i, ":", len(ListOfCombinations), "--", len(ListOfInterpretations_Array), "--",
              len(ListOfAllInterpretations_Array))
        print("Time:", (time.time() - start_time))
        if NumberFlag == len(ListOfAllInterpretations_Array) and NumberFlag != 0:
            print("NumFlag:", NumberFlag)
            break
        else:
            NumberFlag = len(ListOfAllInterpretations_Array)

    print("Number of All Interpretations (RemoveDuplication):", len(ListOfAllInterpretations_Array))
    return ListOfAllInterpretations_Array


def DeletingBetweenTwoArray(Array, FullArrays):
    SetArray = []
    SetFullArrays = []
    for each in Array:
        SetArray.append("{0}".format(each))
    for each in FullArrays:
        SetFullArrays.append("{0}".format(each))
    Temp = set(SetArray).difference(set(SetFullArrays))
    Result = []
    for each in Temp:
        Result.append(ast.literal_eval(each))
    return Result


# ==========================Version 3=================================
# ---------------------------Version 3-------------------------
def ChangeFullName_to_CondensedName(ListOfNames):
    ListOfCondensedNames = []
    for each in ListOfNames:
        Name = GetConceptNameFromConcept(each)
        ListOfCondensedNames.append(Name)
    return ListOfCondensedNames


def ChangeNode_to_StringNames(ListOfNames_Nodes):
    ListOfStringName_From_Nodes = []
    for each in ListOfNames_Nodes:
        ListOfStringName_From_Nodes.append(each.label)
    return ListOfStringName_From_Nodes


def Selection_Percent_Classes(ontology, Percent):
    ListOfConcepts = list(ontology.classes())
    ListOfConcepts = ChangeFullName_to_CondensedName(ListOfConcepts)
    numListOfConcepts = int(round((len(ListOfConcepts)) * Percent / 100, 0))
    return random.sample(ListOfConcepts, k=numListOfConcepts)

def Selection_Percent_Classes_FromClasses(Classes, Percent):
    ListOfConcepts = ChangeFullName_to_CondensedName(Classes)
    numListOfConcepts = int(round((len(ListOfConcepts)) * Percent / 100, 0))
    return random.sample(ListOfConcepts, k=numListOfConcepts)


def Collecting_Children_Father_Siblings_OfNodes(ListOfSelectedConcepts_Percent, Tree):
    List_Collection_Nodes_And_RelatedNodes = []
    for each in ListOfSelectedConcepts_Percent:
        Dictionary_RelatedInformation = {}
        Dictionary_RelatedInformation["Node"] = each
        # ---Children--------
        ListOfChildren = Tree.get(each).children
        ListOfChildren = ChangeNode_to_StringNames(ListOfChildren)
        Dictionary_RelatedInformation["Children"] = ListOfChildren
        # -------Father-------
        FatherOfNode = FindFather(Node(each), Tree).label
        Dictionary_RelatedInformation["Father"] = FatherOfNode
        # ----Siblings----------
        ListOfSiblings = []
        for eachSibling in FindFather(Node(each), Tree).children:
            if each != eachSibling.label:
                ListOfSiblings.append(eachSibling.label)
        Dictionary_RelatedInformation["Sibling"] = ListOfSiblings
        List_Collection_Nodes_And_RelatedNodes.append(Dictionary_RelatedInformation)

    return List_Collection_Nodes_And_RelatedNodes


def CreateNoisyTreesFrom_ANode_and_RelatedNodes(List_Collection_Nodes_And_RelatedNodes, Tree):
    ListOfNoisyTrees = []
    # Swapping between two nodes (5 cases: N-F, F-C, F-S, N-C, C-S)
    for each in List_Collection_Nodes_And_RelatedNodes:
        # ---Swap Node and Father----
        if each.get("Father") != "Thing":
            NewTree = Swap_TwoNodes(Node(each.get("Node")), Node(each.get("Father")), Tree)
            ListOfNoisyTrees.append(NewTree)
            # ---Swap Father and Children-------
            for Children in each.get("Children"):
                NewTree = Swap_TwoNodes(Node(each.get("Father")), Node(Children), Tree)
                ListOfNoisyTrees.append(NewTree)
            # ---Swap Father and Siblings-------
            for Sibling in each.get("Sibling"):
                NewTree = Swap_TwoNodes(Node(each.get("Father")), Node(Sibling), Tree)
                ListOfNoisyTrees.append(NewTree)
        # ---Swap Node and Children----
        for Children in each.get("Children"):
            NewTree = Swap_TwoNodes(Node(each.get("Node")), Node(Children), Tree)
            ListOfNoisyTrees.append(NewTree)
        # ---Swap Children and Siblings-------
        for Sibling in each.get("Sibling"):
            for Children in each.get("Children"):
                NewTree = Swap_TwoNodes(Node(Sibling), Node(Children), Tree)
                ListOfNoisyTrees.append(NewTree)
    # Delecting and Inserting two nodes
    for each in List_Collection_Nodes_And_RelatedNodes:
        if each.get("Father") != "Thing":
            # Delete Father and Insert into Node
            NewTree = DeleteInsertNode(Tree, Node(each.get("Father")), Node(each.get("Node")))
            ListOfNoisyTrees.append(NewTree)
            for Children in each.get("Children"):
                # Delete Father and Insert into Children
                NewTree = DeleteInsertNode(Tree, Node(each.get("Father")), Node(Children))
                ListOfNoisyTrees.append(NewTree)
            for Sibling in each.get("Sibling"):
                # Delete Father and Insert into Sibling
                NewTree = DeleteInsertNode(Tree, Node(each.get("Father")), Node(Sibling))
                ListOfNoisyTrees.append(NewTree)
        for Sibling in each.get("Sibling"):
            NewTree = DeleteInsertNode(Tree, Node(Sibling), Node(each.get("Node")))
            ListOfNoisyTrees.append(NewTree)
            NewTree = DeleteInsertNode(Tree, Node(each.get("Node")), Node(Sibling))
            ListOfNoisyTrees.append(NewTree)
        for Sibling in each.get("Sibling"):
            for Children in each.get("Children"):
                NewTree = DeleteInsertNode(Tree, Node(Children), Node(Sibling))
                ListOfNoisyTrees.append(NewTree)
                NewTree = DeleteInsertNode(Tree, Node(Sibling), Node(Children))
                ListOfNoisyTrees.append(NewTree)
        # ---Swap Node and Children----
        for Children in each.get("Children"):
            NewTree = Swap_TwoNodes(Node(each.get("Node")), Node(Children), Tree)
            ListOfNoisyTrees.append(NewTree)
        # break
    return ListOfNoisyTrees



def NoisyTree2(OriginalTree, ListOfNoisyTrees, NbrTree=100, TypeOfDistance=0):
    # TypeOfDistance: 0:SimpleDistance(TED), 1: pq-grams Distance
    ListOfClosestTrees = []
    for eachTree in ListOfNoisyTrees:
        if TypeOfDistance == 0:
            Dist = simple_distance(eachTree, OriginalTree)
        else:
            Dist = Profile(eachTree).edit_distance(Profile(OriginalTree))
        if Dist > 0:
            ListOfClosestTrees.append([eachTree, Dist])
    if len(ListOfClosestTrees) <= NbrTree:
        NbrTree = len(ListOfClosestTrees)
    ListOfClosestTrees = sorted(ListOfClosestTrees, key=itemgetter(1))
    ListOfClosestTrees = ListOfClosestTrees[0:NbrTree]
    # PrintList(ListOfClosestTrees)
    return ListOfClosestTrees


def ProfileSelection_version2(OriginalTree, ontology, NbrProfile, ListOfClosestTrees, NbrOriginalOntology=0, NbrTree=30,
                              TypeOfDistance=0):
    ListOfNodes = list(ontology.classes())
    ListOfNodes = ChangeFullName_to_CondensedName(ListOfNodes)
    ListOfNodes = TranslatingFromStringToNode_List(ListOfNodes)
    # ListOfNodes.append(Node("Thing")) #================================================----> Tạm bỏ
    NbrConcept = len(ListOfNodes)
    ProfileMerging = []
    ListOfTreeProfile = []
    print("------Before------", len(ListOfClosestTrees))
    for i in range(1, NbrOriginalOntology + 1):
        ListOfClosestTrees.insert(0, [OriginalTree, 0])
    PrintList(ListOfClosestTrees)
    print("-------After------", len(ListOfClosestTrees))
    # print(draw_tree(ListOfClosestTrees[0][0]))
    NbrProfile = NbrProfile + NbrOriginalOntology
    count = 0
    # '''
    if NbrProfile <= len(ListOfClosestTrees) and len(ListOfNodes) > 0:
        # for i in range(3,NbrProfile):
        for i in range(NbrProfile):
            count += 1
            # print(ListOfClosestTrees[i][0])
            ListOfAxioms = CollectingAxioms(ListOfNodes, ListOfClosestTrees[i][0])
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


def CollectionSubsumption(SyntacticResult):
    ListOfSyntacticResult_Subsumption = []
    for each in SyntacticResult:
        if each[1] == "->":
            ListOfSyntacticResult_Subsumption.append([each[0], each[2]])
    return ListOfSyntacticResult_Subsumption


def FilterSubsumption_NotIn_OriginalTree(ListOfChildToRoot, List_SubsumptionResult):
    ListOfSubsumption_Result_Changed = []
    for each in List_SubsumptionResult:
        flag = 1
        for eachbranchOfTree in ListOfChildToRoot:
            if each[0] in eachbranchOfTree and each[1] in eachbranchOfTree:
                flag = 0
                # break
        if flag == 1:
            ListOfSubsumption_Result_Changed.append(each)
    return ListOfSubsumption_Result_Changed


def ModifyTree_With_ResultOfMerging(ListOfSubsumption_Result_Changed, Tree):
    NewTree = copy.deepcopy(Tree)
    for each in ListOfSubsumption_Result_Changed:
        print(each[0], each[1])
        NewTree = DeleteNode(Node(each[0]), NewTree)
        NewTree = InsertNode(Node(each[0]), NewTree, Node(each[1]), 1, 0)
    return NewTree

def Transform_ListOfAxioms_to_ListOfPair(ListOfAxioms):
    ListOfPairs=[]
    for each in ListOfAxioms:
        ListOfPairs.append([each[0],each[2]])
    return ListOfPairs

def Collecting_Concepts_From_FatherChildren(ListFC):
    ListOfConcepts=[]
    for each in ListFC:
        ListOfConcepts.append(each[0])
        ListOfConcepts.append(each[1])
    ListOfConcepts = RemoveDuplicate(ListOfConcepts)
    return ListOfConcepts

def is_subseq(a, b):
    if len(a) > len(b): return False
    start = 0
    for el in a:
        while start < len(b):
            if el == b[start]:
                break
            start = start + 1
        else:
            return False
    return True

def filter_partial_matches(sets):
     return [s for s in sets if all([not(is_subseq(s, ss)) for ss in sets if s != ss])]

def RemoveTransitiveAxioms_ver2(CollectingSubsumption):
    ListOfPairs = Transform_ListOfAxioms_to_ListOfPair(CollectingSubsumption)
    ListOfConcepts = Collecting_Concepts_From_FatherChildren(ListOfPairs)

    ListOfImplicitTransitiveAxioms=[]
    g = networkx.DiGraph(ListOfPairs)
    for concept1 in ListOfConcepts:
       for concept2 in ListOfConcepts:
           Res = list(networkx.all_simple_paths(g, concept1, concept2))
           if len(Res)>0 and len(Res[0])>2 and [concept1,"->",concept2] in CollectingSubsumption:
               longest = max(Res, key=len)
               ListOfImplicitTransitiveAxioms.append(longest)
               #print(".................")
               #print(concept1,"->",concept2,Res)
               #print()
               #print(longest)
               #print()
    #ListOfImplicitTransitiveAxioms = filter_partial_matches(ListOfImplicitTransitiveAxioms)
    Result=[]
    for each in ListOfImplicitTransitiveAxioms:
        Flag=True
        for AxiomsToCheck in ListOfImplicitTransitiveAxioms:
            if each[0] in AxiomsToCheck and each[len(each)-1] in AxiomsToCheck:
                #print("CHECKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKK")
                #print(each[len(each) - 1],each[0],AxiomsToCheck.index(each[len(each) - 1]) - AxiomsToCheck.index(each[0]))
                if AxiomsToCheck.index(each[len(each) - 1]) - AxiomsToCheck.index(each[0])<=1:
                    Flag=False
                    break
        if Flag==True:
            Result.append([each[0],"->",each[len(each)-1]])
    return Result

def CollectingListOfAxiomsFromOriginalOntologies_TwoArrays(SetOfOntologies, ListFC, RemoveTransition=True, RemoveSemanticConflict=False):
    ListOfAxioms = []
    for each in SetOfOntologies:
        ListOfAxioms.extend(each)
    ListOfAxioms = RemoveDuplicate(ListOfAxioms)
    Axioms_OriginalOntology = []
    for each in ListFC:
        Axioms_OriginalOntology.append([each[0], "->", each[1]])
    #print()
    if RemoveTransition:
        #print("$$$$$$$$$$$$$$$$$$$$$$$$$$$")
        ListOfTransitiveAxioms = RemoveTransitiveAxioms_ver2(ListOfAxioms)
        #print("List Of Transitive Axioms")
        #PrintList(ListOfTransitiveAxioms)
        #print("------------List Of Axioms (From Sources)--------------")
        #PrintList(ListOfAxioms)
        #print("---------List Of Axioms (REMOVE TRANSITIVE AXIOMS)-------------")
        ListOfAxioms = DeletingBetweenTwoArray(ListOfAxioms, ListOfTransitiveAxioms)
        #PrintList(ListOfAxioms)
        #print("$$$$$$$$$$$$$$$$$$$$$$$$$$$")
    #using Majority for finding a common set
    CommonSet=[]
    DifferentSet=[]
    Dictionary_EachAxiom =[]
    print("Len:", len(SetOfOntologies))
    for eachAxiom in ListOfAxioms:
        count=0
        for eachSource in SetOfOntologies:
            if eachAxiom in eachSource:
                count+=1
        Dictionary_EachAxiom.append([eachAxiom, count])
        if count>=(len(SetOfOntologies)/2):
            CommonSet.append(eachAxiom)
    Dictionary_EachAxiom = sorted(Dictionary_EachAxiom, key=itemgetter(1),reverse=True)
    CommonSet = sorted(CommonSet, key=itemgetter(1), reverse=True)
    for eachAxiom in ListOfAxioms:
        if eachAxiom not in CommonSet:
            DifferentSet.append(eachAxiom)
    #PrintList(DifferentSet)
    if RemoveSemanticConflict == True:
        #print("&&&&&&&&&&&&&&&&&&&&&&&&&")
        #print("~~~~~~~~~~~~~~~~~SEMANTIC CONFLICTS~~~~~~~~~~~~~~~~~~")
        ListOfAxioms_SemanticConflicts=[]
        for each in CommonSet:
            if [each[2],"->",each[0]] in DifferentSet:
                ListOfAxioms_SemanticConflicts.append([each[2],"->",each[0]])
        #PrintList(ListOfAxioms_SemanticConflicts)
        #########################--------------#LUU Y CHO DISTANCE-----------------------------

        DifferentSet = DeletingBetweenTwoArray(DifferentSet,ListOfAxioms_SemanticConflicts)
        #print("&&&&&&&&&&&&&&&&&&&&&&&&&")

    return ListOfAxioms, CommonSet, DifferentSet

def CollectingListOfAxioms_With_Concept(ListOfAxioms, Concept):
    ListOfAxioms_Collected_with_Concept=[]
    for each in ListOfAxioms:
        if each[0]== Concept or each[2] == Concept:
            ListOfAxioms_Collected_with_Concept.append(each)
    return ListOfAxioms_Collected_with_Concept




def GeneratingInterpretation_FromOntologies_ver3(SetOfOntologies, ListFC,RemoveTransition=True, RemoveSemanticConflict=True):
    ListOfAxioms_From_InputOntologies, CommonAxioms, DifferentAxioms = CollectingListOfAxiomsFromOriginalOntologies_TwoArrays(
        SetOfOntologies, ListFC,RemoveTransition, RemoveSemanticConflict)
    Concepts_Of_AllAxioms = Collecting_AtomicConceptsFrom_OneSources(ListOfAxioms_From_InputOntologies)
    Concepts_Of_CommonAxioms = Collecting_AtomicConceptsFrom_OneSources(CommonAxioms)
    Concepts_Of_DifferentAxioms = Collecting_AtomicConceptsFrom_OneSources(DifferentAxioms)
    primaryConcept = Collecting_AtomicConceptsFrom_AllSources(SetOfOntologies)

    print("All axioms: ", len(Concepts_Of_AllAxioms),Concepts_Of_AllAxioms)
    PrintList(ListOfAxioms_From_InputOntologies)
    print("------------------")
    print("Common Axioms: ", len(Concepts_Of_CommonAxioms), CommonAxioms)
    PrintList(CommonAxioms)
    print()
    print("Difference Axioms: ", len(Concepts_Of_DifferentAxioms), Concepts_Of_DifferentAxioms)
    PrintList(DifferentAxioms)

    '''
    print("----------AAAA-----------")
    
    Collecting_DictionaryOfAxioms_WithRemainingConcepts={}
    Collecting_ListOfAxioms_WithRemainingConcepts = []
    for each in list(set(Concepts_Of_DifferentAxioms).difference(Concepts_Of_CommonAxioms)):
        print(each)
        Collecting_ListOfAxioms_WithRemainingConcepts.append(CollectingListOfAxioms_With_Concept(DifferentAxioms,each)[0])
        if each not in Collecting_DictionaryOfAxioms_WithRemainingConcepts.keys():
            Collecting_DictionaryOfAxioms_WithRemainingConcepts[each]=[]
        Collecting_DictionaryOfAxioms_WithRemainingConcepts[each].append(CollectingListOfAxioms_With_Concept(DifferentAxioms,each)[0])
    print()
    PrintDict(Collecting_DictionaryOfAxioms_WithRemainingConcepts)
    print()
    PrintList(Collecting_ListOfAxioms_WithRemainingConcepts)
    print()
    print("Remaining Axioms in Different:")
    Remaining_InDifferentAxioms = DeletingBetweenTwoArray(DifferentAxioms,Collecting_ListOfAxioms_WithRemainingConcepts)
    PrintList(Remaining_InDifferentAxioms)
    
    TempListOfAxioms=[]
    #for each in Collecting_ListOfAxioms_WithRemainingConcepts:
        #TempListOfAxioms.append(powerset(each))
    print(Collecting_ListOfAxioms_WithRemainingConcepts)
    PrintList(powerset(Collecting_ListOfAxioms_WithRemainingConcepts))
    print("------------------------------")
    #PrintList(TempListOfAxioms)
    print()
    PrintList(list(itertools.product(*TempListOfAxioms)))
    Collecting_ListOfAxioms_WithRemainingConcepts = TempListOfAxioms
    List_Remaining_InDifferentAxioms = powerset(Remaining_InDifferentAxioms)
    print("00000000000000000000000000000000000000")
    for i in range(len(Remaining_InDifferentAxioms)+1):
        print(len(list(itertools.combinations(Remaining_InDifferentAxioms,i))))
    print("00000000000000000000000000000000000000")
    print(len(List_Remaining_InDifferentAxioms))
    print("00000000000000000000000000000000000000")
    Collecting_ListOfAxioms_WithRemainingConcepts.append(List_Remaining_InDifferentAxioms)
    #PrintList(Collecting_ListOfAxioms_WithRemainingConcepts)
    print("Danh sach can thu thap")
    print(len(list(itertools.product(*Collecting_ListOfAxioms_WithRemainingConcepts))))
    #print(len(list(itertools.product(*Collecting_ListOfAxioms_WithRemainingConcepts))))
   
    print("--------------------------")
    print("KHAC NHAU:", set(Concepts_Of_DifferentAxioms).difference(Concepts_Of_CommonAxioms))
    print()
    #print("All Axioms: ", len(Concepts_Of_AllAxioms), Concepts_Of_AllAxioms)
    #print("All Axioms: ", primaryConcept)
    #print("List of All Axioms of Ontologies")
    #PrintList(ListOfAxioms_From_InputOntologies)
    print("------------------")
    print("Nodes (", len(primaryConcept), "): ", primaryConcept)
    print("------------------")
    #'''
    ListOfAllInterpretations_Array = []
    NumberFlag = -1
    ListOfInterpretations_Array=[]
    for i in range(1, len(DifferentAxioms) + 1):
        # Only take combination from changes
        print("VAO")
        ListOfCombinations = list(itertools.combinations(DifferentAxioms, i))
        print("STARTING....", "Nbr of Combination:", len(ListOfCombinations))
        ListOfInterpretations_Array = []
        ChangeInterpretationTime=time.time()
        for each in ListOfCombinations:
            #Ket hop voi common axioms
            Temp = list(each)
            Temp.extend(CommonAxioms)
            #print("Nbr_Axioms: ",len(Temp))
            if CheckConceptInAxioms(primaryConcept, Temp):
                Interpretation = Print_InitialInterpretation(primaryConcept)
                for iTemp in range(3):
                    for eachAxioms in Temp:
                        Interpretation = GeneratingInterpretation(eachAxioms, primaryConcept, Interpretation)
                ListOfInterpretations_Array.append(list(Interpretation.values()))
        print("Time:", time.time()-ChangeInterpretationTime)

        print("---------------")
        SetOfDifferences = DeletingBetweenTwoArray(ListOfInterpretations_Array, ListOfAllInterpretations_Array)
        ListOfAllInterpretations_Array.extend(SetOfDifferences)
        print("Kich Thuoc", i, ":", len(ListOfCombinations), "--", len(ListOfInterpretations_Array), "--",
              len(ListOfAllInterpretations_Array))

        if NumberFlag == len(ListOfAllInterpretations_Array) and NumberFlag != 0:
            print("NumFlag:", NumberFlag)
            break
        else:
            NumberFlag = len(ListOfAllInterpretations_Array)
    #print("=============================================>", len(DifferentAxioms))
    if len(DifferentAxioms)==0:
        Interpretation = Print_InitialInterpretation(primaryConcept)
        for iTemp in range(2):
            for eachAxioms in CommonAxioms:
                Interpretation = GeneratingInterpretation(eachAxioms, primaryConcept, Interpretation)
        Temp_Array = []
        for name, each in Interpretation.items():
            Temp_Array.append(each)
        ListOfAllInterpretations_Array.append(Temp_Array)
    print("Number of All Interpretations (RemoveDuplication):", len(ListOfAllInterpretations_Array))
    return ListOfAllInterpretations_Array

#====================================================================

def Selection_Percent_OfList(List, Percent):
    Number_Of_DisjointClasses = int(round((len(List)*Percent/100),0))
    return random.sample(List,k=Number_Of_DisjointClasses)

def CreateNoisyTreesFrom_ANode_and_RelatedNodes_ComplexTree(List_Collection_Nodes_And_RelatedNodes, Tree,numberNoise=4):
    ListOfNoisyTrees = []
    # Swapping between two nodes (5 cases: N-F, F-C, F-S, N-C, C-S)
    randomlist = random.sample(range(1, 10), numberNoise)
    NewTree = copy.deepcopy(Tree)
    for each in List_Collection_Nodes_And_RelatedNodes:
        #randomlist = random.sample(range(1, 10), numberNoise)
        #print(randomlist)
        # ---Swap Node and Father----
        if each.get("Father") != "Thing":
            if 1 in randomlist:
                NewTree = Swap_TwoNodes(Node(each.get("Node")), Node(each.get("Father")), NewTree)
            # ---Swap Father and Children-------
            if 2 in randomlist:
                for Children in each.get("Children"):
                    NewTree = Swap_TwoNodes(Node(each.get("Father")), Node(Children), NewTree)
            # ---Swap Father and Siblings-------
            if 3 in randomlist:
                for Sibling in each.get("Sibling"):
                    NewTree = Swap_TwoNodes(Node(each.get("Father")), Node(Sibling), NewTree)
        # ---Swap Node and Children----
        if 4 in randomlist:
            for Children in each.get("Children"):
                NewTree = Swap_TwoNodes(Node(each.get("Node")), Node(Children), NewTree)
        # ---Swap Children and Siblings-------
        if 5 in randomlist:
            for Sibling in each.get("Sibling"):
                for Children in each.get("Children"):
                    NewTree = Swap_TwoNodes(Node(Sibling), Node(Children), NewTree)
        # Delecting and Inserting two nodes
        #for each in List_Collection_Nodes_And_RelatedNodes:
        if each.get("Father") != "Thing":
            # Delete Father and Insert into Node
            if 6 in randomlist:
                NewTree = DeleteInsertNode(NewTree, Node(each.get("Father")), Node(each.get("Node")))
            if 7 in randomlist:
                for Children in each.get("Children"):
                    # Delete Father and Insert into Children
                    NewTree = DeleteInsertNode(NewTree, Node(each.get("Father")), Node(Children))
            if 8 in randomlist:
                for Sibling in each.get("Sibling"):
                    # Delete Father and Insert into Sibling
                    NewTree = DeleteInsertNode(NewTree, Node(each.get("Father")), Node(Sibling))
        #for Sibling in each.get("Sibling"):
        #    NewTree = DeleteInsertNode(NewTree, Node(Sibling), Node(each.get("Node")))
        #    NewTree = DeleteInsertNode(NewTree, Node(each.get("Node")), Node(Sibling))
        if 9 in randomlist:
            for Sibling in each.get("Sibling"):
                for Children in each.get("Children"):
                    NewTree = DeleteInsertNode(NewTree, Node(Children), Node(Sibling))
                    NewTree = DeleteInsertNode(NewTree, Node(Sibling), Node(Children))
        ## ---Swap Node and Children----
        #for Children in each.get("Children"):
        #    NewTree = DeleteInsertNode(Node(each.get("Node")), Node(Children), NewTree)

    #print(draw_tree(NewTree))
        # break
    return NewTree#ListOfNoisyTrees


# ===================================================================
# Main Programming
# ===================================================================
import copy
onto1 = get_ontology("C:\\Thanh\\Code\\Owlready2\\Dataset\\conference\\sigkdd.owl")
# onto1 = get_ontology("C:\\Thanh\\Code\\Owlready2\\Dataset\\conference\\Conference.owl")
# onto1 = get_ontology("C:\Thanh\Code\Owlready2\Dataset\Rim\Rim_Ontofarm\iasted.owl")
# onto1 = get_ontology("C:\Thanh\Code\Owlready2\Dataset\Rim\Rim_Hydrography\swo.owl")
#onto1 = get_ontology("C:\Thanh\Code\Owlready2\Dataset\Rim\Rim_Biodiv\sweet.owl")
# onto1 = get_ontology("C:\Thanh\Code\Owlready2\Dataset\Rim\Rim_Ontofarm\ekaw.owl")
# onto1 = get_ontology("C:\Thanh\Code\Owlready2\Dataset\Rim\Rim_Ontofarm\conference-2.owl")
#onto1 = get_ontology("C:\Thanh\Code\Owlready2\Dataset\Rim\Rim_Ontofarm\cmt-2-1.owl")
#onto1 = get_ontology("C:\Thanh\Code\Owlready2\Dataset\Rim\Rim_Ontofarm\cmt-2.owl")
#onto1 = get_ontology("cmt-2.owl")

# onto1 = get_ontology("C:\\Thanh\\Code\\Owlready2\\Dataset\\conference\\cmt.owl")
onto1.load()
ListOfConcept_Source1 = list(onto1.classes())
Classes = copy.deepcopy(ListOfConcept_Source1)

# ------------------------------
# ===========================================
ListFC = Collect_Father_Children_FromOntology(ListOfConcept_Source1)
ListOfFathers, ListOfChildren, ListOfLeaves, ListOf_IntermediateNodes, Root = Enumerating_InforOfTree_ByFC(ListFC)
ListFC = sorted(ListFC, key=itemgetter(0))
ListOfChildToRoot = List_FromLeavesToRoot_byFC(ListFC)

ListOfChildToRoot = sorted(ListOfChildToRoot, key=itemgetter(0))
T2 = CreateTree(ListOfChildToRoot)
# ====================================================
#print(draw_tree(T2))
# ----------------------------------------------
# ==============================================



#============================Noisy  Tree====================================================

def FunctionGeneratingNoisyTrees(Percent):
    Classes_Selected = Selection_Percent_Classes_FromClasses(Classes,Percent=Percent)
    List_Collection_Nodes_And_RelatedNodes = Collecting_Children_Father_Siblings_OfNodes(Classes_Selected , T2)
    NoisyTree = CreateNoisyTreesFrom_ANode_and_RelatedNodes_ComplexTree(List_Collection_Nodes_And_RelatedNodes, T2)
    return NoisyTree
def FunctionGeneratingNoisyTree_NumberTree(numTree,Threshosh_Distance, percent):
    ListOfNoisyTrees_Collection=[]

    while(len(ListOfNoisyTrees_Collection)<numTree):
        Num_CPU = multiprocessing.cpu_count()
        List_Percentage=[]
        for i in range(Num_CPU):
            List_Percentage.append(percent)
        #ListOfNoisyTrees = FunctionGeneratingNoisyTrees(percent)
        with Pool(Num_CPU) as p:
            ListOfNoisyTrees= p.map(FunctionGeneratingNoisyTrees,List_Percentage)
        #if ListOfNoisyTrees!=Node:
        #    continue
        for each in ListOfNoisyTrees:
            dist = simple_distance(each, T2)
            if dist<Threshosh_Distance and dist!=0:
                ListOfNoisyTrees_Collection.append([each,dist])
        print("-------------------------")
        PrintList(ListOfNoisyTrees_Collection)
    ListOfNoisyTrees_Collection = sorted(ListOfNoisyTrees_Collection, key=itemgetter(1), reverse=False)
    PrintList(ListOfNoisyTrees_Collection)
    return ListOfNoisyTrees_Collection[:numTree]
#============================================================================================
# ==============================================
# ----------------------------------------------

#"""
#ListOfClosestTrees = FunctionGeneratingNoisyTree_NumberTree(numTree=10, Threshosh_Distance=15, percent=20)
#PrintList(ListOfClosestTrees)
if __name__ == '__main__':
    freeze_support()
    #ListOfClosestTrees = FunctionGeneratingNoisyTree_NumberTree(numTree=10, Threshosh_Distance=20, percent=20)
    
    ListOfMergedTrees = []
    ListOfMergedTrees_Result2 = []
    dem = 0
    NumberofMergedTrees = 5
    NumberOfNoisyTrees=3
    ManyNoisyTrees=True
    AllTime= time.time()
    print("Number of Nodes:", len(Classes))
    while (dem < NumberofMergedTrees):
        dem += 1
        GeneratingTreeTime = time.time()
        print()
        print("========================Times: {0}========================".format(dem))
        print()
        NoisyTime = time.time()
        ListOfClosestTrees = FunctionGeneratingNoisyTree_NumberTree(numTree=10, Threshosh_Distance=20, percent=10)
        ProfileMerging, ListOfTreeProfile = ProfileSelection_version2(T2, onto1, 4, ListOfClosestTrees,
                                                                      NbrOriginalOntology=3)

        # ListOfAxioms, CommonAxioms, DifferentAxioms = CollectingListOfAxiomsFromOriginalOntologies_TwoArrays(ProfileMerging,ListFC)
        print(" ==> Generating Noisy Tree Time:", (time.time() - NoisyTime))
        PrintList(ListOfClosestTrees)

        # ====================================================================
        # ---------------------Merging-------------------------
        # ======================================================================
        MergingTime = time.time()
        primaryConcept = Collecting_AtomicConceptsFrom_AllSources(ProfileMerging)
        print("--->Interpretation. Loading...")

        print("**************************REMOVE TRANSITION =  TRUE******************************")
        ListOfInterpretations = GeneratingInterpretation_FromOntologies_ver3(ProfileMerging, ListFC,RemoveTransition=True,RemoveSemanticConflict=False)
        # ListOfInterpretations = GeneratingInterpretation_FromOntologies_ver2(ProfileMerging)
        #PrintList(ListOfInterpretations)
        print("---> Done!. Interpretation Loading.")
        print("---> Merging Process is starting...")
        print("Computing Distance From Multi-Sources")
        ListOfInterpretations_Distance = Computing_Distance_From_Multi_Sources(ProfileMerging, ListOfInterpretations,
                                                                               primaryConcept)
        if len(ListOfInterpretations)==0:
            dem=dem-1
            continue
        Top1 = ListOfInterpretations_Distance[0]
        closestdistance = Top1[len(Top1) - 1]
        print(" ==> DISTANCE: ",closestdistance)
        #PrintList(ListOfInterpretations_Distance)
        ResultInterpretation = Selecting_InterpretationResults(ListOfInterpretations_Distance, coefficient=closestdistance)
        #ResultInterpretation = Selecting_InterpretationResults(ListOfInterpretations_Distance, coefficient=0)
        print("-----------------List Of Interpretation Results----------------")
        #PrintList(ResultInterpretation)
        print("================= RESULT ===================")
        print("List of Atomic Concepts: ", primaryConcept)
        print("-----------------------------------------")
        SemanticResult = SIFAlgorithm(ResultInterpretation, primaryConcept)
        print("The Initial Interpretation:", Print_InitialInterpretation(primaryConcept))
        print("-------------------")
        print("Semantic Result: ", SemanticResult)
        # Remove Transitive Paths
        SyntacticResult = Finding_SyntacticResult(ProfileMerging, SemanticResult, primaryConcept,
                                                  SelectionConjunctionDisjunction=0)  # 1: Union, O: Intersection
        SyntacticResult = sorted(SyntacticResult, key=itemgetter(0), reverse=False)
        print()
        #print("Syntactic Result: ")
        #PrintList(SyntacticResult)
        # print(draw_tree(T2))
        print()
        print("-------------------")
        #List_SubsumptionResult = CollectionSubsumption(SyntacticResult)
        #ListOfSubsumption_Result_Changed = FilterSubsumption_NotIn_OriginalTree(ListOfChildToRoot, List_SubsumptionResult)
        #PrintList(ListOfSubsumption_Result_Changed)
        #NewTree = ModifyTree_With_ResultOfMerging(ListOfSubsumption_Result_Changed, T2)

        #Dist = simple_distance(T2, NewTree)
        #print("TED:", Dist)
        #DistPQGRAM = Profile(T2).edit_distance(Profile(NewTree))
        #print("PQGram:", DistPQGRAM)
        #ListOfMergedTrees.append([NewTree, Dist, DistPQGRAM])
        #ListOfMergedTrees_Result2.append([SyntacticResult, Dist])
        print("Merging Time:", (time.time() - MergingTime))
        print("Time of ({0}):".format(dem), (time.time() - GeneratingTreeTime))

    print("All Time:", (time.time() - AllTime))
    print("----------------------")
    '''
    PrintList(ListOfMergedTrees)
    ListOfMergedTrees = sorted(ListOfMergedTrees, key=itemgetter(1), reverse=False)
    ListOfMergedTrees_Result2 = sorted(ListOfMergedTrees_Result2, key=itemgetter(1), reverse=False)
    print()
    PrintList(ListOfMergedTrees)
    '''
#"""

#print("----------Draw Tree--------")
#print("--> Original Tree")
#print(draw_tree(T2))
#print("--> Merged Tree")
#print(draw_tree(ListOfMergedTrees[0][0]))

#print("-------------------")
#print(draw_tree(ListOfMergedTrees_Result2[0][0]))

# '''
#"""

'''
#A= [[1,2],[2,3],[4,5],[7,8],[8,2],[3,8],[7,6]]
A= [[1,2],[2,3],[4,5],[7,8],[8,2],[2,8],[7,6]]
#A= [[1,2],[2,3],[4,5],[7,8],[2,8],[3,6],[7,6],[1,6]]
#PrintList(List_FromLeavesToRoot_byFC(A))



import networkx
#ListOfFathers, ListOfChildren, ListOfLeaves, ListOf_IntermediateNodes, Root = Enumerating_InforOfTree_ByFC(A)
g = networkx.DiGraph(A)
#print("LEAF:", ListOfLeaves)
#print("Root:", Root)
Luu = []
for i in range(1,9):
    for j in range(1,9):
        #print(i,j)
        KQ = list(networkx.all_simple_paths(g, i, j))
        if len(KQ)>0 and len(KQ[0])>2:# and [i,j] in A:
            longest = max(KQ, key=len)
            print(i,j,"-",longest)
            print(i, j, "-", KQ)
            print()
            Luu.append(longest)
Luu = filter_partial_matches(Luu)
PrintList(Luu)
#'''

#a = [[1,2,3],["a","b"],[None,"#","@","$"]]
#PrintList(list(itertools.product(*a)))
'''
A=[]
for each in range(1,21):
    A.append(each)
print(A)
B=[]
for i in range(1,len(A)):
    #B.extend(list(itertools.combinations(A,i)))
    print("---------{0}---------".format(i))
    print(len(list(itertools.combinations(A,i))))
    print()

#PrintList(B)
#print(len(B))
#'''