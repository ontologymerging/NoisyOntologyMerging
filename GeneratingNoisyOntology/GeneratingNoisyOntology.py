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
import copy
# =======================Merging ===========================
# from ModelBasedMerging import Collecting_AtomicConceptsFrom_AllSources
# from ModelBasedMerging import GeneratingAllInterpretation_AllCombination_Level
# from ModelBasedMerging import Computing_Distance_From_Multi_Sources
# from ModelBasedMerging import Selecting_InterpretationResults
# from ModelBasedMerging import SIFAlgorithm
# from ModelBasedMerging import Print_InitialInterpretation
# from ModelBasedMerging import Finding_SyntacticResult
# from ModelBasedMerging import Generating_AllInterpretation
# from ModelBasedMerging import GeneratingInterpretation
# from ModelBasedMerging import Collecting_AtomicConceptsFrom_OneSources
# from ModelBasedMerging import GeneratingInterpretation_version2
# from ModelBasedMerging import Deleting_Individuals_Duplication
import ast
import networkx
import multiprocessing
from multiprocessing import Pool, freeze_support
from statistics import mean
import csv
#======================================================================

# ============================

def PrintList(l):
    count = 0
    for each in l:
        count += 1
        print(count, each)

def PrintList_Line(l):
    count = 0
    for each in l:
        count += 1
        print(count, each)
        print()

def PrintDict(dict):
    for index, each in dict.items():
        print(index, ": ", each)

def GetConceptNameFromConcept_New(Concept):
    eachClassString = "{0}".format(Concept)
    LetterForSplitting = "."
    Position = eachClassString.index(LetterForSplitting)
    eachClassString = eachClassString[Position + len(LetterForSplitting):len(eachClassString)-1]
    return eachClassString

def Collect_Father_Children_FromOntology(ListOfConcept_Source1,onto1):
    ListFC = []
    dem=0
    for eachClass in ListOfConcept_Source1:
        eachFatherString = GetConceptNameFromConcept(eachClass)
        dem+=1
        #print(dem,eachFatherString)
        try:
            for Child in list(onto1[eachFatherString].subclasses()):
                eachChildString = GetConceptNameFromConcept(Child)
                ListFC.append([eachChildString, eachFatherString])
            # Add the Father is "Thing"
            if len(list(onto1[eachFatherString].ancestors())) == 2:
                ListFC.append([eachFatherString, "Thing"])
        except:
            #print("LOI:"+ eachFatherString)
            continue

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
def GetConceptNameFromConcept(Concept):
    eachClassString = "{0}".format(Concept)
    LetterForSplitting = "."
    Position = eachClassString.index(LetterForSplitting)
    eachClassString = eachClassString[Position + len(LetterForSplitting):len(eachClassString)]
    return eachClassString

def isFather(Node1, Node2, Tree):
    try:
        FatherNode2 = FindFather(Node(Node2.label), Tree)
        if Node1.label == FatherNode2.label:
            return True
    except:
        return False
    return False
# PrintList(ListOfConcept_Source1)

def Collect_Father_Children_FromOntology(ListOfConcept_Source1):
    ListFC = []
    dem=0
    for eachClass in ListOfConcept_Source1:
        eachFatherString = GetConceptNameFromConcept(eachClass)
        dem+=1
        #print(dem,eachFatherString)
        try:
            for Child in list(onto1[eachFatherString].subclasses()):
                eachChildString = GetConceptNameFromConcept(Child)
                ListFC.append([eachChildString, eachFatherString])
            # Add the Father is "Thing"
            if len(list(onto1[eachFatherString].ancestors())) == 2:
                ListFC.append([eachFatherString, "Thing"])
        except:
            #print("LOI:"+ eachFatherString)
            continue

    return ListFC

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

#======================================================

def DeleteInsertNode(OriginalTree, Node1, Node2):
    Tree = copy.deepcopy(OriginalTree)
    Tree = DeleteNode(Node1, Tree)
    Tree = InsertNode(Node(Node1.label), Tree, Node2, 1, 0)
    return Tree

def DeleteInsertNode_Ontology(Ontology, Node1, Node2):
    print("-----------------------")
    print(Ontology[Node1],Ontology[Node2])
    print("-----------------------")
    #deleting Node1
    destroy_entity(Ontology[Node1])
    #Inserting Node1 into Node2
    with Ontology:
        types.new_class(Node1, (Ontology[Node2],))  # make a class
    return 1

def SwapBetweenTwoNodes_Ontology(Ontology, Node1, Node2, Tree):
    # print(">>>>",Node1,FindFather(Node(Node1), Tree))
    # print(">>>>",Node2,FindFather(Node(Node2), Tree))
    FatherOfNode1 = FindFather(Node(Node1),Tree)
    FatherOfNode2 = FindFather(Node(Node2),Tree)
    # print("000->",Node1,Node2)
    # print(len(list(Ontology.classes())))
    # print(Node1, "--",Ontology.get_parents_of(Ontology[Node1]))
    # print(Node2, "--",Ontology.get_parents_of(Ontology[Node2]))
    # if len(Ontology.get_parents_of(Ontology[Node1]))==0 or Ontology.get_parents_of(Ontology[Node1])==None:
    #     FatherOfNode1 = "Thing"
    # else:
    #     FatherOfNode1 = GetConceptNameFromConcept(Ontology.get_parents_of(Ontology[Node1])[0])
    #
    # if len(Ontology.get_parents_of(Ontology[Node2]))==0 or Ontology.get_parents_of(Ontology[Node2])==None:
    #     FatherOfNode2 = "Thing"
    # else:
    #     FatherOfNode2 = GetConceptNameFromConcept(Ontology.get_parents_of(Ontology[Node2])[0])
    print("============================")
    print("Node1:",Node1,"+",Ontology[Node1])
    print("Node2:",Node2,"+",Ontology[Node2])
    print("FatherNode1:",FatherOfNode1,"+",Ontology[FatherOfNode1])
    print("FatherNode2:",FatherOfNode2,"+",Ontology[FatherOfNode2])
    print("============================")

    destroy_entity(Ontology[Node1])
    destroy_entity(Ontology[Node2])
    with Ontology:
        if FatherOfNode2 == Node("Thing"):
            types.new_class(Node1, (Thing,))  # make a class
        else:
            types.new_class(Node1, (Ontology[FatherOfNode2],))  # make a class
        if FatherOfNode1 == Node("Thing"):
            types.new_class(Node2, (Thing,))  # make a class
        else:
            types.new_class(Node2, (Ontology[FatherOfNode1],))  # make a class
    return 1
# ==================================

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
        if Tree.get(each)!=None:
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

def CreateNoisyTreesFrom_ANode_and_RelatedNodes_ComplexTree_Ver2(List_Collection_Nodes_And_RelatedNodes, Tree,numberNoise=4):
    ListOfNoisyTrees = []
    ListOfModificationOfTree=[]
    # Swapping between two nodes (5 cases: N-F, F-C, F-S, N-C, C-S)
#    randomlist = random.sample(range(1, 10), numberNoise)
    NewTree = copy.deepcopy(Tree)
    #print(len(List_Collection_Nodes_And_RelatedNodes))
    #PrintList(List_Collection_Nodes_And_RelatedNodes)
    #dem=0
    for each in List_Collection_Nodes_And_RelatedNodes:
        randomlist = random.sample(range(1, 10), numberNoise)
        #dem=dem+1
        #print(len(randomlist), "--", randomlist)
        #print(randomlist)
        for rand in randomlist:

            #randomlist = random.sample(range(1, 10), numberNoise)
            #print(randomlist)
            #print("Node:",each.get("Node"),"Father: ",each.get("Father"))
            #print(each)
            #print("----------------")
            # ---Swap Node and Father----
            if each.get("Father") != "Thing":
                if rand == 1:
                    if each.get("Node")!=None and each.get("Father")!=None:
                        NewTree = Swap_TwoNodes(Node(each.get("Node")), Node(each.get("Father")), NewTree)
                        ListOfModificationOfTree.append([each.get("Node"),each.get("Father"),"SW"])
                # ---Swap Father and Children-------
                if rand == 2:
                    for Children in each.get("Children"):
                        if each.get("Father")!=None and Children!=None:
                            NewTree = Swap_TwoNodes(Node(each.get("Father")), Node(Children), NewTree)
                            ListOfModificationOfTree.append([each.get("Father"), Children, "SW"])
                # ---Swap Father and Siblings-------
                # if rand == 3:
                #     for Sibling in each.get("Sibling"):
                #         NewTree = Swap_TwoNodes(Node(each.get("Father")), Node(Sibling), NewTree)
                # ---Swap Node and Children----
                if rand == 4:
                    for Children in each.get("Children"):
                        if each.get("Node")!=None and Children!=None:
                            NewTree = Swap_TwoNodes(Node(each.get("Node")), Node(Children), NewTree)
                            ListOfModificationOfTree.append([each.get("Node"), Children, "SW"])
            # ---Swap Children and Siblings-------
            # if rand == 5:
            #     for Sibling in each.get("Sibling"):
            #         for Children in each.get("Children"):
            #             NewTree = Swap_TwoNodes(Node(Sibling), Node(Children), NewTree)
            # Delecting and Inserting two nodes
            #for each in List_Collection_Nodes_And_RelatedNodes:
            if each.get("Father") != "Thing":
                # Delete Father and Insert into Node
                if rand == 6:
                    if each.get("Node")!=None and each.get("Father")!=None:
                        NewTree = DeleteInsertNode(NewTree, Node(each.get("Father")), Node(each.get("Node")))
                        ListOfModificationOfTree.append([each.get("Father"), each.get("Node"), "DI"])
                if rand == 7:
                    for Children in each.get("Children"):
                        if each.get("Father")!=None and Children!=None:
                            # Delete Father and Insert into Children
                            NewTree = DeleteInsertNode(NewTree, Node(each.get("Father")), Node(Children))
                            ListOfModificationOfTree.append([each.get("Father"), Children, "DI"])
                # if rand == 8:
                #     for Sibling in each.get("Sibling"):
                #         # Delete Father and Insert into Sibling
                #         NewTree = DeleteInsertNode(NewTree, Node(each.get("Father")), Node(Sibling))
            #for Sibling in each.get("Sibling"):
            #    NewTree = DeleteInsertNode(NewTree, Node(Sibling), Node(each.get("Node")))
            #    NewTree = DeleteInsertNode(NewTree, Node(each.get("Node")), Node(Sibling))

            # if rand == 9:
            #     for Sibling in each.get("Sibling"):
            #         for Children in each.get("Children"):
            #             NewTree = DeleteInsertNode(NewTree, Node(Children), Node(Sibling))
            #             NewTree = DeleteInsertNode(NewTree, Node(Sibling), Node(Children))

            ## ---Swap Node and Children----
            #for Children in each.get("Children"):
            #    NewTree = DeleteInsertNode(Node(each.get("Node")), Node(Children), NewTree)

        #print(draw_tree(NewTree))
            # break
    
    return NewTree, ListOfModificationOfTree#ListOfNoisyTrees


def FunctionGeneratingNoisyTrees(Percent):
    Classes_Selected = Selection_Percent_Classes_FromClasses(Classes,Percent=Percent)
    List_Collection_Nodes_And_RelatedNodes = Collecting_Children_Father_Siblings_OfNodes(Classes_Selected , T2)
    NoisyTree,ListOfModificationOfTree = CreateNoisyTreesFrom_ANode_and_RelatedNodes_ComplexTree_Ver2(List_Collection_Nodes_And_RelatedNodes, T2)
    return NoisyTree

def FunctionGeneratingNoisyTrees_NoParallel(Percent,Classes,Tree):
    Classes_Selected = Selection_Percent_Classes_FromClasses(Classes,Percent=Percent)
    List_Collection_Nodes_And_RelatedNodes = Collecting_Children_Father_Siblings_OfNodes(Classes_Selected , Tree)
    NoisyTree,ListOfModificationOfTree = CreateNoisyTreesFrom_ANode_and_RelatedNodes_ComplexTree_Ver2(List_Collection_Nodes_And_RelatedNodes, Tree)
    return NoisyTree,ListOfModificationOfTree

def FunctionGeneratingNoisyTree_NumberTree(numTree,Threshosh_Distance, percent):

    ListOfNoisyTrees_Collection=[]
    ListOfDistances=[]

    while(len(ListOfNoisyTrees_Collection)<numTree):
        #print("VAO1")
        Num_CPU = multiprocessing.cpu_count()
        List_Percentage=[]
        for i in range(Num_CPU):
            List_Percentage.append(percent)
        #ListOfNoisyTrees = FunctionGeneratingNoisyTrees(percent)

        with Pool(Num_CPU) as p:
             ListOfNoisyTrees= p.map(FunctionGeneratingNoisyTrees,List_Percentage)

        #print("START")
        #ListOfNoisyTrees = FunctionGeneratingNoisyTrees(percent)
        #print("VAO2")
        #if ListOfNoisyTrees!=Node:
        #    continue
        #print(len(ListOfNoisyTrees),"--",ListOfNoisyTrees)
        for each in ListOfNoisyTrees:
            #print("Compute!!!")
            #dist = Profile(T2).edit_distance(Profile(each))
            dist = simple_distance(each, T2)
            print(dist)
            if dist<Threshosh_Distance and dist!=0:
                ListOfNoisyTrees_Collection.append([each,dist])
                ListOfDistances.append(dist)
        #print("-------------------------")
        print("---->Number of Collections:",len(ListOfNoisyTrees_Collection))
        #PrintList(ListOfNoisyTrees_Collection)
    ListOfNoisyTrees_Collection = sorted(ListOfNoisyTrees_Collection, key=itemgetter(1), reverse=False)
    PrintList(ListOfNoisyTrees_Collection)
    print("------------------------------------------------------")
    print ("Min", min(ListOfDistances))
    print("Max", max(ListOfDistances))
    print("Average:", mean(ListOfDistances))
    print("------------------------------------------------------")
    return ListOfNoisyTrees_Collection[:numTree]

def FunctionGeneratingNoisyTree_NumberTree_NoParallel(numTree,Threshosh_Distance, percent, Classes, Tree):

    ListOfNoisyTrees_Collection=[]
    ListOfDistances=[]

    while(len(ListOfNoisyTrees_Collection)<numTree):
        eachTree,ListOfModificationOfTree = FunctionGeneratingNoisyTrees_NoParallel(percent,Classes,Tree)
        dist = simple_distance(eachTree, Tree)
        print(dist)
        if dist < Threshosh_Distance and dist != 0:
            ListOfNoisyTrees_Collection.append([eachTree, dist,ListOfModificationOfTree])
            ListOfDistances.append(dist)

        print("---->Number of Collections:",len(ListOfNoisyTrees_Collection))
        #PrintList(ListOfNoisyTrees_Collection)
    ListOfNoisyTrees_Collection = sorted(ListOfNoisyTrees_Collection, key=itemgetter(1), reverse=False)
    PrintList(ListOfNoisyTrees_Collection)
    print("------------------------------------------------------")
    print ("Min", min(ListOfDistances))
    print("Max", max(ListOfDistances))
    print("Average:", mean(ListOfDistances))
    print("------------------------------------------------------")
    return ListOfNoisyTrees_Collection[:numTree]


def CreateOntologies(numberOfOntologies=3,file_path=""):
    OntoTest = get_ontology(file_path+"my_onto1.owl").load()
    for i in range(1,numberOfOntologies+1):
        file_path_Onto = file_path+"Check\\my_onto{0}.owl".format(i)
        while not os.path.exists(file_path_Onto):
            OntoTest.save(file=file_path_Onto)

def ExportNoisyOntologies(ListOfModifications, Tree,i,file_path):
    Onto = get_ontology(file_path+"Check\\my_onto{0}.owl".format(i)).load()
    with Onto:

        for [Node1, Node2, Type] in ListOfModifications:
            if Type=="DI":

                try:
                    destroy_entity(Onto[Node1])
                except:
                    continue
                # Inserting Node1 into Node2
                types.new_class(Node1, (Onto[Node2],))  # make a class
            if Type=="SW":
                print("[SW]--->",Node1, Node2)
                FatherOfNode1 = FindFather(Node(Node1), Tree)
                FatherOfNode2 = FindFather(Node(Node2), Tree)
                print("[SW]--->Father:", FatherOfNode1, FatherOfNode2)
                print("==>",Node1, Onto[FatherOfNode1])
                print("==>",Node2, Onto[FatherOfNode2])

                # if "{0}".format(FatherOfNode1) =="Thing":
                #     if "{0}".format(FatherOfNode1) == Node2:
                #         print("VAO")
                #
                # else:
                #     if "{0}".format(FatherOfNode2) =="Thing":
                #         print("VAO2")
                # with Ontology:
                #     try:
                #         if FatherOfNode2 == Node("Thing") or FatherOfNode2==None:
                #             destroy_entity(Onto[Node1])
                #             types.new_class(Node1, (Thing,))  # make a class
                #             destroy_entity(Onto[Node2])
                #             types.new_class(Node2, (Onto[Node1],))  # make a class
                #         #else:
                #         #   types.new_class(Node1, (Onto[FatherOfNode2],))  # make a class
                #         if FatherOfNode1 == Node("Thing") or FatherOfNode2==None:
                #             destroy_entity(Onto[Node2])
                #             types.new_class(Node2, (Thing,))  # make a class
                #             destroy_entity(Onto[Node1])
                #             types.new_class(Node1, (Onto[Node2],))  # make a class
                #         #else:
                #         #    print(Onto[FatherOfNode1])
                #         #    types.new_class(Node2, (Onto[FatherOfNode1],))  # make a class
                #     except:
                #         print("LOIIIIIIIIIIIIIIIIIIIIIIIIIII=====>", Node1)
                #         continue

    Onto.save(file=file_path+"Check\\NoisyOntology{0}.owl".format(i))
    print(file_path+"Check\\NoisyOntology{0}.owl".format(i))
    os.remove(file_path+"Check\\my_onto{0}.owl".format(i))
    print("------------------------------------------------------------------------------")


def DeleteSomeConcepts(ListOfModifications, Tree, file_path):
    #for index in range(1, numberOfOntologies+1):
    for index in range(1, len(ListOfModifications)+1):
        print("===================================={0}==================================".format(index))
        print(">>>>>>>>--->",ListOfModifications[index-1][2])
        ExportNoisyOntologies(ListOfModifications[index-1][2], Tree,index,file_path)


def SaveDistanceOfNoisyOntology(NoisyOntologiesForProfile,file_path):
    print("+++++++++++++++++++++++++++++++++++++++++++++")
    f = open(file_path+"Check\\Information_NoisyOntology.csv", 'w')
    header = ['Name', 'Distance']
    writer = csv.writer(f)
    writer.writerow(header)
    index=1
    ListDistance_of_Profile = []
    for each in NoisyOntologiesForProfile:
        ListDistance_of_Profile.append(each[1])
        writer.writerow(["Noisy Ontology {0}".format(index),each[1]])
        index+=1
    writer.writerow(["Statistic:"])
    writer.writerow(["Min:",min(ListDistance_of_Profile)])
    writer.writerow(["Max:", max(ListDistance_of_Profile)])
    writer.writerow(["Avg:", mean(ListDistance_of_Profile)])


#==================================================================

def ProfileSelection_version2(OriginalTree, ontology, NbrProfile, ListOfClosestTrees, NbrOriginalOntology=0, NbrTree=30,
                              TypeOfDistance=0):
    ListOfNodes = list(ontology.classes())
    ListOfNodes = ChangeFullName_to_CondensedName(ListOfNodes)
    ListOfNodes = TranslatingFromStringToNode_List(ListOfNodes)
    # ListOfNodes.append(Node("Thing")) #================================================----> Tạm bỏ
    NbrConcept = len(ListOfNodes)
    ProfileMerging = []
    ListOfTreeProfile = []
    ListDistance_of_Profile=[]
    #print("------Before------", len(ListOfClosestTrees))
    for i in range(1, NbrOriginalOntology + 1):
        ListOfClosestTrees.insert(0, [OriginalTree, 0])
    NbrProfile = NbrProfile + NbrOriginalOntology
    count = 0
    # '''
    if NbrProfile <= len(ListOfClosestTrees) and len(ListOfNodes) > 0:
        for i in range(NbrProfile):
            count += 1
            ListOfAxioms = CollectingAxioms(ListOfNodes, ListOfClosestTrees[i][0])
            ProfileMerging.append(ListOfAxioms)
            ListOfTreeProfile.append(ListOfClosestTrees[i][0])
            dist = simple_distance(ListOfClosestTrees[i][0], T2)
            if dist!=0:
                ListDistance_of_Profile.append(dist)
    print("------------------Min - Max - Average of Profile-------------------")
    print ("Min", min(ListDistance_of_Profile))
    print("Max", max(ListDistance_of_Profile))
    print("Average:", mean(ListDistance_of_Profile))
    print("------------------------------------------------------")
    return ProfileMerging, ListOfTreeProfile
# -----------------------------
#==========================================================================
onto1 = get_ontology("C:\\Thanh\\Code\\Owlready2\\Dataset\\conference\\sigkdd.owl")
onto1.load()
ListOfConcept_Source1 = list(onto1.classes())
Classes = copy.deepcopy(ListOfConcept_Source1)
ListFC = Collect_Father_Children_FromOntology(ListOfConcept_Source1)
ListFC = sorted(ListFC, key=itemgetter(0))
ListOfChildToRoot = List_FromLeavesToRoot_byFC(ListFC)
ListOfChildToRoot = sorted(ListOfChildToRoot, key=itemgetter(0))
T2 = CreateTree(ListOfChildToRoot)

if __name__ == '__main__':
    # ============================================================
    onto2 = get_ontology("C:\\Thanh\\Code\\Owlready2\\Dataset\\conference\\sigkdd.owl")
    addressOntology="C:\\Thanh\\Code\\Owlready2\\Dataset\\Test\\"
    onto2.load()
    ListOfConcept_Source2 = list(onto2.classes())
    Classes1 = copy.deepcopy(ListOfConcept_Source2)
    ListFC2 = Collect_Father_Children_FromOntology(ListOfConcept_Source2)
    ListFC2 = sorted(ListFC2, key=itemgetter(0))
    ListOfChildToRoot2 = List_FromLeavesToRoot_byFC(ListFC2)
    ListOfChildToRoot2 = sorted(ListOfChildToRoot2, key=itemgetter(0))
    Tree = CreateTree(ListOfChildToRoot2)
    #============================================================
    freeze_support()
    ListOfTenFolds = []
    NumberOfNoisyTrees = 100
    t = 40
    r = 15
    print("Number of Nodes:", len(Classes1))
    # GeneratingTreeTime = time.time()
    dem = 0
    NumberofNoisyOntologyForProfile=30

    while (dem < 1):
        dem += 1
        NoisyTime = time.time()
        ListOfClosestTrees = FunctionGeneratingNoisyTree_NumberTree_NoParallel(numTree=NumberOfNoisyTrees, Threshosh_Distance=t,percent=r,Classes = Classes1, Tree = Tree)
        NoisyOntologiesForProfile = ListOfClosestTrees[:NumberofNoisyOntologyForProfile]
        print("-------------------------------")
        PrintList(NoisyOntologiesForProfile)
        CreateOntologies(NumberofNoisyOntologyForProfile,addressOntology)
        DeleteSomeConcepts(NoisyOntologiesForProfile, Tree, addressOntology)
        SaveDistanceOfNoisyOntology(NoisyOntologiesForProfile,addressOntology)
        #ProfileMerging, ListOfTreeProfile = ProfileSelection_version2(T2, onto1, NumberofNoisyOntologyForProfile, ListOfClosestTrees,NbrOriginalOntology=3)
        # # ListOfAxioms, CommonAxioms, DifferentAxioms = CollectingListOfAxiomsFromOriginalOntologies_TwoArrays(ProfileMerging,ListFC)
        TimeComputation = time.time() - NoisyTime
        ListOfTenFolds.append(TimeComputation)
        print(" ==> Generating Noisy Tree Time:", TimeComputation)
    #PrintList(ListOfTenFolds)
    print("Average:", mean(ListOfTenFolds))
    print("----------------------")
