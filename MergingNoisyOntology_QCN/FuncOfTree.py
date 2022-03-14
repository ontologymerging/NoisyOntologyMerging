from zss import simple_distance, Operation,distance #, Node
from simple_tree import Node
from pqgrams import Profile
import copy
import collections
from asciitree import draw_tree
class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'
    # ============================
def FindNode(node, Tree):
    if node == Tree: return Tree
    for c in Tree.children:
        if node in c: return FindNode(node,c)
def FindFather(node, Tree):
    if node == Tree: return Tree
    if node in Tree.children: return Tree
    for c in Tree.children:
        if node in c: return FindFather(node,c)
def IdentifyFatherAndChild(node1,node2,Tree):
    if node1 in Tree.get(node2.label):
        return node1, node2
    if node2 in Tree.get(node1.label):
        return node2, node1
    return None, None
#Note: Option={True: deleting a forest; False deleting a node}
def DeleteNode(node,OriginalTree, option=False):
    Tree = copy.deepcopy(OriginalTree)
    if node != Tree:
        Label_FatherOfNode = FindFather(node, Tree)
        if option == True:
            Label_FatherOfNode.children.remove(node)
        else:
            #Leaf Node
            if len(Tree.get(node.label).children) == 0:
                Label_FatherOfNode.children.remove(node)
                #print("Deleting a leaf node.")
            else:
                ChildrenOfNode = Tree.get(node.label).children
                for each in ChildrenOfNode:
                    #Label_FatherOfNode.children.insert(0,each)
                    Label_FatherOfNode.addkid(each)
                Label_FatherOfNode.children.remove(node)
                #print("Deleting an immediate node.")
    else:
        Tree.children = []
        #print("Deleting a root node: {0}".format(node.label))
    return Tree

#Note that: Position [1 to n], Number is [0-n]
def InsertNode(nodeInsert, OriginalTree, Parent,Position, Number):
    Tree = copy.deepcopy(OriginalTree)
    NbOfChildren = Position + Number - 1
    #print("(",Position, NbOfChildren,")")
    TempChildren = []
    if NbOfChildren <= len(Tree.get(Parent.label).children):
        for i in range(Position-1,NbOfChildren):
            Children = Tree.get(Parent.label).children[i]
            TempChildren.append(Children)
            nodeInsert.addkid(Children)
        for each in TempChildren:
            Label_FatherOfNode = FindFather(each, Tree)
            Label_FatherOfNode.children.remove(each)
        Tree.get(Parent.label).children.insert(Position-1, nodeInsert)
        #print("Inserting a node {0} at the position {1} of {2} and taking {3} children".format(nodeInsert.label,Position,Parent.label,Number))
    else:
        print("------------------------------------------------------")
        print("| ==> Error!. The number of children is out of range |")
        print("------------------------------------------------------")
    return Tree
#===========================================================================
#===========================  SEMANTIC CONFLICTS  ==========================
#===========================================================================
#C -> D => Delete C First, then D -> C
def CreateSemanticConflict_TwoNodes_Father(node1,node2, OriginalTree):
    Tree = copy.deepcopy(OriginalTree)
    Child, Father = IdentifyFatherAndChild(node1,node2,Tree)
    #print(Child,"-",Father)
    if Child != None:
        Temp_Father = Node("Temp{0}".format(Father.label))
        Tree = InsertNode(Temp_Father, Tree, Father, 1, len(Tree.get(Father.label).children))
        Tree = DeleteNode(Child, Tree)
        Tree = InsertNode(Node(Child.label), Tree, Father, 1, len(Tree.get(Father.label).children))
        Tree = DeleteNode(Father, Tree)
        Tree = InsertNode(Node(Father.label), Tree, Child, 1, len(Tree.get(Child.label).children))
        Tree = DeleteNode(Temp_Father, Tree)
    else:
        print("------------------------------------------------------")
        print(" Node <{0}> is not a Child (Father) of Node <{1}> ".format(node1.label, node2.label))
        print("------------------------------------------------------")
    return Tree
#C -> D => Delete D First, then D -> C
def CreateSemanticConflict_TwoNodes_Child(node1,node2, OriginalTree):
    #print("9999999999999999999999")
    #print(node1, "-", node2)
    Tree = copy.deepcopy(OriginalTree)
    Child, Father = IdentifyFatherAndChild(node1,node2,Tree)
    #print(Child,"-",Father)
    if Child != None:
        Tree = DeleteNode(Father, Tree)
        Tree = InsertNode(Node(Father.label), Tree, Child, 1, len(Tree.get(Child.label).children))
    else:
        print("Node {0} is not a Child (Father) of Node {1}".format(node1.label, node2.label))
    return Tree

def CreateSemanticConflict_TwoNodes_Child_Itself(node1,node2, OriginalTree):
    #print("9999999999999999999999")
    #print(node1, "-", node2)
    Tree = copy.deepcopy(OriginalTree)
    Child, Father = IdentifyFatherAndChild(node1,node2,Tree)
    #print(Child,"-",Father)
    if Child != None:
        Tree = DeleteNode(Father, Tree)
        Tree = InsertNode(Node(Father.label), Tree, Child, 1, 0)
    else:
        print("Node {0} is not a Child (Father) of Node {1}".format(node1.label, node2.label))
    return Tree
def Swap_TwoNodes(node1,node2, OriginalTree):
    Tree = copy.deepcopy(OriginalTree)
    Child, Father = node1, node2
    Temp_Child = Node("Temp{0}".format(Child.label))
    Temp_Father = Node("Temp{0}".format(Father.label))
    Tree = InsertNode(Temp_Child,Tree,Child,1,len(Tree.get(Child.label).children))
    Tree = InsertNode(Temp_Father, Tree, Father, 1, len(Tree.get(Father.label).children))
    Tree = DeleteNode(Child,Tree)
    Tree = DeleteNode(Father,Tree)
    Tree = InsertNode(Father, Tree, Temp_Child,1,len(Tree.get(Temp_Child.label).children))
    Tree = InsertNode(Child, Tree, Temp_Father, 1, len(Tree.get(Temp_Father.label).children))
    Tree = DeleteNode(Temp_Child,Tree)
    Tree = DeleteNode(Temp_Father, Tree)
    return Tree
def Swap_TwoNodes_CreateSemanticConflict(node1,node2, OriginalTree):
    Tree = copy.deepcopy(OriginalTree)
    Child, Father = IdentifyFatherAndChild(node1,node2,Tree)
    if Child != None:
        Child, Father = node1, node2
        Temp_Child = Node("Temp{0}".format(Child.label))
        Temp_Father = Node("Temp{0}".format(Father.label))
        Tree = InsertNode(Temp_Child,Tree,Child,1,len(Tree.get(Child.label).children))
        Tree = InsertNode(Temp_Father, Tree, Father, 1, len(Tree.get(Father.label).children))
        Tree = DeleteNode(Child,Tree)
        Tree = DeleteNode(Father,Tree)
        Tree = InsertNode(Father, Tree, Temp_Child,1,len(Tree.get(Temp_Child.label).children))
        Tree = InsertNode(Child, Tree, Temp_Father, 1, len(Tree.get(Temp_Father.label).children))
        Tree = DeleteNode(Temp_Child,Tree)
        Tree = DeleteNode(Temp_Father, Tree)
    else:
        print("------------------------------------------------------")
        print("| ==> Error!. There are not a relationship between two nodes |")
        print("------------------------------------------------------")
    return Tree
#===========================================================================
#===========================  LOGICAL CONFLICTS  ==========================
#===========================================================================
def CreateLogicalConflicts_TwoNodes_Child(node1,node2, OriginalTree):
    Tree = copy.deepcopy(OriginalTree)
    Child, Father = IdentifyFatherAndChild(node1,node2,Tree)
    if Child == None:
        Tree = DeleteNode(node1, Tree)
        Tree = InsertNode(node1, Tree, node2, 1,0)# len(Tree.get(node2.label).children))
    else:
        print("------------------Child--------------------------------")
        print("|{0} - {1}|".format(Child, Father))
        print("| ==> Node {0} and Node {1} have a relationship.     |".format(node1.label,node2.label))
        print("| It can not occur a logical conflict                |")
        print("------------------------------------------------------")
        #print(draw_tree(Tree))
    return Tree

def CreateLogicalConflicts_TwoNodes_Father(node1,node2, OriginalTree):
    Tree = copy.deepcopy(OriginalTree)
    Child, Father = IdentifyFatherAndChild(node1,node2,Tree)
    if Child == None:
        #Tree = DeleteNode(node1, Tree)
        #Tree = InsertNode(node1, Tree, node2, 1, 0)#len(Tree.get(node2.label).children))
        Tree = DeleteNode(node2, Tree)
        Tree = InsertNode(node2, Tree, node1, 1, 0)#len(Tree.get(node1.label).children))
    else:
        print("---------------------Father----------------------------")
        print("|{0} - {1}|".format(Child,Father))
        print("| ==> Node {0} and Node {1} have a relationship.     |".format(node1.label,node2.label))
        print("| It can not occur a logical conflict                |")
        print("------------------------------------------------------")
        #print(draw_tree(Tree))
    return Tree
#For A is-a B and For B is-a A. We just change input at node1 and node2
def CreateLogicalConflicts_TwoNodes_UnDeletion(node1,node2, OriginalTree):
    Tree = copy.deepcopy(OriginalTree)
    Child, Father = IdentifyFatherAndChild(node1,node2,Tree)
    if Child == None:
        Tree = InsertNode(node1, Tree, node2, 1, 0)#len(Tree.get(node2.label).children))
    else:
        print("-------------------UnDeletion-------------------------------")
        print("|{0} - {1}|".format(Child, Father))
        print("| ==> Node {0} and Node {1} have a relationship.     |".format(node1.label,node2.label))
        print("| It can not occur a logical conflict                |")
        print("------------------------------------------------------")
        #print(draw_tree(Tree))
    return Tree

#============================================================================
#-----------------------------------

def List_NodeTree(Tree,K):
    K.append(Tree.label)
    for c in Tree.children:
        List_NodeTree(c,K)

def List_LeafNode_Tree(Tree):
    ListNodeOfTree=[]
    List_NodeTree(Tree,ListNodeOfTree)
    List_Leaf=[]
    for each in ListNodeOfTree:

        if len(Tree.get(each).children)==0:
            List_Leaf.append(each)
    return List_Leaf

def PrintTreeAndDistance(Tree1,Tree2):
    print("--------------A---------------")
    print(Tree1)
    print("-------------A1---------------")
    print(Tree2)
    print("Distance pq (A_PQ,A1_PQ)=", Profile(Tree1).edit_distance(Profile(Tree2)))
    print("Distance (A,A1)=", simple_distance(Tree1, Tree2))

def List_ChildrenFather_On_Tree(Tree):
    NodesInTree=[]
    List_NodeTree(Tree,NodesInTree)
    List_ChildrenFather=[]
    for each in NodesInTree:
        Child = each
        Father = FindFather(Node(each), Tree).label
        if Father != Child:
            List_ChildrenFather.append([Child,Father])
    return List_ChildrenFather

def List_FromLeavesToRoot_byFC(ListFC):
    ListOfFathers,ListOfChildren,ListOfLeaves, ListOf_IntermediateNodes, Root = Enumerating_InforOfTree_ByFC(ListFC)
    ListOfChildToRoot=[]
    for each in ListOfLeaves:
        ChildToRoot =[]
        index = 0
        ChildToRoot.append(each)
        while (each  != Root[0]):
            index+=1
            if each == ListFC[index-1][0]:
                each = ListFC[index-1][1]
                ChildToRoot.append(each)
                index = 0
        ListOfChildToRoot.append(ChildToRoot)
    return ListOfChildToRoot

def List_FromLeavesToRoot_ByTree(Tree):
    ListFC = List_ChildrenFather_On_Tree(Tree)
    return List_FromLeavesToRoot_byFC(ListFC)
#==============================
def ReverseList(List):
    list_Reverse = []
    for each in List:
        list_Reverse.append(each[::-1])
    return list_Reverse
def CreateTree(List_TreesFromLeaves):
    Rev_list_Tree = ReverseList(List_TreesFromLeaves)
    T=Node(Rev_list_Tree[0][0])
    for each in Rev_list_Tree:
        for i in range(0,len(each)-1):
            if each[i+1] not in T:
                T.get(each[i]).addkid(Node(each[i+1]))
    return T
def Enumerating_InforOfTree_ByFC(ListFC):
    ListOfChildren=[]
    ListOfFathers=[]
    for Child, Father in ListFC:
        ListOfChildren.append(Child)
        ListOfFathers.append(Father)
    ListOfFathers = list(set(ListOfFathers))
    ListOfChildren = list(set(ListOfChildren))
    ListOfLeaves = list(set(ListOfChildren).difference(set(ListOfFathers)))
    Root = list(set(ListOfFathers).difference(set(ListOfChildren)))
    ListOf_IntermediateNodes = list(set(ListOfFathers).intersection(set(ListOfChildren)))
    return ListOfFathers,ListOfChildren,ListOfLeaves, ListOf_IntermediateNodes, Root

def FindRoot(ListFC):
    ListOfChildren=[]
    ListOfFathers=[]
    for Child, Father in ListFC:
        ListOfChildren.append(Child)
        ListOfFathers.append(Father)
    Root = list(set(ListOfFathers).difference(set(ListOfChildren)))
    return Root

def FindFatherOfNode_ByFC(node, ListFC):
    for Child, Father in ListFC:
        if node == Child:
            return Father
    return "Not found!"

