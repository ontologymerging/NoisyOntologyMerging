import itertools

Individuals=['p','t','d','b']
Concepts = ['Paper','Text','Document','Book']


def PrintList(List):
    index = 0
    for each in List:
        index+=1
        print(index,".", each)

def GeneratingIndividuals(Individuals, OneConcept):
    ListAll_Individuals_Of_OneConcept=[]
    for i in range(1,len(Individuals)+1):
        List_Individuals = list(itertools.combinations(Individuals,i))
        for each in List_Individuals:
            dict = {}
            dict[OneConcept] = []
            dict[OneConcept].extend(list(each))
            ListAll_Individuals_Of_OneConcept.append(dict)
    return ListAll_Individuals_Of_OneConcept

AllIndividualOfOneConcept = GeneratingIndividuals(Individuals,"Paper")
print(AllIndividualOfOneConcept)
print(len(AllIndividualOfOneConcept))
Array_Number=[]
for i in range(1, len(AllIndividualOfOneConcept)+1):
    Array_Number.append(i)
#List_Combination = list(itertools.product(Array_Number,4))
List_Combination = list(itertools.product(Array_Number, repeat=len(Concepts)))
#print(List_Combination)
#print(len(List_Combination))

AllIndividualOfAllConcepts=[]
for each in Concepts:
    AllIndividualOfOneConcept = GeneratingIndividuals(Individuals,each)
    AllIndividualOfAllConcepts.append(AllIndividualOfOneConcept)

print(AllIndividualOfAllConcepts[0][0])
ListOfAllAssertions=[]
for each in List_Combination:
    TempDict={}
    for i in range(len(Concepts)):
        TempDict = {**TempDict, **AllIndividualOfAllConcepts[i][each[i] - 1]}
    #TempList =  [AllIndividualOfAllConcepts[0][each[0]-1],AllIndividualOfAllConcepts[1][each[1]-1],AllIndividualOfAllConcepts[2][each[2]-1],AllIndividualOfAllConcepts[3][each[3]-1]]
    #print(TempList)
    ListOfAllAssertions.append(TempDict)
#PrintList(ListOfAllAssertions)

Test =  ListOfAllAssertions[98]
print(Test)
#for
def Check_DR_Relation(List1,List2):
    set_List1 = set(List1)
    set_List2 = set(List2)
    #print("DR - List1:",set_List1, "List2:",set_List2)
    return set_List1.isdisjoint(set_List2)
def Check_PPEQ_Relation(List1, List2):
    set_List1 = set(List1)
    set_List2 = set(List2)
    #print("PP,EQ - List1:",set_List1, "List2:",set_List2)
    return set_List1.issubset(set_List2)
def Check_PP_Relation(List1, List2):
    set_List1 = set(List1)
    set_List2 = set(List2)
    #print("PP - List1:",set_List1, "List2:",set_List2)
    if set_List1.issubset(set_List2) and not set_List1.__eq__(set_List2):
        return True
    return False
def Check_PO_Relation(List1,List2):
    set_List1 = set(List1)
    set_List2 = set(List2)
    #print("PO - List1:",set_List1, "List2:",set_List2)
    if len(set_List1.intersection(set_List2))>0 and len(set_List1.difference(set_List2))>0\
        and len(set_List2.difference(set_List1))>0:
            return True
    return False
def Check_EQ_Relation(List1,List2):
    set_List1 = set(List1)
    set_List2 = set(List2)
    return set_List1.__eq__(set_List2)


def Check_A_Constraint(ABox, Constraint):
    Concept1 = ABox.get(Constraint[0])
    Concept2 = ABox.get(Constraint[2])
    if Constraint[0]== Constraint[2]:
        print("A constraint has the same concept")
        return False
    if Constraint[1] == ["DR"]:
        return Check_DR_Relation(Concept1,Concept2)
    if Constraint[1] == ["PP"]:
        return Check_PP_Relation(Concept1,Concept2)
    if Constraint[1] == ["PP","EQ"]:
        return Check_PPEQ_Relation(Concept1,Concept2)
    if Constraint[1] == ["PO"]:
        return Check_PO_Relation(Concept1,Concept2)
    if Constraint[1] == ["EQ"]:
        return Check_EQ_Relation(Concept1,Concept2)
    return False

def Check_ASetOfConstraints(ABox, SetOfConstraints):
    for eachConstraint in SetOfConstraints:
        if Check_A_Constraint(ABox,eachConstraint) == False:
            return False
    return True
print()
'''
Paper =Test.get("Paper")
Book =Test.get("Book")
Text = Test.get("Text")
Document = Test.get("Document")
print(Check_DR_Relation(Book,Text))
print(Check_PP_Relation(Paper,Text))
print(Check_PP_Relation(Paper,Document))
print(Check_PO_Relation(Document,Book))
print(Check_PP_Relation(Paper,Document))
'''
#------------------------------------------------------
Constraint12 = ["Paper",["PP","EQ"],"Text"]
Constraint13 = ["Text",["PO"],"Book"]
Constraint14 = ["Text",["DR"],"Document"]
Constraint23 = ["Paper",["PP"],"Book"]
Constraint24 = ["Paper",["DR"],"Document"]
Constraint34 = ["Document",["PP"],"Book"]
SetOfConstraints1 = [Constraint12,Constraint13,Constraint14,Constraint23,Constraint24,Constraint34]

#-------------------------------------------------------
Constraint12 = ["Paper",["PP","EQ"],"Text"]
Constraint13 = ["Text",["PP"],"Book"]
Constraint14 = ["Text",["DR"],"Document"]
Constraint23 = ["Paper",["PP"],"Book"]
Constraint24 = ["Paper",["DR"],"Document"]
Constraint34 = ["Document",["PP"],"Book"]
SetOfConstraints2 = [Constraint12,Constraint13,Constraint14,Constraint23,Constraint24,Constraint34]

#------------------------------------------------------
#-------------------------------------------------------
Constraint12 = ["Paper",["PP","EQ"],"Text"]
Constraint13 = ["Text",["PP"],"Book"]
Constraint14 = ["Text",["DR"],"Document"]
Constraint23 = ["Paper",["PP"],"Book"]
Constraint24 = ["Paper",["DR"],"Document"]
Constraint34 = ["Document",["PO"],"Book"]
SetOfConstraints3 = [Constraint12,Constraint13,Constraint14,Constraint23,Constraint24,Constraint34]
#-------------------------------------------------------
Constraint12 = ["Paper",["PP","EQ"],"Text"]
Constraint13 = ["Text",["PO"],"Book"]
Constraint14 = ["Text",["DR"],"Document"]
Constraint23 = ["Paper",["PP"],"Book"]
Constraint24 = ["Paper",["DR"],"Document"]
Constraint34 = ["Document",["PO"],"Book"]
SetOfConstraints4 = [Constraint12,Constraint13,Constraint14,Constraint23,Constraint24,Constraint34]
#print()


def Collecting_Assertions_SatisfyConstraints(ListOfAllAssertions, SetOfConstraints):
    ListOfAssertion_SatisfyConstraint = []
    for eachABox in ListOfAllAssertions:
        #print(eachABox)
        if(Check_ASetOfConstraints(eachABox, SetOfConstraints)==True):
            ListOfAssertion_SatisfyConstraint.append(eachABox)
            #break
    return ListOfAssertion_SatisfyConstraint

Collection_SetOfAssertions = Collecting_Assertions_SatisfyConstraints(ListOfAllAssertions,SetOfConstraints1)
PrintList(Collection_SetOfAssertions)

A1 = {'Paper': ['p'], 'Text': ['p', 't'], 'Document': ['d'], 'Book': ['p', 'b']}
A2 = {'Paper': ['p', 'd'], 'Text': ['p', 't', 'd'], 'Document': ['d'], 'Book': ['p', 'd', 'b','t']}
A3 = {'Paper': ['p', 'b', 'd'], 'Text': ['p', 'b', 't', 'd'], 'Document': ['d', 'b'], 'Book': ['b']}
A4 = {'Paper': ['p'], 'Text': ['p', 't'], 'Document': ['b', 'd'], 'Book': ['p', 'd', 'b','t']}
ListOfInputABoxes = [A1,A2,A3,A4]
def Computing_Distance_Between_ABox_And_SetOfCollectedAssertion(ABox, SetOfAssertions):
    ListOfDistances=[]
    for eachABox in SetOfAssertions:
        Distance=[]
        print("----------------------\n")
        print("A=", ABox)
        print("A'=",eachABox)
        for name,individuals in eachABox.items():
            Res = set(ABox.get(name)).difference(set(individuals))
            Distance.append(len(Res))
            print("A: {0}".format(ABox.get(name)),"A': {0}".format(set(individuals)),"Res: {0}".format(Res),"Distance:",Distance)
        ListOfDistances.append(sum(Distance))
        print("Distance:",ListOfDistances)
        print()
    return min(ListOfDistances)

print(Computing_Distance_Between_ABox_And_SetOfCollectedAssertion(A1,Collection_SetOfAssertions))
def Computing_DistanceBetween_SetOfABoxes_and_SetOfABox(ListInputABoxes, SetOfCollectedAssertion):
    List_Distances=[]
    for eachInputABox in ListInputABoxes:
        Distance = Computing_Distance_Between_ABox_And_SetOfCollectedAssertion(eachInputABox,SetOfCollectedAssertion)
        List_Distances.append(Distance)
    print()
    print("Final Distance:",sum(List_Distances))
Computing_DistanceBetween_SetOfABoxes_and_SetOfABox(ListOfInputABoxes, Collection_SetOfAssertions)