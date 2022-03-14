import itertools
import numpy as np
import string
import ast
def PrintList(l):
    count=0
    for each in l:
        count+=1
        print(count, each)

#=======================================================
#A description of relations
# A -> B  , A <- B
def LeftSide(Concept):
    return Concept[0]

def RelationOfConcepts(Concept):
    return Concept[1:len(Concept)-1]

def RightSide(Concept):
    return Concept[len(Concept)-1]
#=======================================================
# ConceptString ABC, ABCD, ABCDE
def PositionOfString(letterToFind,conceptstring):
    count=0
    for i in conceptstring:
        count=count+1
        if(letterToFind == i):
            return count
    return 0
#====================================
def Individuals(primaryConcept):
    ListOfIndividual=[]
    for index in range(1,len(primaryConcept)+1):
        ListOfIndividual.append("a{0}".format(index))
    return ListOfIndividual
#=================List of Interpretations===============
def ListOfIndividuals(Concept):
    Alphabet = Individuals(Concept)#list(string.ascii_lowercase)
    TempConcept=""
    for index in range(len(Concept)):
        TempConcept ="{0}{1}".format(TempConcept,Alphabet[index])
        #print("{0}".format(Alphabet[index]))
    #Concept = Concept.lower()
    Concept = TempConcept

    List_Individual=[]
    for i in range(len(Concept)):
        ConceptConsideration = Concept.replace(Concept[i],"")
        Temp=[]
        Temp.append([Concept[i]])
        for j in range(1, len(ConceptConsideration)+1):
            TempIndividual=[]
            for each in list(itertools.combinations(ConceptConsideration, j)):
                each = list(each)
                each.append(Concept[i])
                each.sort()
                TempIndividual.append(each)
            Temp.extend(TempIndividual)
        List_Individual.append(Temp)
    return List_Individual

def CombineTwoArray(Array1, Array2):
    ListOfArray_Combination=[]
    DimArray = np.array(Array1, dtype="object")
    for eachArray1 in Array1:
        for eachArray2 in Array2:
            Temp=[]
            if DimArray.ndim>1:
                for each in eachArray1:
                    Temp.append(each)
            else:
                Temp.append(eachArray1)
            Temp.append(eachArray2)
            ListOfArray_Combination.append(Temp)

    return ListOfArray_Combination

def ListOfPossibleInterpretations(Concepts_String):
    List_Individual = ListOfIndividuals(Concepts_String)
    Interpretation=List_Individual[0]
    for i in range(1,len(List_Individual)):
        Interpretation = CombineTwoArray(Interpretation,List_Individual[i])
    return Interpretation[0:len(Interpretation)-1]
#================================================================
def CheckCorrectionOfInterpretation_EachConcept(Concept1, Interpretations,primaryConcept):
    resultChecking_Concept1 = False
    # -----------------------Concept 1--------------------------------
    positionRight = PositionOfString(RightSide(Concept1), primaryConcept) - 1
    positionLeft = PositionOfString(LeftSide(Concept1), primaryConcept) - 1
    LeftSet = set(Interpretations[positionLeft])
    RightSet = set(Interpretations[positionRight])
    if RelationOfConcepts(Concept1) == "->" or RelationOfConcepts(Concept1) == ["->"]:
        if LeftSet.issubset(RightSet):
            resultChecking_Concept1 = True
    if RelationOfConcepts(Concept1) == "<-" or RelationOfConcepts(Concept1) == ["<-"]:
        if RightSet.issubset(LeftSet):
            resultChecking_Concept1 = True
    if RelationOfConcepts(Concept1) == "=" or RelationOfConcepts(Concept1) == ["="]:
        if all([Interpretations[positionLeft][i] in Interpretations[positionRight] for i in range(len(Interpretations[positionLeft]))]) == True \
                and len(Interpretations[positionLeft]) == len(Interpretations[positionRight]):
            resultChecking_Concept1 = True
    if RelationOfConcepts(Concept1) == "<-; &#8707;R" and len(Interpretations)>3:
        check=0
        if LeftSide(Concept1).lower() == Interpretations[3][1][0]:
            check+=1
        if RightSide(Concept1).lower() == Interpretations[3][1][1]:
            check+=1
        if check == 2:
            resultChecking_Concept1 = True
    if RelationOfConcepts(Concept1) == "&#8707;R &#8849;" and len(Interpretations)>3:
        check=0
        if RightSide(Concept1).lower() == Interpretations[3][1][0]:
            check+=1
        if LeftSide(Concept1).lower() == Interpretations[3][1][1]:
            check+=1
        if check == 2:
            resultChecking_Concept1 = True

    return resultChecking_Concept1
#================================================================
def ComputingDistance_Satisfaction_Of_AllInterpretations_From_OneSource(ListOfAxioms_Source, Interpretations, primaryConcept):
    ListOfDistance=[]
    for eachInterp in Interpretations:
        Distance = 0
        for eachAxiom in ListOfAxioms_Source:
            if CheckCorrectionOfInterpretation_EachConcept(eachAxiom, eachInterp,primaryConcept)==False:
                Distance+=1
        ListOfDistance.append(Distance)
    return ListOfDistance

#=======================================
def Computing_Distance_From_Multi_Sources(ListOfSources, Interpretations, primaryConcept):
    ListOfInterpretations_Distance=[]
    for eachInterp in Interpretations:
        ListOfDistance = []
        for eachListOfAxioms_Source in ListOfSources:
            Distance = 0
            for eachAxiom in eachListOfAxioms_Source:
                if CheckCorrectionOfInterpretation_EachConcept(eachAxiom, eachInterp,primaryConcept)==False:
                    Distance+=1
            ListOfDistance.append(Distance)
        ListOfInterpretations_Distance.append([eachInterp, ListOfDistance,sum(ListOfDistance)])
    ListOfInterpretations_Distance.sort(key=lambda x: x[-1])
    return ListOfInterpretations_Distance
#========================================
def Selecting_InterpretationResults(ListOfInterpretations_Distance, coefficient=1):
    ResultInterpretation_Distance=[]
    ResultInterpretation=[]
    for each in ListOfInterpretations_Distance:
        if each[len(each)-1]<=coefficient:
            ResultInterpretation_Distance.append(each)
            ResultInterpretation.append(each[0])
    print("Coefficient: ", coefficient)
    return ResultInterpretation
#========================================

def Computing_Frequency(ListOfIndividuals,primaryConcept):
    Individual={}
    Alphabet = Individuals(primaryConcept)#list(string.ascii_lowercase)
    for index in range(len(primaryConcept)):
        Individual[Alphabet[index]]=0
    for eachElement in ListOfIndividuals:
        Individual[eachElement]+=1
    return Individual
#----------------------------------------
def SIFAlgorithm(ListOfInterpretations, primaryConcept):
    SIF={}
    Interpretation={}
    for index in range(len(primaryConcept)):
        Interpretation[primaryConcept[index]]=[]
        for eachInterpretation in ListOfInterpretations:
            for eachIndividual in eachInterpretation[index]:
                Interpretation[primaryConcept[index]].append(eachIndividual)
    for ConceptName,individuals in Interpretation.items():
        SIF[ConceptName]=[]
        #print("---------------------")
        #print("Concept:", ConceptName)
        for IndividualName, Number in Computing_Frequency(individuals,primaryConcept).items():
            #print("-->",IndividualName, ":",Number)
            #if Number>(len(ListOfInterpretations)/2):
            #if Number > (len(ListOfInterpretations)*2 / 3):
            if Number == len(ListOfInterpretations):
                SIF[ConceptName].append(IndividualName)
    #'''
    return SIF
#========================================
def ListOfTripleFor_AIntersectionBSubsumeC(primaryConcept):
    ListOfTriple_FromConceptName=[]
    for eachTriple in list(itertools.permutations(primaryConcept,3)):
        if len(ListOfTriple_FromConceptName)>0:
            Flag=False
            for each in ListOfTriple_FromConceptName:
                if eachTriple[2] == each[2]:
                    Flag = True
                    break
            if Flag == False: ListOfTriple_FromConceptName.append(eachTriple)
        else: ListOfTriple_FromConceptName.append(eachTriple)
    return ListOfTriple_FromConceptName
#----------------------------------------
#=================================================================
def ComputingDistanceBetween_Axiom_And_InputSources(ProfileMerging, Collecting_SemanticConflicts):
    ListOfDistanceOfAxiomsforSematicConflicts=[]
    for eachSemanticConflicts in Collecting_SemanticConflicts:
        count_Left=0
        count_Right = 0
        Left=eachSemanticConflicts[0]
        Right = eachSemanticConflicts[1]
        if "<-" in Left:
            Left = [Left[2],"->",Left[0]]
        if "<-" in Right:
            Right = [Right[2],"->",Right[0]]
        ListOfDistance = []
        for eachProfile in ProfileMerging:
            if Left in eachProfile:
                count_Left+=1
            if Right in eachProfile:
                count_Right += 1
        ListOfDistance.append([Left,count_Left])
        ListOfDistance.append([Right, count_Right])
        ListOfDistanceOfAxiomsforSematicConflicts.append(ListOfDistance)
    return ListOfDistanceOfAxiomsforSematicConflicts

def SelectingFinalAxiomResult(ProfileMerging, Collecting_SemanticConflicts, SelectionConjunctionDisjunction=0):
    #0: Conjunction, 1: Disjunction (union)
    ListDistances_Axioms = ComputingDistanceBetween_Axiom_And_InputSources(ProfileMerging,Collecting_SemanticConflicts)
    #print(ListDistances_Axioms)
    ListOfSelectedAxioms=[]
    for eachPair_Distance_Axiom in ListDistances_Axioms:
        Distance_Axiom_1 = eachPair_Distance_Axiom[0]
        Distance_Axiom_2 = eachPair_Distance_Axiom[1]
        if Distance_Axiom_1[1]< Distance_Axiom_2[1]:
            ListOfSelectedAxioms.append(Distance_Axiom_2[0])
        if SelectionConjunctionDisjunction == 1 and Distance_Axiom_1[1] == Distance_Axiom_2[1]:
            ListOfSelectedAxioms.append(Distance_Axiom_1[0])
            ListOfSelectedAxioms.append(Distance_Axiom_2[0])
    return ListOfSelectedAxioms

def RemoveTransitiveAxioms(SyntacticResult,primaryConcept):
    CollectingSubsumption=[]
    for eachAxiom in SyntacticResult:
        if len(eachAxiom)==3 and eachAxiom[1]=="->":
            CollectingSubsumption.append(eachAxiom)
    #PrintList(CollectingSubsumption)
    #print("------------------")
    Removal=[]
    for eachSubsumption in CollectingSubsumption:
        for eachNext in primaryConcept:
            NextAxioms=[eachSubsumption[2],"->", eachNext]
            if NextAxioms in CollectingSubsumption:
                Removal.append([eachSubsumption[0],"->",eachNext])
    Removal = RemoveDuplicate(Removal)
    return Removal #DeletingBetweenTwoArray(CollectingSubsumption, Removal)
#-----------------------------------------------------------------
def Finding_SyntacticResult(ProfileMerging,SemanticResult,primaryConcept,SelectionConjunctionDisjunction=0):
    Interpretation=[]
    for name,each in SemanticResult.items():
        Interpretation.append(each)
    #-------------------
    Relation=["->","<-"]
    SyntacticResult=[]
    Collecting_SemanticConflictsAxioms=[]
    for each in list(itertools.combinations(primaryConcept, 2)):
        #print(each)
        Temp_SemanticConflictsAxioms=[]
        for eachRelation in Relation:
            #Axiom = "{0}{1}{2}".format(each[0],eachRelation,each[1])
            Axiom = [each[0],eachRelation,each[1]]
            Temp1 = "%s"%SemanticResult.get(each[0])
            Temp2 = "%s"%SemanticResult.get(each[1])
            #if Temp1!=Temp2:
            #    print("+++==>", SemanticResult.get(each[0]), SemanticResult.get(each[1]))
            #print(Axiom)
            #print("+++==>",Temp1, "----",Temp2)
            if CheckCorrectionOfInterpretation_EachConcept(Axiom, Interpretation,primaryConcept) == True\
                    and Temp1!=Temp2:
                if "<-" in Axiom:
                    Axiom = [Axiom[2], "->", Axiom[0]]
                SyntacticResult.append(Axiom)
                #print("NHAN: ",Axiom)
            #print()
            if Temp1==Temp2:
                Temp_SemanticConflictsAxioms.append(Axiom)
        if len(Temp_SemanticConflictsAxioms)>0:
            Collecting_SemanticConflictsAxioms.append(Temp_SemanticConflictsAxioms)
    for each in ListOfTripleFor_AIntersectionBSubsumeC(primaryConcept):
        Temp = set(SemanticResult.get(each[0])).intersection(set(SemanticResult.get(each[1])))
        if Temp.issubset(set(SemanticResult.get(each[2]))):
            #Axiom= "{0} ∩ {1}->{2}".format(each[0],each[1],each[2])
            Axiom = [each[0], "∩", each[1],"->",each[2]]
            SyntacticResult.append(Axiom)
    Res = SelectingFinalAxiomResult(ProfileMerging, Collecting_SemanticConflictsAxioms, SelectionConjunctionDisjunction)
    #print("Selection:",Res)
    SyntacticResult.extend(Res)
    Removal = RemoveTransitiveAxioms(SyntacticResult, primaryConcept)
    #PrintList(Removal)
    SyntacticResult = DeletingBetweenTwoArray(SyntacticResult,Removal)
    #-------------------
    return SyntacticResult

#========================================
def Finding_FinalSyntacticResult(SyntacticResult):
    FinalSyntacticResult=[]
    ListOfConflicts=[]
    for each1 in SyntacticResult:
        for each2 in SyntacticResult:
            if (each1[1:len(each1) - 1] == "->" or each1[1:len(each1) - 1] == "<-") \
                    and (each2[1:len(each2) - 1] == "->" or each2[1:len(each2) - 1] == "<-"):
                if each1[0] == each2[0] \
                        and each1[len(each1)-1] == each2[len(each1)-1]\
                        and each1[1:len(each1)-1]!=each2[1:len(each1)-1]:
                    ListOfConflicts.append(each1)
        #if len(Conflicts)>0: ListOfConflicts.append(Conflicts)

    FinalSyntacticResult = list(set(SyntacticResult).difference(set(ListOfConflicts)))
    FinalSyntacticResult.append(ListOfConflicts[0])
    return ListOfConflicts, FinalSyntacticResult

def Print_InitialInterpretation(primaryConcept):
    Alphabet = Individuals(primaryConcept)#list(string.ascii_lowercase)
    InitialInterpretation={}
    for index in range(len(primaryConcept)):
        InitialInterpretation[primaryConcept[index]] = [Alphabet[index]]
    return InitialInterpretation
#========================================
#---------------------------

def ListOfAxiomsFromConcept(primaryConcept):
    Relation=["->","=","<-"]
    ListOfAxioms=[]
    for eachConcept in list(itertools.combinations(primaryConcept, 2)):
        for each in Relation:
            ListOfAxioms.append([eachConcept[0], each,eachConcept[1]])
    return ListOfAxioms


def Check_DuplicateConceptsInAxioms(ANewAxiom, ListOfAxioms):
    for each in ListOfAxioms:
        if ANewAxiom[0]==each[0] and ANewAxiom[2]==each[2]:
            return True
    return False

def ListOfAllAxioms_Combination(ListOfAxioms):
    ListOfAllCombinationAxioms=[]
    for each in ListOfAxioms:
        count = 0
        flag=False
        for i in range(len(each)):
            Temp = list(each[i+1:])
            if Check_DuplicateConceptsInAxioms(each[i],Temp) == True:
                flag = True
            if RelationOfConcepts(each[i])==["="]:
                count+=1
        if flag==False and count<len(each):
            ListOfAllCombinationAxioms.append(each)
    return ListOfAllCombinationAxioms

def Deleting_Individuals_Duplication(Interpretation):
    for name, each in Interpretation.items():
        Temp = Interpretation.get(name)
        Temp = list(dict.fromkeys(Temp))
        Temp.sort()
        Interpretation[name] = Temp
    return Interpretation

def GeneratingInterpretation(Axiom, Concept, InitialInterpretation):
    if RelationOfConcepts(Axiom) == ["->"]:
        InitialInterpretation[RightSide(Axiom)].extend(InitialInterpretation.get(LeftSide(Axiom)))
    if RelationOfConcepts(Axiom) == ["<-"]:
        InitialInterpretation[LeftSide(Axiom)].extend(InitialInterpretation.get(RightSide(Axiom)))
    if RelationOfConcepts(Axiom) == ["="]:
        InitialInterpretation[LeftSide(Axiom)].extend(InitialInterpretation.get(RightSide(Axiom)))
        InitialInterpretation[RightSide(Axiom)].extend(InitialInterpretation.get(LeftSide(Axiom)))
    InitialInterpretation = Deleting_Individuals_Duplication(InitialInterpretation)
    return InitialInterpretation

def GeneratingInterpretation_version2(Axiom, InitialInterpretation):
    if RelationOfConcepts(Axiom) == ["->"]:
        InitialInterpretation[RightSide(Axiom)].extend(InitialInterpretation.get(LeftSide(Axiom)))
    if RelationOfConcepts(Axiom) == ["<-"]:
        InitialInterpretation[LeftSide(Axiom)].extend(InitialInterpretation.get(RightSide(Axiom)))
    if RelationOfConcepts(Axiom) == ["="]:
        InitialInterpretation[LeftSide(Axiom)].extend(InitialInterpretation.get(RightSide(Axiom)))
        InitialInterpretation[RightSide(Axiom)].extend(InitialInterpretation.get(LeftSide(Axiom)))
    return InitialInterpretation

def ListOfDictionary_to_ListOfArray(ListOfDictionary):
    ListOfInterpretations_Array=[]
    for eachDictionary in ListOfDictionary:
        Temp_Array=[]
        for name, each in eachDictionary.items():
            Temp_Array.append(each)
        ListOfInterpretations_Array.append(Temp_Array)
    return ListOfInterpretations_Array


def Generating_AllInterpretation(ListOfCombinationAxioms,Concept):
    ListOfAllInterpretation_Dictionary=[]
    ListOfAllInterpretation_Array = []
    for eachCombination in ListOfCombinationAxioms:
        Interpretation = Print_InitialInterpretation(Concept)
        for i in range(len(Concept)):
            for eachAxioms in eachCombination:
                Interpretation = GeneratingInterpretation(eachAxioms,Concept,Interpretation)
        ListOfAllInterpretation_Dictionary.append(Interpretation)
    #llInterpretation)
    ListOfInterpretations_Array = ListOfDictionary_to_ListOfArray(ListOfAllInterpretation_Dictionary)
    return ListOfAllInterpretation_Dictionary, ListOfInterpretations_Array
#RemoveDuplicate
def RemoveDuplicate(Array):
    result = []
    for x in Array:
        if x not in result:
            result.append(x)
    return result

def GeneratingAllInterpretation_AllCombination_Level(Concept,AddLevel=1):
    AllInterpretation_AllCombination_Level=[]
    ListOfAxioms = ListOfAxiomsFromConcept(Concept)
    for index in range(2,len(Concept)+AddLevel):
        print("Level: ",index)
        Axioms = itertools.combinations(ListOfAxioms, index)
        ListOfAllCombinationAxioms = ListOfAllAxioms_Combination(list(Axioms))
        ListOfAllInterpretation_Dictionary, ListOfInterpretations_Array = Generating_AllInterpretation(
        ListOfAllCombinationAxioms, Concept)
        AllInterpretation_AllCombination_Level.extend(ListOfInterpretations_Array)
    AllInterpretation_AllCombination_Level = RemoveDuplicate(AllInterpretation_AllCombination_Level)
    #print("--------------------")
    #PrintList(AllInterpretation_AllCombination_Level)
    return AllInterpretation_AllCombination_Level

def Collecting_AtomicConceptsFrom_AllSources(ListOfSources):
    ListOfAtomicConcepts=[]
    #Relation=[["->"],["<-"],["="]]
    Relation = ["->","<-","="]
    for eachSource in ListOfSources:
        for eachAxiom in eachSource:
            for eachConcept in eachAxiom:
                if eachConcept not in Relation:
                    ListOfAtomicConcepts.append(eachConcept)
    ListOfAtomicConcepts = list(dict.fromkeys(ListOfAtomicConcepts))
    return ListOfAtomicConcepts
def Collecting_AtomicConceptsFrom_OneSources(OneSource):
    ListOfAtomicConcepts=[]
    #Relation=[["->"],["<-"],["="]]
    Relation = ["->","<-","="]
    for eachAxiom in OneSource:
        for eachConcept in eachAxiom:
            if eachConcept not in Relation:
                ListOfAtomicConcepts.append(eachConcept)
    ListOfAtomicConcepts = list(dict.fromkeys(ListOfAtomicConcepts))
    return ListOfAtomicConcepts

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


#'''
#ListOfAxioms_Source1 = [["R","->","A"],["C","->","A"]]
#ListOfAxioms_Source2 = [["A","->","R"],["C","->","R"]]
#ListOfAxioms_Source3 = [["A","->","C"],["C","->","R"]]
#ListOfAxioms_Source4 = [["C","->","R"],["R","->","A"]]
#ListOfAxioms_Source5 = [["R","->","A"],["A","->","C"]]
#ListOfAxioms_Source1 = [["Statement","->","Proposition"],["Proposition","->","Sentence"]]
#ListOfAxioms_Source2 = [["Statement","->","Proposition"],["Statement","->","Sentence"]]
#ListOfAxioms_Source3 = [["Proposition","->","Statement"],["Statement","->","Sentence"]]
#ListOfAxioms_Source1 = [["Cash","->","Money"],["Currency","->","Money"]]
#ListOfAxioms_Source2 = [["Cash","->","Money"],["Money","->","Currency"]]
#ListOfAxioms_Source3 = [["Cash","->","Currency"],["Money","->","Currency"]]
'''
ListOfAxioms_Source1 = [["DUCK","->","CAT"],["DOG","->","DUCK"]]
ListOfAxioms_Source2 = [["DUCK","->","CAT"],["DOG","->","DUCK"]]
ListOfAxioms_Source3 = [["DUCK","->","CAT"],["DOG","->","DUCK"]]
ListOfAxioms_Source4 = [["DUCK","->","CAT"],["DOG","->","DUCK"]]
#'''
#--------------------------------------------------
#primaryConcept = ["CAT","DOG","DUCK","HORSE"]
#primaryConcept = ["CAT","DOG","DUCK"]
#["Cash","Money","Currency"]
#primaryConcept = "ACR"
'''
#==============================================
#ListOfSources = [ListOfAxioms_Source1,ListOfAxioms_Source2,ListOfAxioms_Source3,ListOfAxioms_Source4]
ListOfSources = [ListOfAxioms_Source1,ListOfAxioms_Source2,ListOfAxioms_Source3]
#Note: List Of Concept
primaryConcept = Collecting_AtomicConceptsFrom_AllSources(ListOfSources)
#==============================================

#==============================================
#ListOfInterpretations = ListOfPossibleInterpretations(primaryConcept)
ListOfInterpretations = GeneratingAllInterpretation_AllCombination_Level(primaryConcept,1)
#PrintList(ListOfInterpretations)
ListOfInterpretations_Distance = Computing_Distance_From_Multi_Sources(ListOfSources,ListOfInterpretations,primaryConcept)
#PrintList(ListOfInterpretations_Distance)
ResultInterpretation = Selecting_InterpretationResults(ListOfInterpretations_Distance,1)
#==============================================

print("-----------------------------------------")
PrintList(ResultInterpretation)
#---------------------------
print ("================= RESULT ===================")
print("-----------------------------------------")
print("List of Atomic Concepts: ", primaryConcept)
print("-----------------------------------------")
SemanticResult = SIFAlgorithm(ResultInterpretation, primaryConcept)
print("The Initial Interpretation:",Print_InitialInterpretation(primaryConcept))
print("-------------------")
print("Semantic Result: ", SemanticResult)
SyntacticResult = Finding_SyntacticResult(SemanticResult, primaryConcept)
print("Syntactic Result: ", SyntacticResult)
'''
#Conflicts, FinalSyntacticResult = Finding_FinalSyntacticResult(SyntacticResult)
#print("Final Syntactic Result: ", FinalSyntacticResult)

