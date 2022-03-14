import itertools

def Translation_From_EL_To_RCC5(Ontology,ListOfConcepts):
    ListOfConceptPair = list(itertools.combinations(ListOfConcepts, 2))
    ListOfConstraints =[]
    for eachAxiom in Ontology:
        Left_ConceptName = eachAxiom[0]
        Right_ConceptName = eachAxiom[2]
        Relation = eachAxiom[1]
        if Relation == "is-a": #Subsumption
            if (Left_ConceptName, Right_ConceptName) in ListOfConceptPair:
                Constraint = [Left_ConceptName,["PP","EQ"],Right_ConceptName]
            if (Right_ConceptName, Left_ConceptName) in ListOfConceptPair:
                Constraint = [Right_ConceptName,["PPI","EQ"],Left_ConceptName]
            ListOfConstraints.append(Constraint)
        if Relation == "dj": #disjoint
            if (Left_ConceptName,Right_ConceptName) in ListOfConceptPair:
                Constraint = [Left_ConceptName,["DR"],Right_ConceptName]
            if (Right_ConceptName,Left_ConceptName) in ListOfConceptPair:
                Constraint = [Right_ConceptName,["DR"],Left_ConceptName]
            ListOfConstraints.append(Constraint)
    return ListOfConstraints
def Translation_From_EL_To_RCC5_SetOfOntologies(SetOfOntologies,ListOfConcepts):
    ListOfConstraints =[]
    for eachSource in SetOfOntologies:
        #print(Translation_From_EL_To_RCC5(eachSource,ListOfConcepts))
        ListOfConstraints.append(Translation_From_EL_To_RCC5(eachSource,ListOfConcepts))
    return ListOfConstraints
def Tranlation_From_RCC5_To_EL(QCN):
    ListOfAxioms=[]
    index=0
    for eachConstraint in QCN:
        Left_RegionName = eachConstraint[0]
        Right_RegionName = eachConstraint[2]
        Relation =eachConstraint[1]
        if Relation==["PP","EQ"]:
            Axiom = [Left_RegionName,"is-a",Right_RegionName]
            ListOfAxioms.append(Axiom)
        if Relation==["PPI","EQ"]:
            Axiom = [Right_RegionName,"is-a",Left_RegionName]
            ListOfAxioms.append(Axiom)
        if Relation==["EQ"]:
            Axiom = [Left_RegionName,"equals",Right_RegionName]
            ListOfAxioms.append(Axiom)
        if Relation==["DR"]:
            Axiom = [Left_RegionName,"dj",Right_RegionName]
            ListOfAxioms.append(Axiom)
        if Relation==["PP"]:
            index +=1
            SubRight_Region = "Sub{0}".format(index)
            Axiom1 = [SubRight_Region, "is-a", Right_RegionName]
            Axiom2 = [SubRight_Region, "dj", Left_RegionName]
            Axiom0 = [Left_RegionName,"is-a",Right_RegionName]
            ListOfAxioms.append(Axiom0)
            ListOfAxioms.append(Axiom1)
            ListOfAxioms.append(Axiom2)
        if Relation==["PPI"]:
            index +=1
            SubLeft_Region = "Sub{0}".format(index)
            Axiom1 = [SubLeft_Region, "is-a", Left_RegionName]
            Axiom2 = [SubLeft_Region, "dj", Right_RegionName]
            Axiom0 = [Right_RegionName,"is-a",Left_RegionName]
            ListOfAxioms.append(Axiom0)
            ListOfAxioms.append(Axiom1)
            ListOfAxioms.append(Axiom2)
        if Relation==["PO"]:
            index +=1
            Middle = "Sub{0}".format(index)
            Axiom1_1 = [Middle, "is-a", Left_RegionName]
            Axiom1_2 = [Middle, "is-a", Right_RegionName]
            index += 1
            SubLeft_Region = "Sub{0}".format(index)
            Axiom2 = [SubLeft_Region, "is-a", SubLeft_Region]
            Axiom3 = [SubLeft_Region, "dj", Right_RegionName]
            index += 1
            Sub_Right_Region = "Sub{0}".format(index)
            Axiom4 = [Sub_Right_Region, "is-a", Right_RegionName]
            Axiom5 = [Sub_Right_Region, "dj", Left_RegionName]

            ListOfAxioms.append(Axiom1_1)
            ListOfAxioms.append(Axiom1_2)
            ListOfAxioms.append(Axiom2)
            ListOfAxioms.append(Axiom3)
            ListOfAxioms.append(Axiom4)
            ListOfAxioms.append(Axiom5)
    return ListOfAxioms

def ClosureOfABoxComplyingWithTBox(TBox,ABox):
    count=0
    while(count<2):
        for eachAxiom in TBox:
            Left_ConceptName = eachAxiom[0]
            Right_ConceptName = eachAxiom[2]
            Relation = eachAxiom[1]
            TempDict={}
            if Relation == "is-a":
                Temp = ABox.get(Right_ConceptName)
                Temp.extend(ABox.get(Left_ConceptName))
                Temp = set(Temp)
                TempDict[Right_ConceptName] = list(Temp)
                ABox.update(TempDict)
        count+=1
    return ABox

def ClosureOfSetOfABoxes_ComplyingWith_TBoxes(TBoxes,ABoxes):
    ListOfABoxes=[]
    for index in range(len(TBoxes)):
        ListOfABoxes.append(ClosureOfABoxComplyingWithTBox(TBoxes[index],ABoxes[index]))
    return ListOfABoxes


