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

Array_Constraints = [['0', '1', 'TPPI', 'NTPPI', 'EQ'],
['0', '2', 'DC', 'EC', 'PO', 'TPP', 'NTPP'],
['0', '3', 'TPPI', 'NTPPI'],
['1', '2', 'DC', 'EC'],
['1', '3', 'PO', 'NTPP', 'TPP', 'NTPPI', 'TPPI', 'EQ', 'DC', 'EC'],
['2', '3', 'TPPI', 'NTPPI', 'TPP', 'NTPP', 'PO', 'EQ']]

def init_CheckConsistency():
    Vars = 4 #The number of Variable
    TypeId="Example"
    ConMatrix = tuple([array('B',[DALL if i != j else EQ for i in range(Vars)]) for j in range(Vars)])
    parsecsp_Array(ConMatrix,Array_Constraints)
    return TypeId, ConMatrix

def CheckInconsistency(argv=None):
    TypeId, ConMatrix = init_CheckConsistency()
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

    return ChangeMatrixToList(solution),Consistent
if __name__ == '__main__':
    solution,Consistent=CheckInconsistency()
    if Consistent ==1:
        print("Consistent")
    print(solution)