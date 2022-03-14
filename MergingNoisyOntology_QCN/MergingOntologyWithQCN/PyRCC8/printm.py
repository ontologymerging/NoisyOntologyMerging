from basesplit import bsplit
from helpfuncs import translate

# print matrix with relations split into base relations
def printMatrix(Matrix):

   for i in range(len(Matrix)):
       for j in range(i+1,len(Matrix)):
           print(i, j, [translate(p) for p in bsplit[Matrix[i][j]-1][1]])
           
def ChangeMatrixToList(Matrix):
   ListOfConstraints=[]
   for i in range(len(Matrix)):
       for j in range(i+1,len(Matrix)):
           ListOfConstraints.append([i, j, [translate(p) for p in bsplit[Matrix[i][j]-1][1]]])
   return ListOfConstraints
