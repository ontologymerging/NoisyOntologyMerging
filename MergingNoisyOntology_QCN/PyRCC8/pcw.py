from heapq import heapify, heappush, heappop
from vbweights import w
from comptab import fcomp
from bitcoding import DALL
from inverse import inv
from conjunction import l_and
import itertools
from counters import arcCount, conCount
from printm import printMatrix

# path consistency using van Beek weights
def PCw(ConMatrix, m = -1, n = -1):
   pq = []                         # list of entries arranged in a heap
   entry_finder = {}               # mapping of tasks to entries
   #REMOVED = None                  # placeholder for a removed task
   counter = itertools.count()     # unique sequence count
   Vars = len(ConMatrix)
   #print("No Den day")

   def add_task(task, priority=0):
       'Add a new task or update the priority of an existing task'
       if task in entry_finder:
           remove_task(task)
       count = next(counter)
       entry = [priority, count, task]
       entry_finder[task] = entry
       heappush(pq, entry)

   def remove_task(task):
       'Mark an existing task as REMOVED.  Raise KeyError if not found.'
       entry = entry_finder.pop(task)
       entry[-1] = None

   def pop_task():
       'Remove and return the lowest priority task. Raise KeyError if empty.'
       #print("VAO", pq)
       while pq:
           task = heappop(pq)[-1]
           if task:
               del entry_finder[task]
               return task
       raise KeyError('pop from an empty priority queue')
   

   # check if it is the first time the path consistency is ever ran, thus, all useful arcs should be taken into account
   if m == -1 and n == -1:
      # initialize queue with weights and sort the queue
      W = [(w[ConMatrix[i][j]-1]) for i in range(Vars) for j in range(i+1,Vars) if ConMatrix[i][j] != DALL]
      Pos = [(i,j) for i in range(Vars) for j in range(i+1,Vars) if ConMatrix[i][j] != DALL]
      for eachP in Pos:
        for eachW in W:
            add_task(eachP,eachW)
      #map(add_task,[(i,j) for i in range(Vars) for j in range(i+1,Vars) if ConMatrix[i][j] != DALL], [(w[ConMatrix[i][j]-1]) for i in range(Vars) for j in range(i+1,Vars) if ConMatrix[i][j] != DALL])
   else:
      add_task((m,n),w[ConMatrix[m][n]-1])
      
   #printMatrix(ConMatrix)
   #print("------------------------")
   # as long as the queue is not empty, process it
   dem=0
   while 1:
      dem+=1
      try:
         #print(pop_task())
         (i,j) = pop_task() # grab the appropriate relation
         #print((i,j),"-", dem)
      except KeyError:
         #print("THOAT:",dem)      
         break
      next(arcCount) # increment visited arcs counter 
      #printMatrix(ConMatrix)  
      # create all triplets to be checked for path consistency
      for k in range(Vars):
          if (ConMatrix[k][i] != DALL) and i != k != j:
             
             next(conCount) # increment checked constraints counter
  
             # constrain arc (k,i,j)
             temp = fcomp[ConMatrix[k][i]-1][ConMatrix[i][j]-1]
             if temp != DALL:
                if k < j:   
                   temp = l_and[temp-1][ConMatrix[k][j]-1]
                   if temp != ConMatrix[k][j]:
                      if not temp: return False # inconsistency
                      ConMatrix[k][j] = temp
                      ConMatrix[j][k] = inv[temp-1]
                      add_task((k, j),w[ConMatrix[k][j]-1])
                else:  
                   temp = l_and[inv[temp-1]-1][ConMatrix[j][k]-1]
                   if temp != ConMatrix[j][k]:
                      if not temp: return False # inconsistency
                      ConMatrix[j][k] = temp
                      ConMatrix[k][j] = inv[temp-1]
                      add_task((j, k),w[ConMatrix[j][k]-1])

          if (ConMatrix[j][k] != DALL) and i != k != j:

             next(conCount) # increment checked constraints counter
          
             # constrain arc (k,i,j)
             temp = fcomp[ConMatrix[i][j]-1][ConMatrix[j][k]-1]
             if temp != DALL:
                if i < k:  
                   temp = l_and[temp-1][ConMatrix[i][k]-1]
                   if temp != ConMatrix[i][k]:
                      if not temp: return False # inconsistency
                      ConMatrix[i][k] = temp
                      ConMatrix[k][i] = inv[temp-1]
                      add_task((i, k),w[ConMatrix[i][k]-1])
                else:  
                   temp = l_and[inv[temp-1]-1][ConMatrix[k][i]-1]
                   if temp != ConMatrix[k][i]:
                      if not temp: return False # inconsistency
                      ConMatrix[k][i] = temp
                      ConMatrix[i][k] = inv[temp-1]
                      add_task((k, i),w[ConMatrix[k][i]-1])
   #printMatrix(ConMatrix)
   # the network is concistent and can't be refined further
   return True    
