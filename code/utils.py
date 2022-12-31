import math

class Statistics:
    """
    Class used to store the various statistics measuerd while solving
    the SAT problem and defines method to print the statistics.
    """

    def __init__(self):
        self._input_file = ""
        self._result = ""
        self._output_statistics_file = ""
        self._output_assignment_file = ""
        self._num_vars = 0
        self._num_orig_clauses = 0
        self._num_clauses = 0
        self._num_learned_clauses = 0
        self._num_decisions = 0
        self._num_implications = 0
        self._start_time = 0
        self._read_time = 0
        self._complete_time = 0
        self._bcp_time = 0
        self._decide_time = 0
        self._analyze_time = 0
        self._backtrack_time = 0
        self._restarts = 0
        self._bve_flag = False
        self._bve_vars = 0
        self._bve_add_clauses = 0
        self._bve_rm_clauses = 0
        self._bve_time = 0

    def print_stats(self):
        print(
            "=========================== STATISTICS ==============================="
        )
        print("Solving formula from file: ", self._input_file)
        print("Vars:{}, Original Clauses:{}, Finally Stored Clauses:{}".format(
            str(self._num_vars), str(self._num_orig_clauses),
            str(self._num_clauses-self._bve_rm_clauses)))
        print("Input Reading Time: ", self._read_time - self._start_time)
        if self._bve_flag:
            print("--------------- Preprocesscing ----------------")
            print("Var eliminated: ",self._bve_vars)
            print("Original clauses deleted: ",self._bve_rm_clauses)
            print("New clauses added: ",self._bve_add_clauses)
            print("BVE time: ",self._bve_time)
        print("-------------------------------")
        print("Restarts: ", self._restarts)
        print("Learned clauses: ", self._num_learned_clauses)
        print("Decisions made: ", self._num_decisions)
        print("Implications made: ", self._num_implications)
        print("Time taken: ", self._complete_time - self._start_time)
        print("----------- Time breakup ----------------------")
        print("BCP Time: ", self._bcp_time)
        print("Decide Time: ", self._decide_time)
        print("Conflict Analyze Time: ", self._analyze_time)
        print("Backtrack Time: ", self._backtrack_time)
        print("-------------------------------")
        print("RESULT: ", self._result)
        print("Statistics stored in file: ", self._output_statistics_file)

        if self._result == "SAT":
            print("Satisfying Assignment stored in file: ",
                  self._output_assignment_file)
        print(
            "======================================================================"
        )


class LubyGenerator:
    def __init__(self,base) -> None:
        # List to store the luby numbers
        self.luby_list = []
        self.luby_base = base

        # Values that help to generate the Luby Sequence
        self.mult = 1
        self.minu = 0

    def get_next_luby_number(self):

        size = len(self.luby_list)
        new_num_idx = size+1

        if math.log(new_num_idx+1,2).is_integer():
            self.luby_list.append(self.mult)
            self.mult *= 2
            self.minu = size+1
        else:
            self.luby_list.append(self.luby_list[new_num_idx-self.minu-1])
        
        return self.luby_base * self.luby_list[size]

    def reset_luby(self):
        # Reset it for the next use
        self.luby_list=[]
        self.mult=1
        self.minu=0



class PriorityQueue:

    def __init__(self,start_list):
        # The first element is removed as it is not related
        # to any variable or literal
        self.size = len(start_list)-1
        temp = start_list[1:]

        # Array that stores the heap
        # Each element in the heap is of the form
        # [priority,element] where priority is the
        # priority of the element and the heap is
        # max heap with respect to the priority scores
        self.heap = []

        # Array that maps elements to their indices in the heap
        self.indices = []

        ctr = 1
        for x in temp:
            self.heap.append([x,ctr])
            self.indices.append(ctr-1)
            ctr += 1

        for i in range(int(self.size/2)-1,-1,-1):
            self.heapify(i)
    
    def swap(self,ind1,ind2):
        temp = self.heap[ind1]
        self.heap[ind1] = self.heap[ind2]
        self.heap[ind2] = temp

        p1 = self.heap[ind1][1]
        p1 -= 1
        p2 = self.heap[ind2][1]
        p2 -= 1
        temp = self.indices[p1]
        self.indices[p1]=self.indices[p2]
        self.indices[p2]=temp

    def heapify(self,node_index):
        maxp = self.heap[node_index][0]

        left_index = 2*node_index+1
        if left_index<self.size:
            pr = self.heap[left_index][0]
            if pr>maxp:
                maxp = pr
        
        right_index = 2*node_index+2
        if right_index<self.size:
            pr = self.heap[right_index][0]
            if pr>maxp:
                maxp = pr
        
        if maxp != self.heap[node_index][0]:
            if left_index<self.size and maxp == self.heap[left_index][0]:
                self.swap(left_index,node_index)
                self.heapify(left_index)
            else:
                self.swap(right_index,node_index)
                self.heapify(right_index)

    def get_top(self):
        # If queue is empty, return -1
        if self.size == 0:
            return -1

        # Top element is the element in heap[0]
        top_element = self.heap[0][1]

        self.swap(0,self.size-1)
        self.indices[self.heap[self.size-1][1]-1]=-1
        self.size -= 1
        self.heapify(0)

        return top_element

    def increase_update(self,key,value):
        if self.indices[key-1] == -1:
            return
        
        pos = self.indices[key-1]
        
        self.heap[pos][0] += value

        par=pos
        while par!=0:
            temp = par
            par = int((par-1)/2)
            if self.heap[temp][0] > self.heap[par][0]:
                self.swap(temp,par)
            else:
                break
    
    def remove(self,key):
        if self.indices[key-1] == -1:
            return

        pos = self.indices[key-1]
        this_node_pr = self.heap[pos][0]
        final_node_pr = self.heap[self.size-1][0]
        self.swap(pos,self.size-1)
        self.size -= 1
        self.indices[key-1] = -1

        if final_node_pr > this_node_pr:
            par = pos
            while par!=0:
                temp = par
                par = int((par-1)/2)
                if self.heap[temp][0] > self.heap[par][0]:
                    self.swap(temp,par)
                else:
                    break
        elif this_node_pr > final_node_pr:
            self.heapify(pos)

    def add(self,key,value):
        # Push the key to the last position with priority 0
        self.heap[self.size] = [0,key]
        self.indices[key-1] = self.size

        self.size += 1

        self.increase_update(key,value)

class Test():
    def __init__(self,sentence,_assignment,num_vars) -> None:
        self.sentence = sentence
        self.assignment = [a[0] * (2*int(a[1])-1) for a in _assignment.items()]
        self.res = [a[0] + (-1*int(a[1])+1) * num_vars for a in _assignment.items()]

    def test_correctness(self):
        """test the correctness of the result"""
        FLAG = True
        res_set = set(self.res)
        for clause in self.sentence:
            flag = False
            for lit in clause:
                if lit in res_set:
                    flag = True
            FLAG = FLAG and flag
            if FLAG == False:
                break

        # Return the value
        if FLAG:
            print("Yeh! The result is correct.")
        else:
            print("Nop! The result is wrong.")

    def test_rep_assign(self):
        """test whether a variable has been assigned twice"""
        """output the number of 0's in `assignment`. 
        If that doesn't equal to 'num_var - len(var)', where `var` is the number of actual number of variables, then the result is definitely wrong"""
        v_count = {}
        for a in self.assignment:
            v_count[abs(a)] = v_count.get(abs(a), 0) + 1
        for v, count in v_count.items():
            if (count > 1) and (v != 0):
                print("Variable X_" + str(v) + " has been assigned " + str(count) + " times!")
        if v_count.get(0, 0) > 0:
            print("Totally " + str(v_count[0]) + " 0's has been 'assigned'.")
