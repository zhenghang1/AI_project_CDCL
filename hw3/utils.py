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

    def print_stats(self):
        # Print the stored statistics with appropriate labels of what the stats signify
        print(
            "=========================== STATISTICS ==============================="
        )
        print("Solving formula from file: ", self._input_file)
        print("Vars:{}, Clauses:{} Stored Clauses:{}".format(
            str(self._num_vars), str(self._num_orig_clauses),
            str(self._num_clauses)))
        print("Input Reading Time: ", self._read_time - self._start_time)
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
        """
        Method to get the next luby number

        Parameters:
            None
        
        Return:
            the next Luby number in the sequence
        """

        size = len(self.luby_list)

        # Index of the element to be generated,
        # pused into the list and returned
        new_num_idx = size+1

        if math.log(new_num_idx+1,2).is_integer():
            # If the index is of the form 2^K -1,
            # push mult into the queue and double it
            # for the next push
            self.luby_list.append(self.mult)
            self.mult *= 2

            # This helps to fill the other indices
            self.minu = size+1
        else:
            # If the index is not of the form 2^K-1,
            # then the luby number is same as that at
            # the index to_fill-minu-1
            self.luby_list.append(self.luby_list[new_num_idx-self.minu-1])
        
        return self.luby_base * self.luby_list[size]

    def reset_luby(self):
        """
        Method to reset the Luby Generator
        to initial conditions.

        Parameters:
            None
        
        Return:
            None
        """ 
        # Reset it for the next use
        self.luby_list=[]
        self.mult=1
        self.minu=0



class PriorityQueue:
    """
    Class to implement the Priority Queue.
    """

    def __init__(self,start_list):
        """
        Constructor of the priority queue class.

        Parameters:
            start_list: the initially array of scores which are to be pushed in
                        the priority queue
        
        Return:
            the initialized priority queue object
        """

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

        # Array that maps elements to their indices
        # in the heap
        self.indices = []

        ctr = 1
        for x in temp:
            # For all elements in the array,
            # push the [priority,ctr] pair in
            # the heap
            self.heap.append([x,ctr])
            self.indices.append(ctr-1)
            ctr += 1
        
        # This is the basic method to convert an array into
        # heap (by calling heapify in reverse order from first
        # half elements)
        for i in range(int(self.size/2)-1,-1,-1):
            self.heapify(i)
    
    def swap(self,ind1,ind2):
        """
        Swaps elements poined by ind1 and ind2 in the heap.

        Parameters:
            ind1: index in the heap of first element to be swapped
            ind2: index in the heap of the second element to be swapped
        
        Return:
            None
        """

        # Swap the nodes in the heap array
        temp = self.heap[ind1]
        self.heap[ind1] = self.heap[ind2]
        self.heap[ind2] = temp

        # Swap the indices of the nodes
        # in the indices array as the nodes
        # swapped and so their indices also must
        # be swapped
        p1 = self.heap[ind1][1]
        p1 -= 1
        p2 = self.heap[ind2][1]
        p2 -= 1
        temp = self.indices[p1]
        self.indices[p1]=self.indices[p2]
        self.indices[p2]=temp

    def heapify(self,node_index):
        """
        The well known heapify method. Takes in a
        node_index and assuming that its children subtress
        are perfect max heaps, this method converts the whole
        tree rooted at node_index into a max heap.

        Parameters:
            node_index: root of the tree which has to be heapified
        
        Return:
            None
        """

        # Calculate the max priority between the node,
        # its left and its right child

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
            # If max priority is not of root

            if left_index<self.size and maxp == self.heap[left_index][0]:
                # If max priority is of the left node,
                # swap left node with root node 
                # and recursively call heapify on the left node
                # to make it a nax heap
                self.swap(left_index,node_index)
                self.heapify(left_index)
            else:
                # If max priority is of the right node,
                # swap right node with root node 
                # and recursively call heapify on the right node
                # to make it a nax heap
                self.swap(right_index,node_index)
                self.heapify(right_index)

    def get_top(self):
        """
        Get the top element (with max priority) from the queue.

        Parameters:
            None
        
        Return:
            -1 if queue is empty else the element with the highest priority
        """

        # If queue is empty, return -1
        if self.size == 0:
            return -1

        # Top element is the element in heap[0]
        top_element = self.heap[0][1]

        # To remove the first element, we swap it with the last
        # element, reduce size of queue by 1 and call
        # heapify(0) to maintain the heap structure
        self.swap(0,self.size-1)
        self.indices[self.heap[self.size-1][1]-1]=-1
        self.size -= 1
        self.heapify(0)

        return top_element

    def print_data(self):
        """
        Method to print the data structures of the class.

        Parameters:
            None
        
        Return:
            None
        """
        print("Size: ",self.size)
        print("Heap: ",self.heap[:self.size])
        print("Indices: ",self.indices)

    
    def increase_update(self,key,value):
        """
        Method takes in a key and value and for the element that matches the key,
        its priority is increased by value.
        
        Parameters:
            key: element whose priority is to be increased
            value: amount by which the priority has to be increased
        
        Return:
            None
        """
        if self.indices[key-1] == -1:
            return
        
        pos = self.indices[key-1]
        
        # Increase its priority by value
        self.heap[pos][0] += value

        # To maintain the heap structure, traverse the heap 
        # from this node upwards and replace it with its parent 
        # till its parent is bigger than it. 
        # (This is needed as increasing the priority
        # can disrupt the heap structure)
        par=pos
        while par!=0:
            temp = par
            par = int((par-1)/2)
            if self.heap[temp][0] > self.heap[par][0]:
                self.swap(temp,par)
            else:
                break
    
    def remove(self,key):
        """
        Remove the element pointed by key from the queue.

        Parameters:
            key: the element to be removed from the queue
        
        Return:
            None
        """
        if self.indices[key-1] == -1:
            return

        # Replace the node to be deleted with 
        # the final node
        pos = self.indices[key-1]
        this_node_pr = self.heap[pos][0]
        final_node_pr = self.heap[self.size-1][0]
        self.swap(pos,self.size-1)
        self.size -= 1
        self.indices[key-1] = -1


        if final_node_pr > this_node_pr:
            # If the replaced node has a higher priority,
            # then the deleted node, traverse the heap upwards
            # and replace the node with its parent unti 
            # its parent is bigger than it. This is done to 
            # maintain the heap structure.
            par = pos
            while par!=0:
                temp = par
                par = int((par-1)/2)
                if self.heap[temp][0] > self.heap[par][0]:
                    self.swap(temp,par)
                else:
                    break
        elif this_node_pr > final_node_pr:
            # If replaced node has a lower priority than the 
            # removed node,then use heapify to maintain the
            # heap structure
            self.heapify(pos)

    def add(self,key,value):
        """
        Method to add an element (key) with priority value
        into the priority queue.

        Parameters:
            key: the element to be added in the priority queue
            value: the priority value of the element to be added
        
        Return:
            None
        """

        # Push the key to the last position with priority 0
        self.heap[self.size] = [0,key]
        self.indices[key-1] = self.size

        # Increase the heap size
        self.size += 1

        # Call the increase update method to increase
        # the priority of key from 0 to value
        self.increase_update(key,value)

class Test():
    def __init__(self,input_file,_assignment) -> None:
        self.input_file = input_file
        self.assign_dict = {a.var:a.value for a in _assignment}
        self._num_vars = len(_assignment)
        self.assignment = [a.var * (2*int(a.value)-1) for a in _assignment]

    def test_correctness(self):
        """test the correctness of the result"""
        # Open the input file
        input_file = open(self.input_file,"r")
        
        # Value to be returned
        is_correct = True

        # For all lines in the file
        for line in input_file.readlines():
            # Remove trailing characters at the end of the line using rstrip
            line = line.rstrip()
            
            # Split the line with space as delimiter
            line = line.split()
            
            # First word of the line
            first_word = line[0]
            
            if first_word == "c" or first_word == "p":
                # If it is a comment or the line with number of vars
                # and clauses, ignore it
                continue
            else:

                # Satisfiability of this clause
                clause_sat = False

                # Remove the end 0 as in the DIMACS
                # CNF file
                clause = line[:-1]

                # For all literals in the clause
                for lit in clause:
                    if lit[0] == "-":
                        # If the litteral is negative
                        var = lit[1:]

                        # Value read from the assignement
                        # dictionary is reversed
                        value = not self.assign_dict[int(var)]
                    else:
                        # Value is read from the assignment
                        # dictionary
                        value = self.assign_dict[int(lit)]
                    
                    # OR is performed
                    clause_sat = clause_sat or value
                    
                    # We break if the clause is already satisfied
                    if clause_sat:
                        break
                
                # If the clause is not satisfied,
                # we set is_correct to False and
                # break (stop reading the file again
                # as we can now comment that assignment
                # is False) 
                if not clause_sat:
                    is_correct = False
                    break
        
        # Close the input file
        input_file.close()

        # Return the value
        if is_correct:
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

def check_validity(input_file_name,assign_dict):
    """
    Method takes in a input file having a SAT problem and
    an assignment dictionary and checks whether the problem
    is satisfied by the assignment in the assignment dictionary.

    Parameters:
        input_file_name: Name of the input file storing the SAT problem
        assign_dict: the dictionary storing the mapping of variables to the
        assigned boolean values

    Return:
        a boolean which is True if the passed assignment satisfies the
        SAT problem in the input file passed. It is False if the assignment
        is not a satisfying assignment
    """

