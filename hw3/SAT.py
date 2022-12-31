import os
import sys
import time
import json
from decider import Decider
from restarter import Restarter
from collections import OrderedDict
from utils import Statistics

class AssignedNode:
    """
    Class used to store the information about the variables being assigned.

    Attributes:
        var: variable that is assigned
        value: value assigned to the variable (True/False)
        level: level (decision level in the tree) at which the variable is assigned
        clause: The id of the clause which implies this decision (If this is assigned through implication)
        index: The index in the assignment list at which this node is pushed

    """

    def __init__(self, var, value, level, clause):
        self.var = var
        self.value = value
        self.level = level
        self.clause = clause
        self.index = -1


class SAT:
    def __init__(self, decider="VSIDS", restarter="NO_RESTART", bve_flag="False", base=1024):
        '''
        Constructor for the SAT class

        Parameters:
            decider: the init decision heuristic used, should be of ["VSIDS","LRB","CHB"], default is "VSIDS"
            restarter: the restart strategy to be used, should be of ["GEOMETRIC","LUBY","NO_RESTART"], default is "NO_RESTART"
        '''
        self._num_clauses = 0
        self._num_vars = 0
        self._level = 0
        self.sentence = {}
        # a dict: lit -> List[clause]
        self.clause_ptr = 0
        self.orig_sentence = {}
        self.l2c_watch = {}
        # a dict: clause -> [lit1, lit2]
        self.c2l_watch = {}
        # a dict to store the assignnode, with (var,node) as (key,value)
        self.v2a_watch = {}
        # a list store the node in the order of their assignment
        self._assignment = []
        # decider to use
        self._decider = decider
        # restarter to use
        self._restarter = Restarter(restarter,decider,base)
        # the Statistics object to store basic information
        # bve flag
        self._bve_flag = bve_flag
        self.stats = Statistics()

    def is_negative_literal(self, literal):
        """ To judge whether a literal is negative """
        return literal > self._num_vars

    def get_var_from_literal(self, literal):
        """ To get the corresponding variable from literal """
        if self.is_negative_literal(literal):
            return literal - self._num_vars
        return literal

    def add_clause(self, clause):
        """ 
        Method that adds clause to `self.sentence` while reading the .cnf file. 
        Also helps to eliminate unary clauses.
        """
        clause = clause[:-1]
        clause = list(OrderedDict.fromkeys(clause))
        if len(clause) == 1:
            lit = clause[0]
            value_to_set = True

            if lit[0] == '-':
                value_to_set = False
                var = int(lit[1:])
            else:
                var = int(lit)

            if var not in self.v2a_watch:
                self.stats._num_implications += 1
                node = AssignedNode(var, value_to_set, 0, None)
                self.v2a_watch[var] = node
                self._assignment.append(node)
                node.index = len(self._assignment) - 1
            else:
                node = self.v2a_watch[var]
                if node.value != value_to_set:
                    self.stats._result = "UNSAT"
                    return 0
            return 1

        clause_with_literals = []

        for lit in clause:
            if lit[0] == '-':
                var = int(lit[1:])  # lit[1:] removes '-' at start
                clause_with_literals.append(var + self._num_vars)
            else:
                var = int(lit)
                clause_with_literals.append(var)

        clause_id = self.clause_ptr
        self.sentence[self.clause_ptr] = clause_with_literals
        self.clause_ptr += 1

        for lit in clause_with_literals:
            self.bve_watch.setdefault(lit, set()).add(clause_id)

        return 1

    def init_watch(self):
        for clause_id,clause in self.sentence.items():
            watch_literal1 = clause[0]
            watch_literal2 = clause[1]
            self.c2l_watch[clause_id] = [watch_literal1, watch_literal2]
            self.l2c_watch.setdefault(watch_literal1, []).append(clause_id)
            self.l2c_watch.setdefault(watch_literal2, []).append(clause_id)

    def read_cnf_file(self, cnf_filename):
        """ To read from .cnf file """
        cnf_file = open(cnf_filename, "r")
        self.bve_watch = {}
        for line in cnf_file.readlines():
            line = line.rstrip()
            line = line.split()
            first_word = line[0]
            if first_word == "c":
                continue
            elif first_word == "p":
                self._num_vars = int(line[2])
                self.stats._num_orig_clauses = int(line[3])
            else:
                ret = self.add_clause(line)
                if ret == 0:
                    break

        cnf_file.close()
        if self._bve_flag == "True":
            self.bve()
        self.orig_sentence = self.sentence.copy()
        self.init_watch()

    def is_tautological(self,clause):
        for lit in clause:
            if (lit > self._num_vars and lit-self._num_vars in clause) or (lit < self._num_vars and lit+self._num_vars in clause):
                return True

        return False
    
    def bve(self):
        start_time = time.time()
        self.stats._bve_flag = True
        clause_to_be_del = set()
        for var in range(1,self._num_vars+1):
            if var in self.v2a_watch:
                continue
            S_plus = self.bve_watch.setdefault(var,set())
            S_minus = self.bve_watch.setdefault(var + self._num_vars,set())
            var_total_counts = len(S_plus) + len(S_minus)
            if var_total_counts > 6:
                continue

            new_clauses = []
            # c1 c2 are two clause idx
            for c1 in S_plus:
                for c2 in S_minus:
                    new_clause = self.binary_resolute(self.sentence[c1],self.sentence[c2],var)
                    if self.is_tautological(new_clause):
                        continue
                    new_clauses.append(new_clause)

            if len(new_clauses) <= var_total_counts:
                # do elimination
                for c1 in S_plus:
                    clause_to_be_del.add(c1)
                for c2 in S_minus:
                    clause_to_be_del.add(c2)
                for new_clause in new_clauses:
                    self.sentence[self.clause_ptr] = new_clause
                    self.clause_ptr += 1
                    self.stats._bve_add_clauses += 1
                self.stats._bve_vars += 1


        for clause_id in clause_to_be_del:
            self.stats._bve_rm_clauses += 1
            del self.sentence[clause_id]
        end_time = time.time()
        self.stats._bve_time = end_time - start_time

    """ Decide: use the Decider class! """
    def decide(self):
        '''
        Method that chooses an uassigned variable and assigns it with a boolean value.
        Returns -1 if there are no variables to set. Else returns the variable to assigned.
        '''
        
        var, value_to_set = self.sat_decider.decide_var()

        if var == -1:
            return -1

        self._level += 1
        self._restarter.decisions += 1
        self._restarter.decidedVars.add(var)

        new_node = AssignedNode(var, value_to_set, self._level, None)
        self.v2a_watch[var] = new_node
        self._assignment.append(new_node)
        new_node.index = len(self._assignment) - 1

        self.stats._num_decisions += 1

        return var

    """ Core Functions for CDCL """
    def bcp(self, is_first_time):
        '''
        Perform boolean constraint propogation
        
        Parameters:
            is_first_time: Boolean which is set to True when this method is run initially and False for all other invocations
        Return:
            "CONFLICT" or "NO_CONFLICT" depending on whether a conflict arised while making the implications or not. 
            Returns "RESTART" depending on the number of conflicts encountered and the restart strategy used by the solver (if any)
        '''        
        last_assignment_pointer = len(self._assignment) - 1

        if is_first_time:
            last_assignment_pointer = 0

        propagated = []
        while last_assignment_pointer < len(self._assignment):

            last_assigned_node = self._assignment[last_assignment_pointer]

            if last_assigned_node.value is True:
                literal_that_is_falsed = last_assigned_node.var + self._num_vars
            else:
                literal_that_is_falsed = last_assigned_node.var

            itr = 0

            clauses_watched_by_falsed_literal = self.l2c_watch.setdefault(
                literal_that_is_falsed, []).copy()

            clauses_watched_by_falsed_literal.reverse()

            while itr < len(clauses_watched_by_falsed_literal):

                clause_id = clauses_watched_by_falsed_literal[itr]
                watch_list_of_clause = self.c2l_watch[clause_id]

                other_watch_literal = watch_list_of_clause[0]
                if other_watch_literal == literal_that_is_falsed:
                    other_watch_literal = watch_list_of_clause[1]

                other_watch_var = self.get_var_from_literal(other_watch_literal)
                is_negative_other = self.is_negative_literal(other_watch_literal)

                if other_watch_var in self.v2a_watch:
                    value_assgned = self.v2a_watch[
                        other_watch_var].value
                    if (is_negative_other and value_assgned is False) or (
                            not is_negative_other and value_assgned is True):
                        itr += 1
                        continue
                new_literal_to_watch = -1
                clause = self.sentence[clause_id]

                for lit in clause:
                    if lit not in watch_list_of_clause:
                        var_of_lit = self.get_var_from_literal(lit)

                        if var_of_lit not in self.v2a_watch:
                            new_literal_to_watch = lit
                            break
                        else:
                            node = self.v2a_watch[var_of_lit]
                            is_negative = self.is_negative_literal(lit)
                            if (is_negative and node.value is False) or (
                                    not is_negative and node.value is True):
                                new_literal_to_watch = lit
                                break

                if new_literal_to_watch != -1:
                    self.c2l_watch[clause_id].remove(
                        literal_that_is_falsed)
                    self.c2l_watch[clause_id].append(
                        new_literal_to_watch)
                    self.l2c_watch.setdefault(literal_that_is_falsed,
                                                        []).remove(clause_id)
                    self.l2c_watch.setdefault(new_literal_to_watch,
                                                        []).append(clause_id)

                else:
                    if other_watch_var not in self.v2a_watch:
                        value_to_set = not is_negative_other
                        assign_var_node = AssignedNode(other_watch_var,
                                                    value_to_set, self._level,
                                                    clause_id)
                        self.v2a_watch[
                            other_watch_var] = assign_var_node

                        self._assignment.append(assign_var_node)
                        assign_var_node.index = len(self._assignment) - 1

                        propagated.append(other_watch_var)
                        self.sat_decider.bcp_update(other_watch_var, value_to_set)
                        self.stats._num_implications += 1

                    else:
                        self._restarter.incre_conflict()
                        if self._restarter.get_restart_flag():
                            self.stats._restarts += 1
                            return "RESTART", propagated                    

                        conflict_node = AssignedNode(None, None, self._level,
                                                    clause_id)
                        self._assignment.append(conflict_node)

                        conflict_node.index = len(self._assignment) - 1

                        return "CONFLICT", propagated

                itr += 1

            last_assignment_pointer += 1

        return "NO_CONFLICT", propagated


    def binary_resolute(self, clause1, clause2, var):
        '''
        Method that performs binary resolution on two clauses with respect to one variable.
        *Used in `analyze_conflict()`.
        '''
        full_clause = clause1 + clause2
        full_clause = list(OrderedDict.fromkeys(full_clause))
        full_clause.remove(var)
        full_clause.remove(var + self._num_vars)
        return full_clause


    def is_valid_clause(self, clause, level):
        '''
        Method that checks if the passed clause is a valid conflict clause (with only one literal set at level). 
        Also finds the latest assigned literal set at level.
        *Used in `analyze_conflict()`.
        '''
        counter = 0
        maxi = -1
        cand = -1
        for lit in clause:
            var = self.get_var_from_literal(lit)
            node = self.v2a_watch[var]
            if node.level == level:
                counter += 1
                if node.index > maxi:
                    maxi = node.index
                    cand = node

        return counter == 1, cand

    def get_backtrack_level(self, conflict_clause, conflict_level):
        '''
        Method to get the backtrack level using the passed conflict clause and the conflict level.
        Returns the only literal assigned at the conflict level present in the conflict clause.
        *Used in `analyze_conflict()`.
        '''
        maximum_level_before_conflict_level = -1

        literal_at_conflict_level = -1

        for lit in conflict_clause:
            var = self.get_var_from_literal(lit)
            assigned_node = self.v2a_watch[var]
            if assigned_node.level == conflict_level:
                literal_at_conflict_level = lit
            else:
                if assigned_node.level > maximum_level_before_conflict_level:
                    maximum_level_before_conflict_level = assigned_node.level

        return maximum_level_before_conflict_level, literal_at_conflict_level

    def analyze_conflict(self):
        '''
        Analyze the conflict with first-UIP clause learning.
        Returns the backtrack level and the assignment node implied by the conflict clause that will be used for implications in `backtrack()`
        '''
        assigment_stack_pointer = len(self._assignment) - 1
        conflict_node = self._assignment[assigment_stack_pointer]
        conflict_level = conflict_node.level
        conflict_clause = self.sentence[conflict_node.clause]

        self._assignment.pop()

        if conflict_level == 0:
            return -1, None

        conflict_side = []

        while True:

            is_nice, prev_assigned_node = self.is_valid_clause(
                conflict_clause, conflict_level)

            if is_nice:
                break

            clause = self.sentence[prev_assigned_node.clause]
            var = prev_assigned_node.var
            conflict_side.append(var)
            conflict_clause = self.binary_resolute(conflict_clause, clause, var)


        if len(conflict_clause) > 1:
            self.stats._num_learned_clauses += 1
            clause_id = self.clause_ptr

            self.sentence[self.clause_ptr] = conflict_clause
            self.clause_ptr += 1

            self.l2c_watch.setdefault(conflict_clause[0],
                                                []).append(clause_id)
            self.l2c_watch.setdefault(conflict_clause[1],
                                                []).append(clause_id)

            self.c2l_watch[clause_id] = [
                conflict_clause[0], conflict_clause[1]
            ]

            backtrack_level, conflict_level_literal = self.get_backtrack_level(
                conflict_clause, conflict_level)

            conflict_level_var = self.get_var_from_literal(conflict_level_literal)

            is_negative_conflict_lit = self.is_negative_literal(
                conflict_level_literal)

            
            reasons = []
            for lit in conflict_clause:
                var = self.get_var_from_literal(lit)
                if var in self.v2a_watch:
                    node = self.v2a_watch[var]
                    if node.clause is None:
                        reasons += [var]
                    else:
                        reason_clause = self.sentence[node.clause]
                        reasons += [self.get_var_from_literal(lit) for lit in reason_clause]
            self.sat_decider.conflict_update(conflict_clause, conflict_level_var, conflict_side, reasons)

            value_to_set = True
            if is_negative_conflict_lit:
                value_to_set = False

            node = AssignedNode(conflict_level_var, value_to_set, backtrack_level,
                                clause_id)

            return backtrack_level, node
        else:
            literal = conflict_clause[0]
            var = self.get_var_from_literal(literal)
            is_negative_literal = self.is_negative_literal(literal)

            # Backtrack to level 0
            backtrack_level = 0

            # If conflict_level_literal is negative, its variable should be set False,
            # else it should be set True
            value_to_set = True
            if is_negative_literal:
                value_to_set = False

            # Create the node with var, value_to_set,backtrack_level(0)
            # Clause is set to None as this is implied by no clause
            # (added to level 0)
            node = AssignedNode(var, value_to_set, backtrack_level, None)

            # return the backtrack level and the assignment node
            return backtrack_level, node

    def backtrack(self, backtrack_level, node_to_add, restart_flag=False):
        '''
        Method used to backtrack the solver to the backtrack_level.
        It also adds the node_to_add to the assignment stack.

        Parameters:
            backtrack_level: the level to which the solver should backtrack(backjump)
            node_to_add: the implication node implied by the conflict clause to be added
            to the assignment stack at time of backtrack

        Return:
            None
        '''
        self._level = backtrack_level

        itr = len(self._assignment) - 1
        var_list = []
        while True:
            if itr < 0:

                break
            if self._assignment[itr].level <= backtrack_level:
                break
            else:
                del self.v2a_watch[
                    self._assignment[itr].var]

                node = self._assignment.pop(itr)
                var_list.append(node.var)
                del node

                # move to the next node
                itr -= 1

        
        self.sat_decider.backtrack_update(var_list,restart_flag)

        if node_to_add:
            self.v2a_watch[node_to_add.var] = node_to_add

            self._assignment.append(node_to_add)
            node_to_add.index = len(self._assignment) - 1
            
            self.sat_decider.bcp_update(node_to_add.var, node_to_add.value)
            self.stats._num_implications += 1

    """ SOLVE THE SAT PROBLEM! """
    def solve(self, cnf_filename):
        ''' The main method to solve the SAT problem. '''
        self.stats._input_file = cnf_filename
        self.stats._start_time = time.time()

        self.read_cnf_file(cnf_filename)

        self.sat_decider = Decider(self._decider, self.sentence.values(), self._num_vars)
        for node in self._assignment:
            self.sat_decider.unary_update(node.var)

        self.stats._read_time = time.time()

        self.stats._num_vars = self._num_vars
        self.stats._num_clauses = self.clause_ptr

        if self.stats._result == "UNSAT":
            # The case where implications from the unary clauses cause a conflict
            self.stats._complete_time = time.time()
        else:
            # solve the SAT problem
            first_time = True
            while True:
                while True:
                    temp = time.time()
                    result, propagated = self.bcp(first_time)

                    self.sat_decider.chb_update(propagated, result == "CONFLICT")

                    self.stats._bcp_time += time.time() - temp
                    if result == "NO_CONFLICT":
                        break

                    if result == "RESTART":
                        new_heuristic = self._restarter.choose()
                        self.backtrack(0, None, True)
                        self.sat_decider.change_heuristic(new_heuristic)
                        break

                    first_time = False

                    temp = time.time()
                    backtrack_level, node_to_add = self.analyze_conflict()

                    self.stats._analyze_time += time.time() - temp

                    if backtrack_level == -1:
                        self.stats._result = "UNSAT"
                        self.stats._complete_time = time.time()

                        break

                    temp = time.time()
                    self.backtrack(backtrack_level, node_to_add)

                    self.stats._backtrack_time += time.time() - temp

                if self.stats._result == "UNSAT":
                    break

                first_time = False

                temp = time.time()
                var_decided = self.decide()

                self.stats._decide_time += time.time() - temp

                if var_decided == -1:
                    # If var_decided is -1, it means all the variables have been assigned without any conflict
                    # problem is solved

                    self.stats._result = "SAT"

                    self.stats._complete_time = time.time()

                    break

        # store the result as files  
        if not os.path.isdir("Results"):
            os.mkdir("Results")

        inputfile_basename = os.path.basename(cnf_filename)

        # Extracts test case name from the base file name
        # eg. bmc-1 from bmc-1.cnf
        input_case_name = os.path.splitext(inputfile_basename)[0]

        # Create the filename for stats file
        # eg. Results/stats_bmc-1.txt
        stats_file_name = "Results/stats_" + input_case_name + ".txt"

        self.stats._output_statistics_file = stats_file_name

        original_stdout = sys.stdout
        sys.stdout = open(stats_file_name, "wt")
        self.stats.print_stats()
        sys.stdout = original_stdout

        if self.stats._result == "SAT":
            assgn_file_name = "Results/assgn_" + input_case_name + ".txt"
            self.stats._output_assignment_file = assgn_file_name

            self.assignment_dict = {}
            for var in self.v2a_watch:
                self.assignment_dict[var] = self.v2a_watch[var].value

            # the assignment file
            assgn_file = open(assgn_file_name, "w")
            assgn_file.write(json.dumps(self.assignment_dict))
            assgn_file.close
