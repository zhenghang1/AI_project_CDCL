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

    Public Attributes:
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
    def __init__(self, decider="VSIDS", restarter="NO_RESTART"):
        '''
        Constructor for the SAT class

        Parameters:
            decider: the init decision heuristic used, should be of ["VSIDS","LRB","CHB"], default is "VSIDS"
            restarter: the restart strategy to be used, should be of ["GEOMETRIC","LUBY","NO_RESTART"], default is "NO_RESTART"
        
        '''
        self._num_clauses = 0
        self._num_vars = 0
        self._level = 0
        self.sentence = []
        self.l2c_watch = {}
        self.c2l_watch = {}
        # a dict to store the assignnode, with (var,node) as (key,value)
        self._variable_to_assignment_nodes = {}
        # a list store the node in the order of their assignment
        self._assignment = []
        self._init_decider = decider
        self._restarter = Restarter(restarter)
        self.stats = Statistics()


def is_negative_literal(self, literal):

    return literal > self._num_vars


SAT._is_negative_literal = is_negative_literal


def get_var_from_literal(self, literal):

    if self._is_negative_literal(literal):
        return literal - self._num_vars
    return literal


SAT._get_var_from_literal = get_var_from_literal


def add_clause(self, clause):
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

        if var not in self._variable_to_assignment_nodes:
            self.stats._num_implications += 1
            node = AssignedNode(var, value_to_set, 0, None)
            self._variable_to_assignment_nodes[var] = node
            self._assignment.append(node)
            node.index = len(self._assignment) - 1
        else:
            node = self._variable_to_assignment_nodes[var]
            if node.value != value_to_set:
                self.stats._result = "UNSAT"
                return 0
        return 1

    clause_with_literals = []

    for lit in clause:
        if lit[0] == '-':
            var = int(lit[1:])  
            clause_with_literals.append(var + self._num_vars)
        else:
            var = int(lit)
            clause_with_literals.append(var)

    clause_id = self._num_clauses
    self.sentence.append(clause_with_literals)
    self._num_clauses += 1

    watch_literal1 = clause_with_literals[0]
    watch_literal2 = clause_with_literals[1]

    self.c2l_watch[clause_id] = [watch_literal1, watch_literal2]

    self.l2c_watch.setdefault(watch_literal1, []).append(clause_id)
    self.l2c_watch.setdefault(watch_literal2, []).append(clause_id)

    return 1


SAT._add_clause = add_clause


def read_cnf_file(self, cnf_filename):
    cnf_file = open(cnf_filename, "r")
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
            ret = self._add_clause(line)
            if ret == 0:
                break
    cnf_file.close()


SAT._read_cnf_file = read_cnf_file


def decide(self):
    '''
    Method that chooses an uassigned variable and a boolean value for
    it and assigns the variable with that value

    Parameters:
        None

    Returns:
        -1 if there are no variables to set, else it returns the variable
        which is set
    '''
    # Look here!
    var, value_to_set = self.sat_decider.decide_var()

    if var == -1:
        return -1

    self._level += 1
    self._restarter.decisions += 1
    self._restarter.decidedVars.add(var)

    new_node = AssignedNode(var, value_to_set, self._level, None)
    self._variable_to_assignment_nodes[var] = new_node
    self._assignment.append(new_node)
    new_node.index = len(self._assignment) - 1

    self.stats._num_decisions += 1

    return var


SAT._decide = decide


def boolean_constraint_propogation(self, is_first_time):
    '''
    Parameters:
        is_first_time: Boolean which is set to True when this method is run initially and False for all
        other invocations

    Return:
        "CONFLICT" or "NO_CONFLICT" depending on whether a conflict arised while making the
        implications or not. Returns "RESTART" depending on the number of conflicts encountered
        and the restart strategy used by the solver (if any)
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

            other_watch_var = self._get_var_from_literal(other_watch_literal)
            is_negative_other = self._is_negative_literal(other_watch_literal)

            if other_watch_var in self._variable_to_assignment_nodes:
                value_assgned = self._variable_to_assignment_nodes[
                    other_watch_var].value
                if (is_negative_other and value_assgned is False) or (
                        not is_negative_other and value_assgned is True):
                    itr += 1
                    continue

            new_literal_to_watch = -1
            clause = self.sentence[clause_id]

            for lit in clause:
                if lit not in watch_list_of_clause:
                    var_of_lit = self._get_var_from_literal(lit)

                    if var_of_lit not in self._variable_to_assignment_nodes:
                        new_literal_to_watch = lit
                        break
                    else:
                        node = self._variable_to_assignment_nodes[var_of_lit]
                        is_negative = self._is_negative_literal(lit)
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
                if other_watch_var not in self._variable_to_assignment_nodes:
                    value_to_set = not is_negative_other
                    assign_var_node = AssignedNode(other_watch_var,
                                                   value_to_set, self._level,
                                                   clause_id)
                    self._variable_to_assignment_nodes[
                        other_watch_var] = assign_var_node

                    self._assignment.append(assign_var_node)
                    assign_var_node.index = len(self._assignment) - 1

                    # Look here!
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


# Add the method to the SAT class
SAT._boolean_constraint_propogation = boolean_constraint_propogation


def binary_resolute(self, clause1, clause2, var):
    '''
    Method that takes in two clauses, clause1 and clause2 and performs
    their binary resolution (as described above) with respect to the passed
    variable.

    Parameters:
        clause1: the first clause(list of literals)
        clause2: the second clause(list of literals)
        var: the variable with respect to which the binary resolution should be performed

    Return:
        the binary resolution of the passed clauses (Clause 1 and Clause 2) with respect to
        the passed variable (var)
    '''
    full_clause = clause1 + clause2
    full_clause = list(OrderedDict.fromkeys(full_clause))
    full_clause.remove(var)
    full_clause.remove(var + self._num_vars)
    return full_clause


SAT._binary_resolute = binary_resolute


def is_valid_clause(self, clause, level):
    '''
    Method that checks if the passed clause is a valid conflict clause (
    with only one literal set at level). This method while traversing the clause
    also finds the latest assigned literal set at level

    Parameters:
        clause: the clause that has to be checked
        level: the level at which the conflict occurs

    Return:
        a boolean which is True if the passed clause is a valid conflict clause
        the latest assigned literal set at level
    '''
    counter = 0
    maxi = -1
    cand = -1
    for lit in clause:
        var = self._get_var_from_literal(lit)
        node = self._variable_to_assignment_nodes[var]
        if node.level == level:
            counter += 1
            if node.index > maxi:
                maxi = node.index
                cand = node

    return counter == 1, cand


SAT._is_valid_clause = is_valid_clause


def get_backtrack_level(self, conflict_clause, conflict_level):
    '''
    Method to get the backtrack level (level to which the solver should jump)
    using the passed conflict clause and the conflict level. The method also
    returns the only literal assigned at the conflict level present in the
    conflict clause.

    Parameters:
        conflict_clause: the passed conflict clause
        conflict_level: the passed conflict level

    Return:
        the level to which the solver should backtrack and
        the only literal assigned at the conflict_level in the conflict_clause
    '''
    maximum_level_before_conflict_level = -1

    literal_at_conflict_level = -1

    for lit in conflict_clause:
        var = self._get_var_from_literal(lit)
        assigned_node = self._variable_to_assignment_nodes[var]
        if assigned_node.level == conflict_level:
            literal_at_conflict_level = lit
        else:
            if assigned_node.level > maximum_level_before_conflict_level:
                maximum_level_before_conflict_level = assigned_node.level

    return maximum_level_before_conflict_level, literal_at_conflict_level


SAT._get_backtrack_level = get_backtrack_level


def analyze_conflict(self):
    '''
    Method that is called when a conflict occurs during the
    Boolean Constrain Propogation (BCP). It analyzes the conflict,
    generates the valid conflict clause (as discussed above) and adds
    it to the clause database. It then returns the backtrack level
    and the assignment node implied by the conflict clause that will be used
    for implications once the solver backtracks (described below in the algorithm).

    Parameters:
        None

    Return:
        the level to which the solver should jump back and
        the assignement node implied by the conflict clause
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

        is_nice, prev_assigned_node = self._is_valid_clause(
            conflict_clause, conflict_level)

        if is_nice:
            break

        clause = self.sentence[prev_assigned_node.clause]
        var = prev_assigned_node.var
        conflict_side.append(var)
        conflict_clause = self._binary_resolute(conflict_clause, clause, var)

    if len(conflict_clause) > 1:
        self.stats._num_learned_clauses += 1
        clause_id = self._num_clauses

        self._num_clauses += 1
        self.sentence.append(conflict_clause)

        self.l2c_watch.setdefault(conflict_clause[0],
                                              []).append(clause_id)
        self.l2c_watch.setdefault(conflict_clause[1],
                                              []).append(clause_id)

        self.c2l_watch[clause_id] = [
            conflict_clause[0], conflict_clause[1]
        ]

        backtrack_level, conflict_level_literal = self._get_backtrack_level(
            conflict_clause, conflict_level)

        conflict_level_var = self._get_var_from_literal(conflict_level_literal)

        is_negative_conflict_lit = self._is_negative_literal(
            conflict_level_literal)

        # Look here!
        reasons = []
        for lit in conflict_clause:
            var = self._get_var_from_literal(lit)
            if var in self._variable_to_assignment_nodes:
                node = self._variable_to_assignment_nodes[var]
                if node.clause is None:
                    reasons += [var]
                else:
                    reason_clause = self.sentence[node.clause]
                    reasons += [self._get_var_from_literal(lit) for lit in reason_clause]
        self.sat_decider.conflict_update(conflict_clause, conflict_level_var, conflict_side, reasons)

        value_to_set = True
        if is_negative_conflict_lit:
            value_to_set = False

        node = AssignedNode(conflict_level_var, value_to_set, backtrack_level,
                            clause_id)

        return backtrack_level, node
    else:
        literal = conflict_clause[0]
        var = self._get_var_from_literal(literal)
        is_negative_literal = self._is_negative_literal(literal)

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


SAT._analyze_conflict = analyze_conflict


def backtrack(self, backtrack_level, node_to_add):
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
            del self._variable_to_assignment_nodes[
                self._assignment[itr].var]

            node = self._assignment.pop(itr)
            var_list.append(node.var)
            del node

            # move to the next node
            itr -= 1

    # Look here!
    self.sat_decider.backtrack_update(var_list)
    if node_to_add:
        self._variable_to_assignment_nodes[node_to_add.var] = node_to_add

        self._assignment.append(node_to_add)
        node_to_add.index = len(self._assignment) - 1
        # Look here!
        self.sat_decider.bcp_update(node_to_add.var, node_to_add.value)
        self.stats._num_implications += 1


SAT._backtrack = backtrack


def solve(self, cnf_filename):
    '''
    The main method which is public in the SAT class
    and solves the SAT problem instance present in
    the passed filename. It prints "SAT" or "UNSAT"
    depending on whether the problem was satisfiable
    or not.

    Parameters:
        cnf_filename: Name of the file having the SAT formula (DIMACS CNF format)
        to be solved

    Return:
        None
    '''

    # Set the input file name in the stats object
    self.stats._input_file = cnf_filename

    # Set the start time in the stats object
    self.stats._start_time = time.time()

    # Call the _read_cnf_file method to
    # read the input and process the clauses
    self._read_cnf_file(cnf_filename)

    # Look here!
    self.sat_decider = Decider(self._init_decider, self.sentence, self._num_vars)
    for node in self._assignment:
        self.sat_decider.unary_update(node.var)

    # Once read is complete, store the time
    self.stats._read_time = time.time()

    # Set the number of variables and clauses in the stats object
    self.stats._num_vars = self._num_vars
    self.stats._num_clauses = self._num_clauses

    if self.stats._result == "UNSAT":
        # The case where implications from the unary clauses
        # cause a conflict

        # Store the time when the result is
        # ready to the stats object
        self.stats._complete_time = time.time()

    else:
        # We now solve the SAT problem

        # Indicating that BCP runs first time
        first_time = True

        # The main alogrithm loop
        while True:

            # Perform the Boolean Constraint Propogation untill there are no
            # conflicts
            while True:

                # Perform the BCP and store its return value in result
                temp = time.time()
                result, propagated = self._boolean_constraint_propogation(first_time)

                # Look here!
                self.sat_decider.chb_update(propagated, result == "CONFLICT")

                # Increase the time spend in BCP (stored in the stats object)
                self.stats._bcp_time += time.time() - temp

                # Break if no conflict
                if result == "NO_CONFLICT":
                    break

                # If "RESTART" is returned, it means
                # we need to restart the solver
                if result == "RESTART":
                    # Solver is restarted by undoing all the decisions
                    # and implications made starting from Level 1
                    # (As the level 0 decisions and implications are ones
                    # due to the unary clauses and so are fixed)
                    # So, we backtrack to level 0 to restart the solver
                    new_heuristic = self._restarter.choose()
                    self._backtrack(0, None)
                    self.sat_decider.change_heuristic(new_heuristic)
                    break

                # Set first_time to False as we want it
                # to be true only once initially
                first_time = False

                # If there is a conflict, call _analyze_conflict method to
                # analyze it
                temp = time.time()
                backtrack_level, node_to_add = self._analyze_conflict()

                # Increase the time spend in analyzing (stored in the stats object)
                self.stats._analyze_time += time.time() - temp

                # If backtrack level is -1, it means a conflict at level 0,
                # so the problem is UNSAT.
                if backtrack_level == -1:
                    # Store the result in the stats object
                    self.stats._result = "UNSAT"

                    # Store the time when the result is
                    # ready to the stats object
                    self.stats._complete_time = time.time()

                    # Break out of the BCP loop
                    # as the problem is solved
                    break

                # Backtrack to the backtrack_level
                # node_to_add is added to the assignment stack in this
                # method and this woll be used to get further implications
                # when _boolean_constraint_propogation is called again in
                # the next iteration
                temp = time.time()
                self._backtrack(backtrack_level, node_to_add)

                # Increase the time spend in backtracking (stored in the stats object)
                self.stats._backtrack_time += time.time() - temp

            if self.stats._result == "UNSAT":
                # Means that problem was proved to be UNSAT during BCP
                # so we break out of the external loop
                break

            # Set first_time to False as we want it
            # to be true only once initially
            first_time = False

            # If all possible implications are made without conflicts,
            # then the solver decides on an unassigned variable
            # using the _decide method
            temp = time.time()
            var_decided = self._decide()

            # Increase the time spend in deciding (stored in the stats object)
            self.stats._decide_time += time.time() - temp

            if var_decided == -1:
                # If var_decided is -1, it means all the variables
                # have been assigned without any conflict and so the
                # input problem is satisfiable.
                # If this is not the case, then the external while loop
                # will again call the propogation loop and this cycle of
                # propogation and decision will continue until the
                # problem is solved

                # print the result

                # Store the result in the stats object
                self.stats._result = "SAT"

                # Store the time when the result is
                # ready to the stats object
                self.stats._complete_time = time.time()

                # Break out of the external while loop
                # as the problem is solved
                break

    # Create the Results directory if it does not exists
    if not os.path.isdir("Results"):
        os.mkdir("Results")

    # Extracts base file name from file path
    # eg. bmc-1.cnf from test/sat/bmc-1.cnf
    inputfile_basename = os.path.basename(cnf_filename)

    # Extracts test case name from the base file name
    # eg. bmc-1 from bmc-1.cnf
    input_case_name = os.path.splitext(inputfile_basename)[0]

    # Create the filename for stats file
    # eg. Results/stats_bmc-1.txt
    stats_file_name = "Results/stats_" + input_case_name + ".txt"

    # Set the stats file name to _output_statistics_file
    # stored in the statistics object
    self.stats._output_statistics_file = stats_file_name

    # Writing the stats to the stats file

    # Store the original standard output
    original_stdout = sys.stdout

    # Set the standard output to point to the stats file
    sys.stdout = open(stats_file_name, "wt")

    # Call the print stats which actually writes in
    # the file as standard output is directed towards the
    # stats file
    self.stats.print_stats()

    # Restore the standard output once the stats file is
    # written
    sys.stdout = original_stdout

    if self.stats._result == "SAT":
        # If the problem is SAT

        # Create a filename for the assignment file
        # eg. Results/assgn_bmc-1.txt
        assgn_file_name = "Results/assgn_" + input_case_name + ".txt"

        # Set the assgn file name to _output_assignment_file
        # stored in the statistics object
        self.stats._output_assignment_file = assgn_file_name

        # Create a dictionary of variable to its assigned boolean
        # value
        assignment_dict = {}

        # Traverse the _variable_to_assignment_nodes and for each variable
        # store its set value in assignment_dict
        for var in self._variable_to_assignment_nodes:
            assignment_dict[var] = self._variable_to_assignment_nodes[
                var].value

        # Open the assignment file
        assgn_file = open(assgn_file_name, "w")

        # Write the dictionary into the file by
        # serializing it through json.dumps() method
        assgn_file.write(json.dumps(assignment_dict))

        # Close the assignment file
        assgn_file.close


# Add the method to the SAT class
SAT.solve = solve

# sat = SAT("LRB", "NO_RESTART")
# sat.solve("hw3/examples/bmc-1.cnf")
# sat.stats.print_stats()
