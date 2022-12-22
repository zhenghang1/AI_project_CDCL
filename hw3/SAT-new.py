import os
import sys
import time
import json
import random
from collections import OrderedDict

# Import the Priority Queue class from PriorityQueue.py file
from utils import PriorityQueue

# Import the Luby Sequence Generator methods from LubyGenerator.py file
from utils import LubyGenerator

from decider import Decider
from restarter import Restarter


class Statistics:
    """
    Class used to store the various statistics measuerd while solving
    the SAT problem and defines method to print the statistics.
    
    Public Attributes:
        None
        
    Public Methods:
        print_stats(): Prints the statistics gathered during the solving of the SAT instance
    """
    
    def __init__(self):
        '''
        Constructor for the Statistics class.
        
        Arguments:
            None
        
        Return:
            intialized Statistics object
        '''    
        
        # Input file in which the problem is stored
        self._input_file = "" 
        
        # Path of the output statistics file used to store the statistics for the solved problem
        self._output_statistics_file = ""
        
        # Path of the output assignment file which stores the satisfying assignment
        # if the problem is satisfied, it is empty if the problem is UNSAT
        self._output_assignment_file = ""

        # Result of the SAT solver (SAT or UNSAT)
        self._result = ""
        
        # Number of variables in the problem
        self._num_vars = 0
        
        # Original number of clauses present in the problem
        self._num_clauses = 0
        
        # Number of clauses learned by the solver during the conflict analysis
        self._num_learned_clauses = 0
        
        # Number of decisions made by the solver
        self._num_decisions = 0
        
        # Number of implications made by the solver (These are assignments which are not decided but are implied from the decisions)
        self._num_implications = 0

        # Number of restarts
        self._num_restarts = 0
        
        # Time at which the solver starts solving the problem
        self._start_time = 0
        
        # Time at which the solver is done reading the problem
        self._read_time = 0
        
        # Time at which the solver has completed solving the problem
        self._complete_time = 0
        
        # Time which the solver spend while performing BCP
        self._bcp_time = 0
        
        # Time which the solver spend while deciding (in _decide method)
        self._decide_time = 0
        
        # Time which the solver spend while analyzing the conflicts
        self._analyze_time = 0
        
        # Time which the solver spend while backtracking
        self._backtrack_time = 0
    
    def print_stats(self):
        '''
        Method to print the statistics.
        
        Arguments:
            None
            
        Return:
            None
        '''
        
        # Print the stored statistics with appropriate labels of what the stats signify
        print("=========================== STATISTICS ===============================")
        print("Solving formula from file: ",self._input_file)
        print("Vars:{}, Clauses:{} Stored Clauses:{}".format(str(self._num_vars),str(self._num_orig_clauses),str(self._num_clauses)))
        print("Input Reading Time: ",self._read_time - self._start_time)
        print("-------------------------------")
        print("Restarts: ",self._num_restarts)
        print("Learned clauses: ",self._num_learned_clauses)
        print("Decisions made: ",self._num_decisions)
        print("Implications made: ",self._num_implications)
        print("Time taken: ",self._complete_time-self._start_time)
        print("----------- Time breakup ----------------------")
        print("BCP Time: ",self._bcp_time)
        print("Decide Time: ",self._decide_time)
        print("Conflict Analyze Time: ",self._analyze_time)
        print("Backtrack Time: ",self._backtrack_time)
        print("-------------------------------")
        print("RESULT: ",self._result)
        print("Statistics stored in file: ",self._output_statistics_file)
        
        # Check if the result of the problem is
        # SAT and if it is, then show the
        # assignement file name
        if self._result == "SAT":
            print("Satisfying Assignment stored in file: ",self._output_assignment_file)
        print("======================================================================")  


class SAT:
    """
    Class to store the data structures that are maintained while solving the SAT problem.
    It also stores the statistics of the solved problem and the methods that are used to solve the
    SAT problem.
    
    Public Attributes:
        stats: The statistics object that has the statistics of the solved SAT problem
    
    Public Methods:
        solve(filename): Takes as argument the filename which has the problem instance in the DIMACS CNF format 
        and solves it
    """
    
    def __init__(self, init_decider:str, use_restart:bool):
        '''
        Constructor for the SAT class
        
        Parameters:
            init_decider: a string (VSIDS/) which indicates the decide heuristic to initialize `self._decider`
            use_restart: a boolean (True/False) which indicates whether to use `restart` strategy
        
        Return:
            initialized SAT object
        '''
        # Statistics object used to store the statistics of the problem being solved
        self._stats = Statistics()
        
        # List of clauses where each clause is stored as a list of literals as explained above.
        self._sentence = []
        
        # Dictionary mapping a literal to the list of clauses the literal watches
        self._l2c_watch = {}
        
        # Dictionary mapping a clause to the list of literals that watch the clause
        self._c2l_watch = {}
        
        # A stack(list) that stores the assignment in order
        self._assignment = []

        # Dictionary mapping a vriable to 0/1 indicating whether it has been assigned
        self._v2a_watch = {}

        # Decision level log
        self._decided_idxs = []
        
        # The decider for the SAT problem
        # The decider must be VSIDS, ...
        self._decider = Decider(init_decider)

        # The restarter for the SAT problem
        self._restarter = Restarter(use_restart)

    def bcp(self, up_idx=0):
        """
        Propagate unit clauses with watched literals.

        Parameters:
            up_idx: record which assignment triggers the BCP
        Return:
            the antecedent of the conflict; `None` is returned if there's no conflict
        """
        # For fast checking if a literal is assigned.
        assigned_lits = [a[0] for a in self._assignment]

        # If the assignment is empty, try BCP.
        if len(self._assignment) == 0:
            assert up_idx == 0

            for clause_idx, watched_lits in self._c2l_watch.items():
                if len(watched_lits) == 1:
                    assigned_lits.append(watched_lits[0])
                    self._assignment.append((watched_lits[0], clause_idx))
                    self._decider.bcp_update(watched_lits[0])   # update `_decider`

        # If it is after conflict analysis, directly assign the literal.
        elif up_idx == len(self._assignment):  # we use `up_idx = len(assignment)` to indicate after-conflict BCP
            neg_first_uip = self._sentence[-1][-1]
            self._assignment.append((neg_first_uip, len(self._sentence) - 1))
            self._decider.bcp_update(neg_first_uip)   # update `_decider`

        # Propagate until no more unit clauses.
        while up_idx < len(self._assignment):
            lit, _ = self._assignment[up_idx]
            watching_clause_idxs = self._l2c_watch[-lit].copy()

            for clause_idx in watching_clause_idxs:
                if len(self._sentence[clause_idx]) == 1: return self._sentence[clause_idx]

                another_lit = self._c2l_watch[clause_idx][0] if self._c2l_watch[clause_idx][1] == -lit else self._c2l_watch[clause_idx][1]
                if another_lit in assigned_lits:
                    continue

                is_new_lit_found = False
                for tmp_lit in self._sentence[clause_idx]:
                    if tmp_lit != -lit and tmp_lit != another_lit and -tmp_lit not in assigned_lits:
                        self._c2l_watch[clause_idx].remove(-lit)
                        self._c2l_watch[clause_idx].append(tmp_lit)
                        self._l2c_watch[-lit].remove(clause_idx)
                        self._l2c_watch[tmp_lit].append(clause_idx)
                        is_new_lit_found = True
                        break

                if not is_new_lit_found:
                    if -another_lit in assigned_lits:
                        return self._sentence[clause_idx]  # NOTE: return a clause, not the index of a clause
                    else:
                        assigned_lits.append(another_lit)
                        self._assignment.append((another_lit, clause_idx))
                        self._decider.bcp_update(another_lit)   # update `_decider`

            up_idx += 1

        return None  # indicate no conflict; other return the antecedent of the conflict

    def decide(self):
        """
        Decide which variable to assign and whether to assign True or False.
        
        Parameters:
            None
        Return:
            an integer indicating which variable to assign and whether to assign True or False
        """
        assigned_lit = self._decider.decide()
        return assigned_lit

    def update_scores(self):
        """
        Update scores for VSIDS, ```.

        Parameters:
            None
        Return:
            None
        """
        pass

    def analyze_conflict(self, conflict_ante):
        """
        Analyze the conflict with first-UIP clause learning.

        Parameters:
            conflict_ante: the conflict antecedent returned by `self.bcp()`
        Return:
            backtrack_level
            learned_clause
        """
        backtrack_level, learned_clause = None, []

        # Check whether the conflict happens without making any decision.
        if len(self._decided_idxs) == 0:
            return -1, []

        # For fast checking if a literal is assigned.
        assigned_lits = [a[0] for a in self._assignment]

        # Find the first-UIP by repeatedly applying resolution.
        learned_clause = conflict_ante.copy()

        while True:
            lits_at_conflict_level = assigned_lits[self._decided_idxs[-1]:]
            clause_lits_at_conflict_level = [-lit for lit in learned_clause if -lit in lits_at_conflict_level]

            if len(clause_lits_at_conflict_level) <= 1:
                break

            # Apply the binary resolution rule.
            is_resolved = False
            while not is_resolved:
                lit, clause_idx = self._assignment.pop()
                if -lit in learned_clause:
                    learned_clause = list(set(learned_clause + self._sentence[clause_idx]))
                    learned_clause.remove(lit)
                    learned_clause.remove(-lit)
                    is_resolved = True

        # Order the literals of the learned clause. This is for:
        # 1) determining the backtrack level;
        # 2) watching the negation of the first-UIP and the literal at the backtrack level.
        lit_to_assigned_idx = {lit: assigned_lits.index(-lit) for lit in learned_clause}
        learned_clause = sorted(learned_clause, key=lambda lit: lit_to_assigned_idx[lit])

        # Decide the level to backtrack to as the second highest decision level of `learned_clause`.
        if len(learned_clause) == 1:
            backtrack_level = 0
        else:
            second_highest_assigned_idx = lit_to_assigned_idx[learned_clause[-2]]
            backtrack_level = next((level for level, assigned_idx in enumerate(self._decided_idxs) if assigned_idx > second_highest_assigned_idx), 0)

        return backtrack_level, learned_clause
    
    def backtrack(self, level):
        """
        Backtrack by deleting assigned variables.

        Parameters:
            level: the backtrack level
        Return:
            None
        """
        # update `decider`
        del_lits = [d[0] for d in self._assignment[self._decided_idxs[level]:]]
        self._decider.backtrack_update(del_lits)

        del self._assignment[self._decided_idxs[level]:]
        del self._decided_idxs[level:]
    
    def add_learned_clause(self, learned_clause):
        """
        Add learned clause to the sentence and update watch.

        Parameters:
            learned_clause: the learned clause returned by `self.analyze_conflict()`
        Return:
            None
        """
        # Add the learned clause to the sentence.
        self._sentence.append(learned_clause)

        # Update watch.
        clause_idx = len(self._sentence) - 1
        self._c2l_watch[clause_idx] = []

        # Watch the negation of the first-UIP and the literal at the backtrack level.
        # Be careful that the watched literals may be assigned.
        for lit in learned_clause[::-1]:
            if len(self._c2l_watch[clause_idx]) < 2:
                self._c2l_watch[clause_idx].append(lit)
                self._l2c_watch[lit].append(clause_idx)
            else:
                break
    
    def restart(self):
        """retart"""
        self._restarter.restart()

    def cdcl_run(self):
        """
        Run a CDCL solver for the SAT problem.
        
        Parameters:
            None
        Return:
            the SAT entity
        """
        # Run BCP.
        if self.bcp() is not None:
            return None  # indicate UNSAT

        # Main loop.
        while len(self._assignment) < self._stats._num_vars:
            # Make a decision.
            assigned_lit = self.decide()
            self._decided_idxs.append(len(self._assignment))
            self._assignment.append((assigned_lit, None))

            # Run BCP.
            conflict_ante = self.bcp(len(self._assignment) - 1)
            while conflict_ante is not None:
                # Learn conflict.
                backtrack_level, learned_clause = self.analyze_conflict(conflict_ante)
                self.add_learned_clause(learned_clause)

                # Update scores for VSIDS/.
                self._decider.conflict_update(learned_clause)

                # Backtrack.
                if backtrack_level < 0:
                    return None

                self.backtrack(backtrack_level)

                # Propagate watch.
                conflict_ante = self.bcp(len(self._assignment))

        return self