from decider import Decider
from restarter import Restarter


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
    
    def __init__(self,decider,restarter=None):
        '''
        Constructor for the SAT class
        
        Parameters:
            to_log: a boolean (True/False) which indicates whether the solver should log the progress while 
            solving the problem
            decider: the decision heuristic used while deciding the next variable to be assigned and the value
            to be assigned to it in the _decide method
            restarter: the restart strategy to be used by the SAT solver (None set by default, so if nothing is
            passed, restarting will not be used) 
        
        Return:
            initialized SAT object
        '''
        
        # Decision level (level at which the solver is in backtracking tree)
        self.level = 0
        
        # List of clauses where each clause is stored as a list of literals as explained above.
        self.sentence = []
        
        # Dictionary mapping a literal to the list of clauses that contains the literal
        self.l2c_watch = {}
        
        # Dictionary mapping a clause to 2 of the list of literals which are contained in the clause and not assigned False
        self.c2l_watch = {}
        
        # Dictionary mapping the variables to their assignment nodes
        self.v2a_watch = {}
        
        # A stack(list) that stores the assignment nodes in order of their assignment
        self.assignment = []

        # 
        self.decided_idxs = []
        
        # The decision heuristic to be used while solving the SAT problem.
        # The decider must be ORDERED, VSIDS or MINISAT (discussed above) (Raise error if it is not one of them)
        self.decider = Decider(decider)

        self.restarter = Restarter(restarter)
               
        # Statistics object used to store the statistics  of the problem being solved
        self.stats = Statistics()
    
    def bcp(sentence):