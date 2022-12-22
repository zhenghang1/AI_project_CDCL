from utils import PriorityQueue

class Decider:
    def __init__(self,decider,sentence,num_vars) -> None:
        if decider == None or decider not in ["VSIDS","LRB","CHB"]:
            raise ValueError('The decider must be one from the list ["VSIDS","LRB","CHB"]')

        self.curr_decider = decider
        self.lrb_priority_queue = PriorityQueue()
        self.chb_priority_queue = PriorityQueue()

        # VSIDS init
        self.vsids_incr = 1
        self.vsids_scores = {}
        for lit in range(-num_vars, num_vars + 1):
            self.vsids_scores[lit] = 0

        for clause in sentence:
            for lit in clause:
                self.vsids_scores[lit] += 1
        self.vsids_priority_queue = PriorityQueue(self.vsids_scores)

    def decide_lit(self):
        if self.curr_decider == "VSIDS":
            literal = self.vsids_priority_queue.get_top()
            self.vsids_priority_queue.remove(-1*literal)
            return literal

    
    def conflict_update(self,learned_clause):
        if self.curr_decider == "VSIDS":
            for lit in learned_clause:
                self.vsids_scores[lit] += self.vsids_incr
                self.vsids_priority_queue.increase_update(lit,self.vsids_incr)
                # give more weightage to the recent conflict clausing literal
                self.vsids_incr += 0.75

    def bcp_update(self,lit):
        if self.curr_decider == "VSIDS":
            self.vsids_priority_queue.remove(lit)
            self.vsids_priority_queue.remove(-1*lit)

    def backtrack_update(self,lit_list):
        if self.curr_decider == "VSIDS":
            for lit in lit_list:
                self.vsids_priority_queue.add(lit,self.vsids_scores[lit])
                self.vsids_priority_queue.add(-1*lit,self.vsids_scores[-1*lit])


    def change_heuristic(self):
        if self.curr_decider == "VSIDS":
            self.vsids_incr = 1
        pass