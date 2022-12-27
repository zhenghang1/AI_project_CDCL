from utils import PriorityQueue


class Decider:

    def __init__(self, decider, sentence, num_vars) -> None:
        if decider is None or decider not in ["VSIDS", "LRB", "CHB"]:
            raise ValueError('The decider must be one from the list ["VSIDS","LRB","CHB"]')

        self.num_vars = num_vars
        self.curr_decider = None

        # VSIDS init
        self.vsids_incr = 1
        self.vsids_scores = [0]*(2*num_vars+1)

        for clause in sentence:
            for lit in clause:
                self.vsids_scores[lit] += 1

        # CHB init
        self.plays = set()
        self.chb_alpha = 0.4
        self.numConflicts = 0
        self.lastConflict = [0] * (num_vars + 1)
        self.chb_phase = [0] * (num_vars + 1)
        self.chb_scores = [0] * (num_vars + 1)  # only record variables, not literals

        # LRB init
        self.lrb_alpha = 0.4
        self.LearntCounter = 0
        self.lrb_scores = [0] * (num_vars + 1)
        self.assigned = [0] * (num_vars + 1)
        self.participated = [0] * (num_vars + 1)
        self.lrb_phase = [0] * (num_vars + 1)
        # rsr extension
        self.reasoned = [0] * (num_vars + 1)

        # build PriorityQueue correspond to the current decide heuristic method
        self.change_heuristic(decider)

    def is_negative_literal(self, literal):
        return literal > self.num_vars

    def get_var_from_literal(self, literal):
        if self.is_negative_literal(literal):
            return literal - self.num_vars
        return literal

    def decide_var(self):
        # called when needs a decide
        if self.curr_decider == "VSIDS":
            literal = self.vsids_priority_queue.get_top()
            if literal == -1:
                return -1, None
            var = self.get_var_from_literal(literal)
            is_neg = self.is_negative_literal(literal)
            value_to_set = not is_neg
            if is_neg:
                self.vsids_priority_queue.remove(var)
            else:
                self.vsids_priority_queue.remove(var+self.num_vars)
            # also change CHB
            # self.chb_priority_queue.remove(var)
            self.chb_phase[var] = value_to_set
            # also change LRB
            # self.lrb_priority_queue.remove(var)
            self.lrb_phase[var] = value_to_set

        elif self.curr_decider == "CHB":
            var = self.chb_priority_queue.get_top()
            if var == -1:
                return -1, None
            value_to_set = bool(self.chb_phase[var])
            # also change vsids
            # self.vsids_priority_queue.remove(var)
            # self.vsids_priority_queue.remove(var+self.num_vars)
            # also change LRB
            # self.lrb_priority_queue.remove(var)
            self.lrb_phase[var] = value_to_set

        else:  # LRB
            var = self.lrb_priority_queue.get_top()
            if var == -1:
                return -1, None
            value_to_set = bool(self.lrb_phase[var])
            # also change vsids
            # self.vsids_priority_queue.remove(var)
            # self.vsids_priority_queue.remove(var + self.num_vars)
            # also change CHB
            # self.chb_priority_queue.remove(var)
            self.chb_phase[var] = value_to_set

        self.plays = set([var])
        # LRB: this corresponds to OnAssign by branching
        self.assigned[var] = self.LearntCounter
        self.participated[var] = 0
        # rsr extension
        self.reasoned[var] = 0

        return var, value_to_set
    
    def unary_update(self,var):
        if self.curr_decider == "VSIDS":
            self.vsids_priority_queue.remove(var)
            self.vsids_priority_queue.remove(var+self.num_vars)
        elif self.curr_decider == "CHB":
            self.chb_priority_queue.remove(var)          


    def conflict_update(self, learned_clause, uip, conflict_side, reasons):
        # learned_clause: list of literals!
        # conflict_side: list of variables!
        # reasons: list of variables!
        self.numConflicts += 1
        self.LearntCounter += 1
        var_learnt_clause = [self.get_var_from_literal(lit) for lit in learned_clause]
        for lit in learned_clause:
            # update vsids
            self.vsids_scores[lit] += self.vsids_incr
            if self.curr_decider == "VSIDS":
                self.vsids_priority_queue.increase_update(lit, self.vsids_incr)
            # update chb
            var = self.get_var_from_literal(lit)
            self.lastConflict[var] = self.numConflicts
        # give more weightage to the recent conflict clausing literal
        self.vsids_incr += 0.75
        if self.chb_alpha > 0.06:
            self.chb_alpha -= 1e-6
        self.plays = set([uip])
        # update lrb
        if self.lrb_alpha > 0.06:
            self.lrb_alpha -= 1e-6
        for var in set(conflict_side+var_learnt_clause):
            self.participated[var] += 1
        # rsr extension
        for var in set(reasons)-set(learned_clause):
            self.reasoned[var] += 1

    def bcp_update(self, var, value_to_set):
        # called when var is implied in bcp
        # value_to_set is needed to keep the chb_phase
        # update vsids
        if self.curr_decider == "VSIDS":
            self.vsids_priority_queue.remove(var)
            self.vsids_priority_queue.remove(var+self.num_vars)
        # update chb
        elif self.curr_decider == "CHB":
            self.chb_priority_queue.remove(var)
        else:
            self.lrb_priority_queue.remove(var)

        self.chb_phase[var] = int(value_to_set)
        # update lrb, correspond to OnAssign by propagation
        self.assigned[var] = self.LearntCounter
        self.participated[var] = 0
        self.lrb_phase[var] = int(value_to_set)
        # rsr extension
        self.reasoned[var] = 0

    def chb_update(self, propagated, in_conflict):
        self.plays = self.plays.union(set(propagated))
        if in_conflict:
            multiplier = 1.0
        else:
            multiplier = 0.9
        for v in self.plays:
            reward = multiplier / (self.numConflicts -
                                   self.lastConflict[v] + 1)
            delta = self.chb_alpha * (reward - self.chb_scores[v])
            self.chb_scores[v] += delta
            if self.curr_decider == "CHB":
                self.chb_priority_queue.increase_update(v, delta)

    def backtrack_update(self, var_list):
        # called when backtrack unassigns some vars, put them in priority_queue
        # var_list: vars unassigned
        for var in var_list:
            # update vsids
            if self.curr_decider == "VSIDS":
                self.vsids_priority_queue.add(var, self.vsids_scores[var])
                self.vsids_priority_queue.add(var + self.num_vars, self.vsids_scores[var + self.num_vars])
            # update chb
            elif self.curr_decider == "CHB":
                self.chb_priority_queue.add(var, self.chb_scores[var])
            # update lrb, which corresponds to OnUnassign
            else:
                self.lrb_priority_queue.add(var, self.lrb_scores[var])
            interval = self.LearntCounter - self.assigned[var]
            if interval > 0:
                r = self.participated[var]/interval
                rsr = self.reasoned[var]/interval
                delta = self.lrb_alpha*(r+rsr-self.lrb_scores[var])
                self.lrb_scores[var] += delta
                if self.curr_decider == "LRB":
                    self.lrb_priority_queue.increase_update(var, delta)

    def change_heuristic(self, new_heuristic):
        if self.curr_decider == new_heuristic:
            return
        self.curr_decider = new_heuristic
        if self.curr_decider == "VSIDS":
            self.vsids_priority_queue = PriorityQueue(self.vsids_scores)
        elif self.curr_decider == "CHB":
            self.chb_priority_queue = PriorityQueue(self.chb_scores)
        else:
            self.lrb_priority_queue = PriorityQueue(self.lrb_scores)
