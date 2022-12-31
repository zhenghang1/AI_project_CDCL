from utils import LubyGenerator
import numpy as np


class Restarter:

    def __init__(self, restarter, decider="CHB", base=1024) -> None:
        if restarter is None or restarter not in ["GEOMETRIC", "LUBY", "NO_RESTART"]:
            raise ValueError('The restarter must be one from the list ["GEOMETRIC","LUBY","NO_RESTART"]')

        # This stores the number of conflicts before restart and is set to 0 at each restart
        self.conflicts_count = 0
        self.conflict_limit = 0
        self.deciders = ["LRB", "CHB","VSIDS"]
        self.counts = [0] * len(self.deciders)
        self.expected_reward = [0] * len(self.deciders)
        self.last_arm = self.deciders.index(decider)
        self.num_restarts = 0
        self.base = base
        self.decisions = 0
        self.decidedVars = set()
        if restarter == "GEOMETRIC":
            # If the GEOMETRIC restart strategy is used, then initialize the conflict limit with 512
            self.conflict_limit = self.base

            # This is the limit multiplier by which the conflict limit will be multiplied after each restart
            self.limit_mult = 2

        if restarter == "LUBY":
            # If the LUBY restart strategy is used

            # We set base (b) as 512 here
            luby_base = self.base
            self.luby = LubyGenerator(luby_base)

            # Reset the luby sequencer to initialize it
            self.luby.reset_luby()

            # Intialize the conflict limit with base * the first luby number fetched using the get_next_luby_number()
            self.conflict_limit = self.luby.get_next_luby_number()

        # This stores the number of conflicts before restart and is set to 0 at each restart
        self.conflicts_count = 0

        # Set _restarter to the passed restart strategy
        self.restarter = restarter

    def incre_conflict(self):
        if self.restarter == "NO_RESTART":
            return

        self.conflicts_count += 1

    def get_restart_flag(self):
        if self.restarter == "NO_RESTART":
            return False

        if self.conflicts_count < self.conflict_limit:
            return False

        self.conflicts_count = 0
        if self.restarter == "GEOMETRIC":
            self.conflict_limit *= self.limit_mult

        if self.restarter == "LUBY":
            self.conflict_limit = self.luby.get_next_luby_number()

        return True

    def choose(self):
        # call if restart, namely when update_state() returns True
        # return a decider name
        self.num_restarts += 1
        r = np.log2(self.decisions) / len(self.decidedVars)
        self.decisions = 0
        self.decidedVars = set()

        self.expected_reward[self.last_arm] = 1. / (self.counts[self.last_arm] + 1) * (r - self.expected_reward[self.last_arm])
        self.counts[self.last_arm] += 1
        ucb = self.expected_reward+ np.sqrt(4.* np.log((self.num_restarts + 1) / (np.array(self.counts) + 1)))
        print("Ready for restart, scores for {} is :".format(self.deciders),ucb)
        self.last_arm = np.argmax(ucb)
        print("New heuristic:",self.deciders[self.last_arm],'\n')
        return self.deciders[self.last_arm]
