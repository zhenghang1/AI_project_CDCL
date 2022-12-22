

class Decider:
    def __init__(self,decider) -> None:
        self.curr_decider = decider
        self.vsids_priority_queue = PriorityQueue()
        self.lrb_priority_queue = PriorityQueue()
        self.chb_priority_queue = PriorityQueue()


