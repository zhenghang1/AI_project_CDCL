from utils import LubyGenerator

class Restarter:
    def __init__(self,restarter) -> None:
        if restarter == None or restarter not in ["GEOMETRIC","LUBY","NO_RESTART"]:
            raise ValueError('The restarter must be one from the list ["GEOMETRIC","LUBY","NO_RESTART"]')
        
        # This stores the number of conflicts before restart and is set to 0 at each restart
        self.conflicts_count = 0
        self.conflict_limit = 0

        if restarter == "GEOMETRIC":
            # If the GEOMETRIC restart strategy is used, then initialize the conflict limit with 512
            self.conflict_limit = 512
            
            # This is the limit multiplier by which the conflict limit will be multiplied after each restart
            self.limit_mult = 2
            
        if restarter == "LUBY":
            # If the LUBY restart strategy is used

            # We set base (b) as 512 here
            luby_base = 512
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

