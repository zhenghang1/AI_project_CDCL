class Restarter:
    def __init__(self,restarter) -> None:
        
        if restarter == None:
            # If no restart strategy passed, set _restarter to None
            self.restarter = None
        else:         
            if restarter not in ["GEOMETRIC","LUBY"]:
                # Check that the passed strategy should be one of the GEOMETRIC or LUBY(as discussed above)
                # Raise error if it is not one of them
                raise ValueError('The restarter must be one from the list ["GEOMETRIC","LUBY"]')
            
            if restarter == "GEOMETRIC":
                # If the GEOMETRIC restart strategy is used, then initialize the conflict limit with 512
                self.conflict_limit = 512
                
                # This is the limit multiplier by which the conflict limit will be multiplied after each restart
                self.limit_mult = 2
                
                # This stores the number of conflicts before restart and is set to 0 at each restart
                self.conflicts_before_restart = 0
            
            if restarter == "LUBY":
                # If the LUBY restart strategy is used
                
                # Reset the luby sequencer to initialize it
                reset_luby()
                
                # We set base (b) as 512 here
                self.luby_base = 512
                
                # Intialize the conflict limit with base * the first luby number fetched using the get_next_luby_number()
                self.conflict_limit = self._luby_base * get_next_luby_number()
                
                # This stores the number of conflicts before restart and is set to 0 at each restart
                self.conflicts_before_restart = 0           
            
            # Set _restarter to the passed restart strategy
            self.restarter = restarter    