from SAT_new import SAT
from utils import read_cnf
import argparse
import sys

if __name__ == "__main__":
    # File name of the file containing the input problem
    input_file_name = sys.argv[1]
    
    # Initial Decision Heuristic to be used
    decider_to_use = sys.argv[2]
    
    # Restart Heuristic to be used
    # None if no restart strategy to be used
    restarter_to_use = sys.argv[3]

    # Open file
    with open(input_file_name, "r") as f:
        sentence, num_vars = read_cnf(f)
    
    # Create the SAT class and solve!
    sat = SAT(decider_to_use, restarter_to_use, sentence, num_vars)
    sat.cdcl_run()
    sat._stats.print_stats()