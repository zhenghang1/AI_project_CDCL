from SAT_sr import SAT
import argparse
from utils import Test
import time

parser = argparse.ArgumentParser()
parser.add_argument('-i','--input_file', default='examples/and1.cnf', type=str, help='path to input cnf file')
parser.add_argument('-d','--decider',default='VSIDS',type=str,help='type of decider, should be one of ["VSIDS","LRB","CHB"]')
parser.add_argument('-r','--restarter',default='LUBY',type=str,help='type of restarter, should be one of ["GEOMETRIC","LUBY","NO_RESTART"]')
parser.add_argument('-b','--bve',default='False',type=str,help='Boolean flag indicating whether do bve or not, should be one of [""True","False"]')
parser.add_argument('-t','--test',default='True',type=bool,help='Boolean flag indicating whether taking a test or not, should be one of [""True","False"]')

args = parser.parse_args()

if __name__ == "__main__":
    # File name of the file containing the input problem
    input_file_name = args.input_file
    
    # Initial Decision Heuristic to be used
    decider_to_use = args.decider
    
    # Restart Heuristic to be used
    # None if no restart strategy to be used
    restarter_to_use = args.restarter

    bve_flag = args.bve

    # Create the SAT class and solve!
    # sat = SAT(decider_to_use, restarter_to_use, bve_flag)
    sat = SAT(decider_to_use, restarter_to_use, bve_flag)
    sat.solve(input_file_name)

    if args.test:
        start = time.time()
        print('\n')
        print("============================= TEST ===================================")
        if sat.stats._result == "SAT":
            t = Test(sat.orig_sentence.values(), sat.assignment_dict,sat._num_vars)
            t.test_correctness()
            t.test_rep_assign()
            pass
        else:
            print("The result is UNSAT and No test could be done!")
        end = time.time()
        print("Testing time:",end-start)
        print("============================= TEST ===================================",'\n')

    sat.stats.print_stats()