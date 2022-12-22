from SAT_new import SAT
from utils import read_cnf
import argparse
import sys

def test(sentence, _assignment):
    """test the correctness of the result"""
    assignment = [a[0] for a in _assignment]
    FLAG = True
    for clause in sentence:
        flag = False
        for lit in clause:
            if lit in assignment:
                flag = True
                break
        FLAG = FLAG & flag
        if FLAG == False:
            break
    if FLAG:
        print("Yeh! The result is correct.")
    else:
        print("Nop! The result is wrong.")

def test_rep_assign(_assignment):
    """test whether a variable has been assigned twice"""
    """output the number of 0's in `assignment`. 
       If that doesn't equal to 'num_var - len(var)', where `var` is the number of actual number of variables, then the result is definitely wrong"""
    assignment = [a[0] for a in _assignment]
    v_count = {}
    for a in assignment:
        v_count[abs(a)] = v_count.get(abs(a), 0) + 1
    for v, count in v_count.items():
        if (count > 1) and (v != 0):
            print("Variable X_" + str(v) + " has been assigned " + str(count) + " times!")
    if v_count.get(0, 0) > 0:
        print("Totally " + str(v_count[0]) + " 0's has been 'assigned'.")

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

    if sat._assignment is None:
        print("No solution found")
    else:
        print(f"Successfully found a solution: {sat._assignment}")
        print(f"decided_idxs: {sat._decided_idxs}")
        test(sentence, sat._assignment)
        test_rep_assign(sat._assignment)
    sat._stats.print_stats()