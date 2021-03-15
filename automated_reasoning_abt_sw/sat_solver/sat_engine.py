import copy
from typing import *
from automated_reasoning_abt_sw.prop_logic.formula import Formula
from automated_reasoning_abt_sw.prop_logic.semantics import evaluate, is_satisfiable
from automated_reasoning_abt_sw.parser_util import parser
from automated_reasoning_abt_sw.sat_solver.bcp import Bcp, PART_A_BCP, PART_B_BCP
from collections import Counter
from automated_reasoning_abt_sw.smt_solver.smt_helper import *
from automated_reasoning_abt_sw.fol.syntax import Formula as fol_Formula

# constants
UNSAT_STATE = 0
BCP_OK = 1
ADD_CONFLICT_CLAUS = 2
SAT = 1
UNSAT = 0


def get_watch_literals_for_clause(claus):
    """
    return tuple of the clause watch literals
    @param claus:
    @return:
    """
    claus.watch_literals = claus.get_two_watch_literals()
    claus.possible_watch_literals = list(set(claus.possible_watch_literals) - set(claus.watch_literals))
    return claus.watch_literals


def add_watch_literals_for_clause(claus, watch_literal_map):
    """
    find two unassigned literals in the clause make the the watch literals. in case of only one literal, it assigend
    only one
    @param claus:
    @param watch_literal_map:
    @return:
    """
    literals_list = get_watch_literals_for_clause(claus)
    for lit in literals_list:
        if lit not in watch_literal_map.keys():
            watch_literal_map[lit] = []
        watch_literal_map[lit].append(claus)


def get_initial_assignment(f):
    """
    get initial assignment for all the clauses with only one literal
    @param f:
    @return:
    """
    satisfiable, assignment_map = check_initial_assignment(f)
    if not satisfiable:
        return (False, False)
    else:
        return (satisfiable, [(k, v) for k, v in assignment_map.items()])


def creates_watch_literals(f):
    """
    :param f:
    :return:
    """
    watch_literal_map = dict()
    for claus in f:
        if claus.number_of_literals > 1:
            add_watch_literals_for_clause(claus, watch_literal_map)
    return watch_literal_map


def check_initial_assignment(f):
    """
    function gives assignment to all clause with only one variabel and checks whether is comes to contradiction
    :param f:
    :return:
    """
    satisfiable = True
    assignment_map = dict()
    for claus in f:
        if claus.number_of_literals == 1:
            var = claus.variables[0]
            assign = claus.get_last_one()
            if var in assignment_map.keys():
                if assign != assignment_map[var]:
                    satisfiable = False
            else:
                assignment_map[var] = assign
    return satisfiable, assignment_map


def count_variables(f):
    """
    count the numbers of literals in the formula
    @param f:
    @return:
    """
    l = []
    for claus in f:
        l += claus.variables
    return len(set(l))


def get_literal_list(f):
    """
    return the literals of the formula
    @param f:
    @return: set of the literals
    """
    literal_list = []
    for claus in f:
        literal_list += claus.literals
    return literal_list


def dlis(assignmet_map, f):
    """
    implement dlis(dynamic largest individual sum) as taught in class
    @param assignmet_map:
    @param f:
    @return:
    """
    counter = Counter(get_literal_list(f))
    for key in assignmet_map.keys():
        del counter[key]
        del counter["~" + key]
    literal = max(counter, key=counter.get)
    if literal[0] == "~":
        return (literal[1:], False)
    else:
        return (literal, True)


def get_variable_list(f):
    """
    get all the variables in the ormula
    @param f:
    @return:
    """
    literal_list = []
    for claus in f:
        literal_list += claus.variables
    return set(literal_list)


def assign_true_assingment(assignmet_map, f):
    """
    assign true to unassign literal in formula
    @param assignmet_map:
    @param f:
    @return:
    """
    literals = list(get_variable_list(f) - set(assignmet_map.keys()))
    literals.sort()
    return literals[0], True


def convert_to_dic(l):
    return {k: v for k, v in l}


def part_A(f, input_formula_fol=None, substitution_map=None):
    """
    this is part A of the bcp algorithm. this is propagete assigment only. if false, unsat
    @param f:
    @param input_formula_fol:
    @param substitution_map:
    @return:
    """
    # pre-proccsing
    satsfible, assignmet_map = get_initial_assignment(f)

    if not satsfible:
        return (False, False)

    if input_formula_fol != None:
        ass_map2 = convert_to_dic(assignmet_map)
        intersected_keys = list(ass_map2.keys() & substitution_map.keys())
        model_over_formula_filtered = dict()
        for key in intersected_keys:
            model_over_formula_filtered[key] = ass_map2[key]
        model_over_formula = switch_assignment_to_fol_assignment(model_over_formula_filtered,
                                                                 substitution_map)
        if model_over_formula != {}:
            if not (congruence_closure_algorithm(model_over_formula, input_formula_fol)):
                return (False, False)

    # creating watch literal map
    watch_literal_map = creates_watch_literals(f)

    # PART A
    bcp = Bcp(watch_literal_map.copy(), input_formula_fol, substitution_map)
    state, response = bcp.bcp_step(assignmet_map,
                                   PART_A_BCP)  # (msg_type(int), content) type: 0 - unsat, 1 - assignment, 2- conflict clause
    if state == UNSAT_STATE:
        return (False, False)
    elif state == BCP_OK:
        assignmet_map = response
        return (True, (watch_literal_map, assignmet_map, bcp))


def solve_sat(input_formula, smt_flag=False):
    """
    main function of sat solver
    @param input_formula:
    @param smt_flag:
    @return:
    """
    fol_formula = None
    substitution_map = None
    if smt_flag:  # SMT solver part
        fol_formula = copy.deepcopy(input_formula)
        fol_formula = fol_Formula.parse(fol_formula)
        input_formula, substitution_map = fol_Formula.parse(input_formula).propositional_skeleton()

    #creates Tsieni
    f, original_variables, original_formula = parser.parse(str(input_formula))
    formula_original = copy.deepcopy(f)
    # number of variables in formula
    N = count_variables(f)
    state, response = part_A(f, fol_formula, substitution_map)
    if state == UNSAT_STATE:
        return UNSAT, {}
    else:
        watch_literal_map, assignmet_map, bcp = response

    # PART B
    iteration_number = 0
    while len(assignmet_map.keys()) < N:
        iteration_number += 1
        chosen_literal, chosen_assignment = dlis(assignmet_map.copy(), f)
        state, response = bcp.bcp_step([(chosen_literal, chosen_assignment)], PART_B_BCP)
        if (state == ADD_CONFLICT_CLAUS):
            # build watch literal for claus add calus to formula and go back to line 104
            if not (response is False):
                formula_original.append(response)
            f = copy.deepcopy(formula_original)
            state, response = part_A(f, fol_formula, substitution_map)
            if state == UNSAT_STATE:
                return UNSAT, {}
            else:
                watch_literal_map, assignmet_map, bcp = response
        elif (state == BCP_OK):
            assignmet_map = response

    # convert assignment to the real one
    final_assignment = dict()
    for item in original_variables:
        final_assignment[item] = assignmet_map[item]
    if not (evaluate(original_formula, final_assignment)):
        return UNSAT, {}
    return SAT, final_assignment
