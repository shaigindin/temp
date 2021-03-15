from sat_solver.sat_engine import solve_sat


def smt_solver(original_formula: str):
    return solve_sat(original_formula, smt_flag=True)


