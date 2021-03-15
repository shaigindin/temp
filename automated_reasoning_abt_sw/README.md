![67532 AUTOMATED REASONING ABOUT SOFTWARE](https://github.com/norbit8/automated_reasoning_abt_sw/blob/main/logo.png?raw=true)

<!-- ALL-CONTRIBUTORS-BADGE:START - Do not remove or modify this section -->
![python versions](https://img.shields.io/pypi/pyversions/firebase?style=flat-square)
<space>
[![All Contributors](https://img.shields.io/badge/all_contributors-2-orange.svg?style=flat-square)](#contributors-)
<!-- ALL-CONTRIBUTORS-BADGE:END -->

## SAT Solver :robot:
In order to use the SAT solver, you'll need to import `sat_solver.sat_engine` and then call the function `solve_sat(formula)` where 
a formula is defined like so
- An atomic proposition should be a letter in 'p' ... 'z', optionally followed by a sequence of digits. Examples: 'p', 'y12', 'z035'.

- Could have 'T' and 'F' (as True and False respectively).

- ~φ where φ is a valid propositional formula.

- '(φ&ψ)' where each of φ and ψ is a valid propositional formula.

- '(φ|ψ)' where each of φ and ψ is a valid propositional formula.

- '(φ->ψ)' where each of φ and ψ is a valid propositional formula.

#### Example:
  ```
  from sat_solver.sat_engine import *
  formula = '(~p0|~pq<->(p2<->(p3->p4))))'
  print(solve_sat(formula))
  ```
## SMT Solver :ghost:
First you'll need to import `smt_solver.smt_engine`.
Now, using the SMT solver is almost identical to the SAT solver,
but because its FOL (First order logic) we have introduced functions and the equal sign.

A valid formula is of the form:

- A formula as described in the SAT Solver section (above).
- f(a,b)=c where a, b and c are variables. (Also, the function can have any arity that you'd like)

### Example:
  ```
  from smt_solver.smt_engine import *
  formula_fol = '~((f(a,c)=b&~f(a,g(b))=b)&c=g(b))'
  print(smt_solver(formula_fol))
  ```

## LP Solver :alien:
In order to use the LP solver, you'll need to import `lp_solver.lp_engine.py`.
Then, you'll need to provide the engine with an Linear programming problem in a form of matricies, and vectors.
Specifically we're accepting linear program in the form of: 
  
  ```
  Maximize Cx
  s.t. Ax <= b
  and x >= 0
  ```
### Example
  ```
    from lp_solver.lp_engine.py import *
    A = np.array([[3, 2, 1, 2], [1, 1, 1, 1], [4, 3, 3, 4]])
    b = np.array([225, 117, 420])
    c = np.array([19, 13, 12, 17])
    res, val = lp_solver(A, b, c, BLAND_RULE)
    if res == UNBOUNDED:
        print("UNBOUNDED")
    elif res == SUCCESS:
        print(f"SUCCESS\nMaximal value is: {val}")
    else:
        print("NO SOLUTION")
  ```
## Tests :heart:
We are providing tests for each of the above solvers, located at

- SAT SOLVER TESTS: `/lp_solver/tests/`

  The tests run for `number_of_iterations = 1000` by default but you can change the parameter there, just run the file and you're set. 
- SMT SOLVER TESTS: `/smt_solver/tests/`

  The tests taken from examples we saw in class, and more self made ones. just run the file and you're set.
- LP SOLVER TESTS: `/lp_solver/tests/`

  The tests taken from examples we saw in class, and more self made ones. just run the file and you're set.


## Contributors ✨

Thanks goes to these wonderful people ([emoji key](https://allcontributors.org/docs/en/emoji-key)):

<!-- ALL-CONTRIBUTORS-LIST:START - Do not remove or modify this section -->
<!-- prettier-ignore-start -->
<!-- markdownlint-disable -->
<table>
  <tr>
    <td align="center"><a href="https://github.com/shaigindin"><img src="https://avatars.githubusercontent.com/u/49125116?v=4?s=100" width="100px;" alt=""/><br /><sub><b>shaigindin</b></sub></a><br /><a href="#infra-shaigindin" title="Infrastructure (Hosting, Build-Tools, etc)">🚇</a> <a href="https://github.com/norbit8/automated_reasoning_abt_sw/commits?author=shaigindin" title="Tests">⚠️</a> <a href="https://github.com/norbit8/automated_reasoning_abt_sw/commits?author=shaigindin" title="Code">💻</a></td>
    <td align="center"><a href="https://github.com/norbit8"><img src="https://avatars.githubusercontent.com/u/18491183?v=4?s=100" width="100px;" alt=""/><br /><sub><b>Yoav</b></sub></a><br /><a href="#infra-norbit8" title="Infrastructure (Hosting, Build-Tools, etc)">🚇</a> <a href="https://github.com/norbit8/automated_reasoning_abt_sw/commits?author=norbit8" title="Tests">⚠️</a> <a href="https://github.com/norbit8/automated_reasoning_abt_sw/commits?author=norbit8" title="Code">💻</a></td>
  </tr>
</table>

<!-- markdownlint-restore -->
<!-- prettier-ignore-end -->

<!-- ALL-CONTRIBUTORS-LIST:END -->

This project follows the [all-contributors](https://github.com/all-contributors/all-contributors) specification. Contributions of any kind welcome!
