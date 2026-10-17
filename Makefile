default: all

all: 
	agda Everything.agda

time:
	time agda Everything.agda

examples:
	agda TypeInference/Examples.agda

# The example sets by the parts of the solver they exercise, for
# checking a change under TypeInference/SolverImpl/ before a full
# `make examples`:
#   generation, subtyping, the report (Generate, Solve, SolverImpl)
#                                                        -> stdlib
#   annotations                                          -> annotations
#   clause-local unknowns, handlers (Localise)           -> handlers
#   unbox, the var rule, closed orderings (Entail)       -> boxes
#   pruning, canonical forms, elimination
#     (Simplify, Canon, Eliminate)                       -> reports (+ stdlib)
#   product grades, normal forms (Product, Normal, Entail) -> product
#   durations other than ticks, dense time (Entail)      -> durations
#   single stages on hand-written input: splitting,
#     disjunction pruning, absorption by the top, multiset
#     comparison of products, chained closed orderings, cycle
#     collapse, the value of lowering at each shape of cycle
#     (Canon, Simplify, Entail, Localise, Values)        -> stages
#   the search for a refutation and establishment: retry,
#     the closed check with failing chains, candidates
#     (Search, Entail, Localise, Solve)                  -> runs
#   natural numbers, sums and lists: zero, succ, caseℕ,
#     numerals, inl, inr, case+, nil, cons and caseL, the
#     former table at Nat, at sums and at lists, eternality
#     under locks
#     (Generate, Former, Expand, Entail)                 -> data
#   primitive recursion: recℕ and recL, the cycle
#     ε · ε ≾ ε, the step's lock at the top, the head
#     behind the lock at the effect, recursion in a clause
#     (Generate, Localise, Search)                       -> recursion

examples-stdlib:
	agda TypeInference/Examples/Stdlib/All.agda

examples-annotations:
	agda TypeInference/Examples/Annotations/All.agda

examples-handlers:
	agda TypeInference/Examples/Handlers/All.agda

examples-boxes:
	agda TypeInference/Examples/Boxes/All.agda

examples-reports:
	agda TypeInference/Examples/Reports/All.agda

examples-product:
	agda TypeInference/Examples/Product/All.agda

examples-stages:
	agda TypeInference/Examples/Stages/All.agda

examples-durations:
	agda TypeInference/Examples/Durations/All.agda

examples-runs:
	agda TypeInference/Examples/Runs/All.agda

examples-data:
	agda TypeInference/Examples/Data/All.agda

examples-recursion:
	agda TypeInference/Examples/Recursion/All.agda

clean:
	git clean -fx
