default: all

all: 
	agda Everything.agda

time:
	time agda Everything.agda

examples:
	agda OpenCalculus/Examples.agda
	agda Bridge/Examples/Uniform/All.agda

# The example sets by the parts of the solver they exercise, for
# checking a change under OpenCalculus/Inference/SolverImpl/ before a full
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
#   comparisons: cmp at eternal types, refused at
#     functions and boxes, eternality asked of an unknown
#     (Generate, Solve)                                  -> compare
#   completeness on a uniform handler typing
#     (Localise, Bridge/Instantiation/)                  -> uniform

examples-stdlib:
	agda OpenCalculus/Examples/Stdlib/All.agda

examples-annotations:
	agda OpenCalculus/Examples/Annotations/All.agda

examples-handlers:
	agda OpenCalculus/Examples/Handlers/All.agda

examples-boxes:
	agda OpenCalculus/Examples/Boxes/All.agda

examples-reports:
	agda OpenCalculus/Examples/Reports/All.agda

examples-product:
	agda OpenCalculus/Examples/Product/All.agda

examples-stages:
	agda OpenCalculus/Examples/Stages/All.agda

examples-durations:
	agda OpenCalculus/Examples/Durations/All.agda

examples-runs:
	agda OpenCalculus/Examples/Runs/All.agda

examples-data:
	agda OpenCalculus/Examples/Data/All.agda

examples-recursion:
	agda OpenCalculus/Examples/Recursion/All.agda

examples-compare:
	agda OpenCalculus/Examples/Compare/All.agda

examples-uniform:
	agda Bridge/Examples/Uniform/All.agda

clean:
	git clean -fx
