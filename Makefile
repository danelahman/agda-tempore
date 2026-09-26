default: all

all: 
	agda Everything.agda

time:
	time agda Everything.agda

examples:
	agda TypeInference/Examples.agda

# Which example set exercises which part of the solver, so a change
# under TypeInference/SolverImpl/ can be checked against the sets that
# cover it before a full `make examples`:
#   generation, subtyping, the report itself (Generate, Solve, Report)
#     -> stdlib
#   annotations                                        -> annotations
#   clause-local unknowns, handlers (Localise)          -> handlers
#   unbox, the var rule, closed orderings (Closed)      -> boxes
#   pruning, canonical form, elimination
#     (Simplify, Canon, Eliminate)                      -> reports (+ stdlib)
#   product grades, the normal form (Product, Normal)   -> product
#   single stages on hand-written input: splitting,
#     disjunction pruning, the top's absorption, multiset
#     products, chained closed orderings, cycle collapse
#     (Canon, Simplify, Normal, Closed, Localise, Solve) -> stages

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

clean:
	git clean -fx
