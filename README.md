# SAT Solvers Front-end
  The purpose of the project is to develop a front-end for encoding 
problems in SAT using an high level language which is converted into 
optimised CNF format to be used with available SAT solvers.
  Using antlr4 to generate a parser according to the grammar specified
in formula.g4 file, implement a listener which converts the formula to CNF
as the tree is parsed.

## The outcomes of your work should be:
### the actual tool, both executable and source code
### a report describing both the tool (algorithms, design choices) 
    and how to use it a 20 minutes presentation of your work
# Optimised CNF Converter
## Takes as input a formula in the high level language (see below)
### Generates the grounded version of the formula (by removing and
expanding the variables)
### Converts the formula into optimised (linear size) CNF
#### minimise the number of additional variables and clauses
### Output formats:
    Human readable CNF (set of clauses)
### Interfaces to a SAT solver to check the satisfiability 
    (invocation and model extraction)
#### if satisfiable it should return a model (with the original valuable names, not only the DIMACS integers)
#### (optional) possibility of searching for all the models
# High-level Language

Propositional variables can be both symbols and predicate-like terms; i.e. cell(0,4)
Standard connectives (⋀, ⋁, ¬, →, ←, ↔︎) as well as xor and if-then-else ternary operator:

ite(p,q,r)≡(p→q)∧(¬p→r)ite(p,q,r)≡(p→q)∧(¬p→r)

Variables ranging over integers or symbols bound by universal (conjunction) or existential (disjunction operators); e.g.:

∃x∈{r,g}(a∨¬t(x))≡(a∨¬t(r))∨(a∨¬t(g))∃x∈{r,g}(a∨¬t(x))≡(a∨¬t(r))∨(a∨¬t(g))

unbound variables in integer context should be considered 0 or False in propositional contexts
Integers (in ranges or arguments of predicates) can be calculated by simple expressions including the operators integer (truncated) division, modulo, multiplication, sum, difference and absolute value
variables bound to non-numbers should be considered 0 in integer expressions
The definition of the language is available as an ANTLR4 grammar (raw source). It can be used directly to generate the parser or read as an EBNF grammar to be implemented using your favorite parser (beware of the fact that, for clarity, the grammar has been designed using left recursion).
