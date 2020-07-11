module solvers.cdcl;

import cnf, assignment;
import std.variant : Algebraic;
import std.typecons : Tuple;

debug import std.stdio;

alias Null = typeof(null);
alias SolverResult = Algebraic!(Assignment, Null);

// alias unitPropagateResult = Tuple!(CNF, "F", Assignment, "assignment");

class Solver
{
    Variable newVariable()
    {

    }

    bool addClause(Clause clause)
    {

    }

    bool simplifyDB()
    {

    }

    bool solve(Assignment assumptions)
    {

    }

    Assignment model()
    {

    }
}
