module solvers.dpll;

import cnf, assignment;
import std.variant : Algebraic;
import std.typecons : Tuple;

debug import std.stdio;

alias Null = typeof(null);
alias SolverResult = Algebraic!(Assignment, Null);

alias unitPropagateResult = Tuple!(CNF, "F", Assignment, "assignment");

SolverResult solve(CNF F)
{
    return dpll(F, Assignment(F.variableNum));
}

SolverResult dpll(CNF F, Assignment assignment)
{
    debug F.debugString.writeln;
    debug writefln("CNF: %s, asgn: %s", F, assignment);

    auto uPRes = unitPropagate(F, assignment);
    F = uPRes.F, assignment = uPRes.assignment;

    debug writefln("p: CNF: %s, asgn: %s", F, assignment);

    // if there exists an empty clause
    if (F.emptyClauses.length > 0)
        return SolverResult(null);
    // if there's no clauses left
    if (F.allClauses.length == 0)
        return SolverResult(assignment);

    if (!assignment.hasUnassignedLiteral)
        return SolverResult(null);
    Literal l = assignment.getUnassignedLiteral();

    CNF F_l = F;
    Assignment asgn1 = assignment;
    F_l.simplify(l);
    asgn1.assign(l, true);
    auto res1 = dpll(F_l, asgn1);
    if (res1.peek!Assignment)
        return SolverResult(res1);

    CNF F_lnotl = F;
    Assignment asgn2 = assignment;
    F_lnotl.simplify(l.negate);
    asgn2.assign(l, false);
    return dpll(F_lnotl, asgn2);
}

unitPropagateResult unitPropagate(CNF F, Assignment assignment)
{
    while (F.emptyClauses.length == 0 && F.unitClauses.length > 0)
    {
        auto k = F.unitClauses.keys[0], v = F.unitClauses[k];
        Literal x = v.unitLiteral;

        F.simplify(x);
        assignment.assign(x, true);

    }

    return unitPropagateResult(F, assignment);
}
