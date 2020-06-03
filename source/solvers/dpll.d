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

ulong k;
SolverResult dpll(CNF F, Assignment assignment)
{
    k++;
    debug "===== %d".writefln(k);
    debug F.writeln;
    debug assignment.writeln;
    auto uPRes = unitPropagate(F, assignment);
    F = uPRes.F, assignment = uPRes.assignment;
    debug F.writeln;
    debug assignment.writeln;

    // if there exists an empty clause
    if (F.emptyClauses.length > 0)
        return SolverResult(null);
    // if there's no clauses left
    if (F.allClauses.length == 0)
        return SolverResult(assignment);

    if (!assignment.hasUnassignedLiteral)
        return SolverResult(null);
    Literal l = assignment.getUnassignedLiteral();

    CNF F_l = CNF(F);
    Assignment asgn1 = Assignment(assignment);
    F_l.simplify(l);
    asgn1.assign(l);

    auto res1 = dpll(F_l, asgn1);
    if (res1.peek!Assignment)
        return SolverResult(res1);

    debug "************test".writeln;
    debug F.writeln;
    CNF F_lnotl = CNF(F);
    Assignment asgn2 = Assignment(assignment);
    F_lnotl.simplify(l.negate);
    asgn2.assign(l);

    return dpll(F_lnotl, asgn2);
}

unitPropagateResult unitPropagate(CNF F, Assignment assignment)
{
    debug F.debugString.writeln;
    while (F.emptyClauses.length == 0 && F.unitClauses.length > 0)
    {
        auto k = F.unitClauses.keys[0], v = F.unitClauses[k];
        Literal x = v.unitLiteral;

        F.simplify(x);
        assignment.assign(x);
        debug "up".writeln;
        debug F.writeln;
        debug F.debugString.writeln;
        debug writeln;

    }

    return unitPropagateResult(F, assignment);
}
