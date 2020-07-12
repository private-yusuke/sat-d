module solvers.dpll;

import cnf, assignment;
import std.variant : Algebraic;
import std.typecons : Tuple;

alias Null = typeof(null);
alias SolverResult = Algebraic!(Assignment, Null);

alias unitPropagateResult = Tuple!(CNF, "F", Assignment, "assignment");

SolverResult solve(CNF F)
{
    auto res = dpll(F, Assignment(F.variableNum));
    if (res.peek!Assignment)
    {
        auto tmp = res.get!0;
        tmp.fillUnassignedLiterals();
        res = tmp;
    }
    return res;
}

ulong k;
SolverResult dpll(CNF F, Assignment assignment)
{
    k++;
    auto uPRes = unitPropagate(F, assignment);
    F = uPRes.F, assignment = uPRes.assignment;

    // if there exists an empty clause
    if (F.emptyClauses.length > 0)
        return SolverResult(null);
    // if there's no clauses left
    if (F.allClauses.length == 0)
        return SolverResult(assignment);

    Literal l = assignment.getUnassignedLiteral();

    CNF F_l = CNF(F);
    Assignment asgn1 = Assignment(assignment);
    F_l.simplify(l);
    asgn1.assign(l);

    auto res1 = dpll(F_l, asgn1);
    if (res1.peek!Assignment)
        return SolverResult(res1);

    CNF F_lnotl = CNF(F);
    Assignment asgn2 = Assignment(assignment);
    F_lnotl.simplify(l.negate);
    asgn2.assign(l);

    return dpll(F_lnotl, asgn2);
}

unitPropagateResult unitPropagate(CNF F, Assignment assignment)
{
    while (F.emptyClauses.length == 0 && F.unitClauses.length > 0)
    {
        auto k = F.unitClauses.keys[0], v = F.unitClauses[k];
        Literal x = v.unitLiteral;

        F.simplify(x);
        assignment.assign(x);
    }
    return unitPropagateResult(F, assignment);
}
