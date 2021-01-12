module tseytin;
import pegged.grammar;
import pegged.tohtml;
import dimacs;
import cnf;
import std.stdio;
import std.string : strip;
import std.container : redBlackTree;
import std.array : array;
import std.range : enumerate;
import std.typecons : Tuple;

mixin(grammar(`
Expression:
    Expr < Imp (OrOperator Imp)*
    Imp < Conj (ImpOperator Conj / EquivOperator Conj)*
    Conj < Unary (ConjOperator Unary)*
    Unary < (UnaryOperator)? Primary
    Primary < "(" Expr ")" / Ident

    OrOperator < "or" / "∨" / "v" / "\\/"
    ImpOperator < "implies" / "then" / "→" / "⇒" / "->" / "=>"
    EquivOperator < "equiv" / "⇔" / "↔" / "<=>"

    ConjOperator < "and" / "∧" / "^" / "/\\"
    UnaryOperator < "not" / "-" / "￢" / "!"
    Keyword < OrOperator / ImpOperator / EquivOperator / ConjOperator / UnaryOperator / "__VAR" ~[0-9]+
    Ident <- !Keyword ~[0-9A-Za-z_]+
`));

debug
{
    import solvers.cdcl;

    enum bool[string] answers = [
            "not (a or not (b and c))" : true,
            "not (a -> (b and c)) -> (b or not d equiv a)" : true,
            "a and not a" : false, "not (a and not a)" : true
        ];
    bool isSAT(string formula)
    {
        CDCLSolver solver = new CDCLSolver();
        solver.initialize(tseytinTransform(formula).parseResult);
        return solver.solve().peek!(Literal[]) !is null;
    }

    unittest
    {
        assert(isSAT(""));
        assert(isSAT(" "));
        assert(isSAT("a"));
        assert(isSAT("A or B and A or not B or not A or not B"));
        assert(isSAT("A or B and not A or B and A or not B and not A or not B"));
        assert(isSAT("a or not a"));
        assert(!isSAT("a and not a"));
        assert(!isSAT("A /\\ !A"));

        // check whether all the symbols can be interpreted correctly...
        assert(isSAT("A or A ∨ A v A \\/ A implies B then B → B ⇒ B -> B equiv C ⇔ C ↔ C <=> D and D ∧ D ^ D /\\ D or not E or -D or ￢ D or ! D"));
        import std.exception : collectException;

        // check that exceptions should be thrown if the input is invalid
        assert(collectException(isSAT("a or v")));
        assert(collectException(isSAT("not")));
        assert(isSAT("A -> A"));
        assert(isSAT("A implies A"));
        assert(isSAT("not (a or not (b and c))"));
        assert(isSAT("not (a -> (b and c)) -> (b or not d equiv a)"));
    }
}

enum ExprType
{
    NOT,
    OR,
    AND,
    IMP,
    EQUIV,
}

struct Expr
{
    string left;
    ExprType type;
    string right;
}

ExprType toExprType(string name)
{
    with (ExprType)
    {
        enum ExprType[string] exprMap = [
                "Expression.OrOperator" : OR, "Expression.ImpOperator" : IMP,
                "Expression.EquivOperator" : EQUIV,
                "Expression.ConjOperator" : AND, "Expression.UnaryOperator" : NOT
            ];
        return exprMap[name];
    }
}

alias tseytinTransformResult = Tuple!(parseResult, "parseResult", Literal[string], "varToLiteral");

tseytinTransformResult tseytinTransform(string input)
{
    input = input.strip;
    // if the input is just blanks
    if (input == "")
        return tseytinTransformResult(parseResult([], Preamble(0, 0)), null);

    auto inputExpr = Expression(input);
    if (inputExpr.end != input.length)
        error("invalid input");

    Expr[] expressions;
    Set!string originalVars = redBlackTree!string;
    string getPreviousVariable()
    {
        assert(expressions.length != 0);
        return format("__VAR%d", expressions.length - 1);
    }

    PT visit(PT)(PT p)
    {
        switch (p.name)
        {
        case "Expression":
            return visit(p.children[0]);
        case "Expression.Expr", "Expression.Imp",
                "Expression.Conj":
                if (p.children.length == 1) return visit(p.children[0]);
            Expr lastExpr = Expr(visit(p.children[0]).input,
                    p.children[1].name.toExprType, visit(p.children[2]).input);
            expressions ~= lastExpr;

            ulong k = 3;
            while (k < p.children.length)
            {
                ExprType type = p.children[k].name.toExprType;
                lastExpr = Expr(getPreviousVariable(), type, visit(p.children[k + 1]).input);
                expressions ~= lastExpr;
                k += 2;
            }
            p.input = getPreviousVariable();
            return p;

        case "Expression.Unary":
            if (p.children.length == 1)
                return visit(p.children[0]);

            auto res = visit(p.children[1]);
            expressions ~= Expr(res.input, ExprType.NOT);
            res.input = getPreviousVariable();
            return res;

        case "Expression.Primary":
            if (p.children.length == 1)
                return visit(p.children[0]);
            else
                return visit(p.children[1]);

        case "Expression.Ident":
            p.input = p.input[p.begin .. p.end].strip;
            originalVars.insert(p.input);
            return p;

        default:
            error("invalid formula");
            assert(0);
        }

    }

    visit(inputExpr);

    // if the input is like "a", there's only one variable left and no operations included
    if (expressions.length == 0)
        return tseytinTransformResult(parseResult([Clause(1, [1])], Preamble(1, 1)), [
input: 1
                ]);

    auto vars = redBlackTree!string;
    foreach (ind, expr; expressions)
    {
        vars.insert(expr.left);
        vars.insert(expr.right);
        vars.insert(format("__VAR%d", ind));
    }
    vars.removeKey("");
    long[string] m;
    foreach (i, v; vars.array.enumerate)
        m[v] = i + 1;
    m[""] = 0;

    size_t clauseVarNum = 1;
    Clause newClause(T...)(T literals)
    {
        return Clause(clauseVarNum++, [literals]);
    }

    Clause[] clauses;

    Clause[] exprToClauses(size_t ind, Expr expr)
    {
        auto tseytinLit = m[format("__VAR%d", ind)];
        auto left = m[expr.left], right = m[expr.right];
        with (ExprType) switch (expr.type)
        {
        case NOT:
            return [
                newClause(tseytinLit, left), newClause(-tseytinLit, -left)
            ];
        case OR:
            return [
                newClause(tseytinLit, -left), newClause(tseytinLit, -right),
                newClause(-tseytinLit, left, right)
            ];
        case AND:
            return [
                newClause(-tseytinLit, left), newClause(-tseytinLit, right),
                newClause(tseytinLit, -left, -right)
            ];
        case IMP:
            return [
                newClause(tseytinLit, left), newClause(tseytinLit, -right),
                newClause(-tseytinLit, -left, right)
            ];
        case EQUIV:
            return [
                newClause(tseytinLit, left), newClause(tseytinLit, -right),
                newClause(-tseytinLit, -left, right), newClause(tseytinLit,
                        right), newClause(tseytinLit, -left),
                newClause(-tseytinLit, -right, left)
            ];
        default:
            assert(0);
        }
    }

    foreach (ind, expr; expressions)
    {
        clauses ~= exprToClauses(ind, expr);
    }
    clauses ~= newClause(m[format("__VAR%d", expressions.length - 1)]);

    Literal[string] varToLiteral;
    foreach (var; originalVars)
    {
        varToLiteral[var] = m[var];
    }

    return tseytinTransformResult(parseResult(clauses, Preamble(vars.length,
            clauseVarNum - 1)), varToLiteral);
}

private:
import std.string : format;

void error(A...)(string msg, A args)
{
    class ExpressionReadException : Exception
    {
        this(string msg)
        {
            super(msg);
        }
    }

    throw new ExpressionReadException(format(msg, args));
}
