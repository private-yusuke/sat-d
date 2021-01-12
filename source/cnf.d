module cnf;
import std.container : redBlackTree, RedBlackTree;
import std.array : array;
import std.algorithm : count, sort;
import std.string : format;
import std.range : empty, zip;
import std.math : abs;
import dimacs;

debug import std.stdio;

alias Set(T) = RedBlackTree!T;

public:

/++
+ 0 は \overline \Lambda (conflict node) を表す。
+ \cdots, -3, -2, -1, 1, 2, 3, \cdots を通常のリテラルのために利用する。
+ x > 0 であるとき、
+ 正の整数 x は、x を意味する。
+ 負の整数 -x は、\lnot x を意味する。
+/
alias Literal = long;

/// 与えられた Literal を否定したものを返す。
Literal negate(Literal lit)
{
    return -lit;
}

/// 節
struct Clause
{
    alias ID = size_t;

    /// 節を区別するための ID
    ID id;
    /// 節に含まれる Literal の集合
    Set!Literal literals;

    this(ID id, Set!Literal literals)
    {
        this.id = id;
        this.literals = literals;
    }

    this(ID id, Literal[] literals)
    {
        this(id, redBlackTree!Literal(literals));
    }

    this(Clause clause)
    {
        this.id = clause.id;
        this.literals = clause.literals.dup;
    }

    bool isEmptyClause()
    {
        return literals.length == 0;
    }

    bool isUnitClause()
    {
        return literals.length == 1;
    }

    Literal unitLiteral()
    {
        assert(this.isUnitClause());
        return literals.front;
    }

    bool containsLiteral(Literal lit)
    {
        return lit in literals;
    }

    auto removeLiteral(Literal lit)
    {
        return literals.removeKey(lit);
    }

    int opCmp(R)(const R other) const
    {
        return this.id < other.id;
    }

    bool opBinaryRight(string op)(Literal lit) const if (op == "in")
    {
        return lit in literals;
    }

    string toString()
    {
        if (literals.length == 0)
            return "(empty)";
        else
            return format("(%(%d ∨ %))", literals.array.sort!((a, b) => a.abs < b.abs));
    }
}

struct CNF
{
    size_t variableNum, clauseNum;

    Clause[Clause.ID] allClauses;

    Clause[Clause.ID] normalClauses; // other than "unit" or "empty" clause
    Clause[Clause.ID] unitClauses;
    Clause[Clause.ID] emptyClauses;

    Literal[][Clause.ID] literalsInClause;
    Clause.ID[][Literal] clausesContainingLiteral;

    this(Clause[] clauses, Preamble preamble)
    {
        this.variableNum = preamble.variables;
        this.clauseNum = preamble.clauses;

        foreach (clause; clauses)
        {
            Clause.ID cid = clause.id;
            allClauses[cid] = clause;

            if (clause.isEmptyClause())
                emptyClauses[cid] = clause;
            else if (clause.isUnitClause())
                unitClauses[cid] = clause;
            else
                normalClauses[cid] = clause;

            foreach (literal; clause.literals.array)
            {
                literalsInClause[cid] ~= literal;
                clausesContainingLiteral[literal] ~= clause.id;
                debug stderr.writeln(clause.id);
            }
        }
    }

    // for deep copy
    this(CNF rhs)
    {
        this.variableNum = rhs.variableNum;
        this.clauseNum = rhs.clauseNum;

        foreach (key, value; rhs.allClauses)
        {
            this.allClauses[key] = Clause(value);
        }
        foreach (key, value; rhs.normalClauses)
        {
            this.normalClauses[key] = Clause(value);
        }
        foreach (key, value; rhs.unitClauses)
        {
            this.unitClauses[key] = Clause(value);
        }
        foreach (key, value; rhs.emptyClauses)
        {
            this.emptyClauses[key] = Clause(value);
        }
        this.literalsInClause = rhs.literalsInClause.dup;
        this.clausesContainingLiteral = rhs.clausesContainingLiteral.dup;
    }

    void removeLiterals(Literal literal)
    {
        if (literal !in clausesContainingLiteral)
            return;
        foreach (id; clausesContainingLiteral[literal])
        {
            if (id in unitClauses)
            {
                Clause clause = unitClauses[id];
                unitClauses.remove(id);
                clause.removeLiteral(literal);
                this.emptyClauses[id] = clause;
            }
            else if (id in normalClauses)
            {
                Clause clause = normalClauses[id];
                clause.removeLiteral(literal);
                if (clause.isUnitClause())
                {
                    normalClauses.remove(id);
                    unitClauses[id] = clause;
                }
            }
        }
    }

    void removeClauseById(Clause.ID clauseId)
    {
        normalClauses.remove(clauseId);
        unitClauses.remove(clauseId);
        emptyClauses.remove(clauseId);
        allClauses.remove(clauseId);
    }

    void removeClauseContainingLiteral(Literal literal)
    {
        foreach (id; clausesContainingLiteral[literal])
            removeClauseById(id);
        clausesContainingLiteral.remove(literal);
    }

    void simplify(Literal literal)
    {
        this.removeClauseContainingLiteral(literal);
        this.removeLiterals(-literal);
    }

    string toString() const
    {
        if (allClauses.length == 0)
            return "<none>";
        const(Clause)[] tmp;
        foreach (key; allClauses.keys.sort)
        {
            tmp ~= allClauses[key];
        }
        return format("%((%s)∧%))", tmp);
    }

    debug string debugString() const
    {
        return format("all: %s\nnormal:%s\nunit:%s\nempty:%s\nclcon:%s", allClauses,
                normalClauses, unitClauses, emptyClauses, clausesContainingLiteral);
    }
}
