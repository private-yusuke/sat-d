module cnf;
import std.container : redBlackTree, RedBlackTree;
import std.array : array;
import std.algorithm : count;
import std.string : format;
import std.range : empty;
import dimacs;

debug import std.stdio;

public:

alias IDType = long;

struct Literal
{
    string variable;
    bool isNegated;
    IDType id;

    // "a < b"
    long opCmp(ref const Literal rhs) const
    {
        return this.id - rhs.id;
    }

    Literal negate()
    {
        this.isNegated = !this.isNegated;
        this.id = -id;
        return this;
    }

    string toString() const
    {
        if (this.isNegated)
            return format("¬%s", this.variable);
        else
            return this.variable;
    }
}

struct Clause
{
    RedBlackTree!Literal literals;
    IDType id;

    this(Literal[] literals, IDType id)
    {
        this.id = id;
        this.literals = redBlackTree(literals);
    }

    bool isEmpty()
    {
        return literals.array.empty;
    }

    bool isUnit()
    {
        return literals.array.count == 1;
    }

    Literal unitLiteral()
    {
        return literals.array[0];
    }

    void removeLiteral(Literal literal)
    {
        literals.removeKey(literal);
    }

    string toString() const
    {
        return format("%(%s∧%)", literals.array);
    }
}

struct CNF
{
    size_t variableNum, clauseNum;

    Clause[IDType] allClauses;

    Clause[IDType] normalClauses; // other than "unit" or "empty" clause
    Clause[IDType] unitClauses;
    Clause[IDType] emptyClauses;

    Literal[][IDType] literalsInClause;
    IDType[][IDType] clausesContainingLiteral;

    this(Clause[] clauses, Preamble preamble)
    {
        this.variableNum = preamble.variables;
        this.clauseNum = preamble.clauses;

        foreach (clause; clauses)
        {
            IDType cid = clause.id;
            allClauses[cid] = clause;

            if (clause.isEmpty)
                emptyClauses[cid] = clause;
            else if (clause.isUnit)
                unitClauses[cid] = clause;
            else
                normalClauses[cid] = clause;

            foreach (literal; clause.literals.array)
            {
                literalsInClause[cid] ~= literal;
                clausesContainingLiteral[literal.id] ~= clause.id;
            }
        }
    }

    void removeLiterals(Literal literal)
    {
        if (literal.id !in clausesContainingLiteral)
            return;
        foreach (id; clausesContainingLiteral[literal.id])
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
                if (clause.isUnit)
                {
                    normalClauses.remove(id);
                    unitClauses[id] = clause;
                }
            }
        }
        clausesContainingLiteral.remove(literal.id);
    }

    void removeClauseById(IDType clauseId)
    {
        bool res = normalClauses.remove(clauseId)
            || unitClauses.remove(clauseId) || emptyClauses.remove(clauseId);
        if (res)
            allClauses.remove(clauseId);
    }

    void removeClauseContainingLiteral(Literal literal)
    {
        if (literal.id !in clausesContainingLiteral)
            return;
        foreach (id; clausesContainingLiteral[literal.id])
            removeClauseById(id);
    }

    void simplify(Literal literal)
    {
        this.removeClauseContainingLiteral(literal);
        this.removeLiterals(literal.negate());
    }

    string toString() const
    {
        if (allClauses.length == 0)
            return "<empty>";
        return format("%((%s)∨%))", allClauses.values);
    }

    debug string debugString() const
    {
        return format("%(%s\n%)", [
                allClauses, normalClauses, unitClauses, emptyClauses
                ]);
    }
}
