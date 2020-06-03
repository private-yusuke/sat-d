module cnf;
import std.container : redBlackTree, RedBlackTree;
import std.array : array;
import std.algorithm : count, sort;
import std.string : format;
import std.range : empty, zip;
import std.math : abs;
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

    Literal positive()
    {
        this.isNegated = false;
        this.id = abs(this.id);
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

    this(Clause rhs)
    {
        this.literals = rhs.literals.dup;
        this.id = id;
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
        if (literals.array.empty)
            return "<empty>";
        return format("%(%s∨%)", literals.array);
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

    // for deep copy...
    // TODO: Is there simpler implementation than this?
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
    }

    void removeClauseById(IDType clauseId)
    {
        normalClauses.remove(clauseId);
        unitClauses.remove(clauseId);
        emptyClauses.remove(clauseId);
        allClauses.remove(clauseId);
    }

    void removeClauseContainingLiteral(Literal literal)
    {
        foreach (id; clausesContainingLiteral[literal.id])
            removeClauseById(id);
        clausesContainingLiteral.remove(literal.id);
    }

    void simplify(Literal literal)
    {
        this.removeClauseContainingLiteral(literal);
        this.removeLiterals(literal.negate());
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
