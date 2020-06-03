module assignment;

import cnf;
import std.container : redBlackTree, RedBlackTree;
import std.range : iota, front, array, empty;
import std.array : array;
import std.conv : to;
import std.algorithm : map;
import std.string : format;

debug import std.stdio;

public:

alias Variable = string;

struct Assignment
{
    bool[Variable] _assignment;
    RedBlackTree!Literal unassigned;

    this(IDType variableNum)
    {
        this.unassigned = redBlackTree!Literal(iota(1, variableNum + 1)
                .map!(v => Literal(format("x_%d", v), false, v)).array);

    }

    this(Assignment rhs)
    {
        _assignment = rhs._assignment.dup;
        unassigned = rhs.unassigned.dup;
    }

    void clear()
    {
        _assignment.clear();
    }

    void assign(Literal literal)
    {
        bool truth = !literal.isNegated;
        this._assignment[literal.variable] = truth;
        if (literal.positive() !in unassigned)
        {
            debug writefln("not found: %s", literal);
        }
        unassigned.removeKey(literal);
    }

    bool hasUnassignedLiteral()
    {
        return !this.unassigned.array.empty;
    }

    Literal getUnassignedLiteral()
    {
        return this.unassigned.array.front;
    }

    bool getTruthOfVariable(Variable variable)
    {
        return this._assignment[variable];
    }

    string toString() const
    {
        return this._assignment.to!string;
    }
}
