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

    void clear()
    {
        _assignment.clear();
    }

    void assign(Literal literal, bool truth)
    {
        _assignment[literal.variable] = truth;
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
        return _assignment[variable];
    }

    string toString() const
    {
        return _assignment.to!string;
    }
}
