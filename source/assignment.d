module assignment;

import cnf;
import std.container : redBlackTree, RedBlackTree;
import std.range : iota, front, array, empty;
import std.array : array;
import std.conv : to;
import std.algorithm : map, sort;
import std.string : format;
import std.math : abs;

debug import std.stdio;

public:
alias Variable = string;

struct Assignment
{
    bool[IDType] _assignment;
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
        this._assignment[abs(literal.id)] = truth;
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

    bool getTruthOfVariable(IDType id)
    {
        return this._assignment[id];
    }

    string toString() const
    {
        return this._assignment.to!string;
    }

    void fillUnassignedLiterals()
    {
        debug unassigned.writeln;
        foreach (literal; unassigned.array)
        {
            this.assign(literal);
        }
    }

    string toDIMACSFormat() const
    {
        IDType[] arr;
        foreach (key; _assignment.keys.sort)
            arr ~= (_assignment[key] ? key : -key);
        return format("v%( %d%) 0", arr);
    }
}
