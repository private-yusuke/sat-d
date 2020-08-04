module assignment;

import cnf;
import std.container : redBlackTree, RedBlackTree;
import std.range : iota, front, array, empty;
import std.array : array;
import std.conv : to;
import std.algorithm : map, sort;
import std.string : format;
import std.math : abs;
import std.stdio : stderr;

debug import std.stdio;

public:
alias Variable = string;

struct Assignment
{
    bool[Literal] _assignment;
    RedBlackTree!Literal unassigned;

    this(size_t variableNum)
    {
        this.unassigned = redBlackTree!Literal(iota(1, variableNum + 1).array.to!(Literal[]));
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
        this._assignment[abs(literal)] = literal > 0 ? true : false;
        if (abs(literal) !in unassigned)
        {
            debug writefln("not found: %s", literal);
        }
        unassigned.removeKey(literal);
    }

    Literal getUnassignedLiteral()
    {
        return this.unassigned.array.front;
    }

    bool getTruthOfVariable(Literal id)
    {
        return this._assignment[id];
    }

    string toString() const
    {
        return this._assignment.to!string;
    }

    void fillUnassignedLiterals()
    {
        stderr.writeln(unassigned);
        foreach (literal; unassigned.array)
        {
            this.assign(literal);
        }
    }

    string toDIMACSFormat() const
    {
        Literal[] arr;
        foreach (key; _assignment.keys.sort)
            arr ~= (_assignment[key] ? key : -key);
        return format("v%( %d%) 0", arr);
    }
}
