module solvers.cdcl;
import dimacs;
import cnf : CNF;
import std.container : RedBlackTree, redBlackTree;
import std.typecons : Tuple;

alias Set(T) = RedBlackTree!T;

/+++
+ 0 は \overline \Lambda (conflict node) を表す。
+ \cdots, -3, -2, -1, 1, 2, 3, \cdots を通常のリテラルのために利用する。
+ x > 0 であるとき、
+ 正の整数 x は、x を意味する。
+ 負の整数 -x は、\lnot x を意味する。
+/
alias Literal = long;

/// LAMBDA は conflict node の意。
const Literal LAMBDA = 0;

/// 与えられた Literal を否定したものを返す。
Literal negate(Literal lit) {
    return -lit;
}

/// 節
struct Clause {
    alias ID = size_t;

    /// 節を区別するための ID
    ID id;
    /// 節に含まれる Literal の集合
    Set!Literal literals;
    bool isEmptyClause() {
        return literals.length == 0;
    }
    bool isUnitClause() {
        return literals.length == 1;
    }
    Literal unitLiteral() {
        assert(this.isUnitClause());
        return literals.front;
    }
    bool containsLiteral(Literal lit) {
        return lit in literals;
    }
    auto removeLiteral(Literal lit) {
        return literals.removeKey(lit);
    }

    int opCmp(R)(const R other) const
    {
        return this.id < other.id;
    }
}

private Clause.ID usedIDNum;
Clause.ID nextClauseID() {
    return ++usedIDNum;
}

import std.stdio : File, stdin;
import std.algorithm : filter, map;
import std.array : join, split, array;
import std.conv : to;
import std.range : enumerate, empty;
Clause[] parseInput(File f = stdin) {
    return f.byLine.filter!(line => line[0] != 'c' && line[0] != 'p').join(" ").split.map!(to!long).array.split(0).filter!(arr => !arr.empty).array.enumerate.map!(p => Clause(p.index, redBlackTree!Literal(p.value))).array;
}

struct ImplicationGraph {
    /// dlevel とは、decision level のことをさす。
    alias Node = Tuple!(Literal, "literal", size_t, "dlevel");

    Set!Node nodes;
    Set!Node[Node] successors;
    Set!Node[Node] predecessors;
    Clause.ID[Node][Node] edges;

    void removeLevel(size_t dlevel) {
        foreach(node; nodes) {
            if(node.dlevel >= dlevel) nodes.removeKey(node);
        }
        foreach(key, value; successors) {
            if(key.dlevel >= dlevel) successors.remove(key);
            foreach(node; value) {
                if(node.dlevel >= dlevel) value.removeKey(node);
            }
        }
        foreach(key, value; predecessors) {
            if(key.dlevel >= dlevel) successors.remove(key);
            foreach(node; value) {
                if(node.dlevel >= dlevel) value.removeKey(node);
            }
        }
        foreach(key, value; edges) {
            if(key.dlevel >= dlevel) {
                edges.remove(key);
                continue;
            }
            foreach(key2, _; value) {
                if(key2.dlevel >= dlevel) {
                    value.remove(key2);
                }
            }
        }
    }
}

debug import std.stdio;

/// CDCL を実装した Solver
class CDCLSolver {
    Set!Clause clauses;


    this(Clause[] clauses) {
        this.clauses = redBlackTree!Clause(clauses);
    }

    void deduce() {
        
    }
}