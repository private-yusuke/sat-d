module solvers.cdcl;
import dimacs;
import cnf : CNF;
import std.container : RedBlackTree, redBlackTree;
import std.typecons : Tuple;
import std.algorithm : each;
import std.range : front, popFront;

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
    bool opBinaryRight(string op)(Literal lit) const if (op == "in")
    {
        return lit in literals;
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
    return f.byLine.filter!(line => line[0] != 'c' && line[0] != 'p').join(" ").split.map!(to!long).array.split(0).filter!(arr => !arr.empty).array.enumerate.map!(p => Clause(p.index+1, redBlackTree!Literal(p.value))).array;
}

struct ImplicationGraph {
    /// dlevel とは、decision level のことをさす。
    alias Node = Tuple!(Literal, "literal", size_t, "dlevel");

    Set!Node nodes = redBlackTree!Node;
    Set!Node[Node] successors;
    Set!Node[Node] predecessors;
    Clause.ID[Node][Node] edges;

    Literal newestDecisionLiteral;

    this(ImplicationGraph graph) {
        this.nodes = graph.nodes.dup;
        this.successors = graph.successors.dup;
        this.predecessors = graph.predecessors.dup;
        this.edges = graph.edges.dup;
        this.newestDecisionLiteral = graph.newestDecisionLiteral;
    }

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

    Literal find1UIP(Node start, Node end) {
        foreach_reverse(node; getTopologicallySorted(start, end)) {
            ImplicationGraph tmpGraph = ImplicationGraph(this);
            foreach(predecessor; tmpGraph.predecessors[node])
                tmpGraph.successors[predecessor].removeKey(node);
            foreach(successor; tmpGraph.successors[node])
                tmpGraph.predecessors[successor].removeKey(node);
            
            Node[] queue = [start];
            while(!queue.empty) {
                Node n = queue.front;
                queue.popFront();
                if(end in tmpGraph.successors) return n.literal;
                queue ~= tmpGraph.successors[n].array;
            }
        }
        // decision literal
        return start.literal;
    }

    Node[] getTopologicallySorted(Node start, Node end) {
        Node[] topologicallySorted;
        Node[] arr = [start];
        ImplicationGraph tmpGraph = ImplicationGraph(this);

        while(!arr.empty) {
            Node n = arr.front;
            arr.popFront();
            topologicallySorted ~= n;
            foreach(successor; tmpGraph.successors[n]) {
                tmpGraph.successors[n].removeKey(successor);
                tmpGraph.predecessors[successor].removeKey(n);
                if(tmpGraph.predecessors[successor].empty) {
                    arr ~= successor;
                }
            }
        }
        return topologicallySorted;
    }
}

debug import std.stdio;

/// CDCL を実装した Solver
class CDCLSolver {
    Clause[Clause.ID] clauses;
    Set!(long) unassignedVariables = redBlackTree!long;
    Set!(Clause.ID) availClauses = redBlackTree!(Clause.ID);
    ImplicationGraph implicationGraph;
    size_t currentLevel;

    Set!(Clause.ID) unitClauses = redBlackTree!(Clause.ID);
    Clause[Clause.ID] originalClauses;

    CDCLSolver[] history;

    this(Clause[] clauses) {
        debug writeln("ok");
        foreach(clause; clauses) {
            this.clauses[clause.id] = clause;
            if(clause.isUnitClause) unitClauses.insert(clause.id);
            availClauses.insert(clause.id);
        }
        debug writeln("ok2");
        this.originalClauses = this.clauses.dup;
        usedIDNum = clauses.length;
    }

    /// for deep copy
    this(CDCLSolver solver) {
        this.clauses = solver.clauses.dup;
        this.unassignedVariables = solver.unassignedVariables.dup;
        this.availClauses = solver.availClauses.dup;
        this.implicationGraph = ImplicationGraph(solver.implicationGraph);
        this.currentLevel = solver.currentLevel;
    }

    enum SolverStatus {
        SAT,
        CONFLICT,
        OK
    }

    Literal[] solve() {
        while(true) {
            decideNextBranch();
            with(SolverStatus) while(true) {
                SolverStatus status = deduce();
                if(status == SAT) return implicationGraph.nodes.array.map!(node => node.literal).array;
                if(status == CONFLICT) {
                    auto res = analyzeConflict();
                    if(res.dlevel == 0) return null;
                    backtrack(res.dlevel);
                    addConflictClause(res.conflict);
                }
                else break;
            }
        }
    }

    void decideNextBranch() {
        history ~= new CDCLSolver(this);

        Literal lit = unassignedVariables.front;
        unassignedVariables.removeKey(lit);
        assignLiteral(lit);
        implicationGraph.newestDecisionLiteral = lit;
    }

    SolverStatus deduce() {
        while(!unitClauses.empty) {
            Clause.ID clsID = unitClauses.front;
            unitClauses.removeKey(clsID);
            Literal lit = clauses[clsID].unitLiteral;
            if(ImplicationGraph.Node(-lit, this.currentLevel) in implicationGraph.nodes) {
                assignLiteral(LAMBDA, lit);
                addEdge(-lit, LAMBDA, 0);
                addEdge(lit, LAMBDA, 0);
                return SolverStatus.CONFLICT;
            }
            assignLiteral(lit);
            foreach(oclit; this.originalClauses[clsID].literals)
                addEdge(oclit, lit, clsID);
        }

        if(unassignedVariables.empty) return SolverStatus.SAT;
        else return SolverStatus.OK;
    }

    alias analyzeConflictResult = Tuple!(size_t, "dlevel", Clause, "conflict");
    analyzeConflictResult analyzeConflict() {
        with(ImplicationGraph) {
            if(implicationGraph.predecessors[Node(LAMBDA, currentLevel)].front.dlevel == 0)
                return analyzeConflictResult(0, Clause(0, null));
            Node start = Node(implicationGraph.newestDecisionLiteral, currentLevel);
            Node end = Node(LAMBDA, currentLevel);
            Clause conflict = newClause(implicationGraph.find1UIP(start, end));
            return analyzeConflictResult(currentLevel, conflict);
        }
    }

    void backtrack(size_t dlevel) {
        assert(this.history.length == currentLevel);
        CDCLSolver oldSolver = this.history[dlevel];
        this.history = this.history[0..dlevel];

        this.clauses = oldSolver.clauses;
        this.unassignedVariables = oldSolver.unassignedVariables;
        this.availClauses = oldSolver.availClauses;
        this.implicationGraph = oldSolver.implicationGraph;
        this.currentLevel = oldSolver.currentLevel;
    }

    Clause newClause(T...)(T literals) {
        usedIDNum++;
        return Clause(usedIDNum, redBlackTree!Literal(literals));
    }

    void addConflictClause(Clause conflict) {
        assert(conflict.id !in clauses);
        clauses[conflict.id] = conflict;
        originalClauses[conflict.id] = conflict;
        if(conflict.isUnitClause) unitClauses.insert(conflict.id);
    }

    void assignLiteral(T...)(T literals) {
        with(this.implicationGraph) foreach(lit; literals) {
            addNode(lit, this.currentLevel);
            removeClausesContaining(lit);
            removeLiteralFromClauses(lit);
            availClauses.array
                        .filter!(clauseID => clauses[clauseID].isUnitClause)
                        .each!(clauseID => unitClauses.insert(clauseID));
        }
    }

    void addNode(Literal lit, size_t dlevel) {
        assert(implicationGraph.nodes.insert(ImplicationGraph.Node(lit, dlevel)));
    }

    void addEdge(Literal from, Literal to, Clause.ID clauseID) {
        with(ImplicationGraph) {
            Node fromNode = Node(from, this.currentLevel), toNode = Node(to, this.currentLevel);
            assert(fromNode in implicationGraph.nodes && toNode in implicationGraph.nodes);
            implicationGraph.successors[fromNode].insert(toNode);
            implicationGraph.predecessors[toNode].insert(fromNode);
            implicationGraph.edges[fromNode][toNode] = clauseID;
        }
    }

    void removeClausesContaining(Literal lit) {
        availClauses.array
                    .filter!(clauseID => lit in clauses[clauseID])
                    .each!(clauseID => availClauses.removeKey(clauseID));
    }
    void removeLiteralFromClauses(Literal lit) {
        availClauses.array.each!(clauseID => clauses[clauseID].removeLiteral(lit));
    }
}