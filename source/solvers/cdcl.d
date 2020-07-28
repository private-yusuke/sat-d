module solvers.cdcl;
import dimacs;
import cnf : CNF;
import std.container : RedBlackTree, redBlackTree;
import std.typecons : Tuple;
import std.algorithm : each, any, sort;
import std.range : front, popFront, iota;
import std.math : abs;
import std.string : format;

import std.stdio;

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

    string toString() {
        return format("%(%d ∨ %)", literals.array);
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

    Node getNode(Literal lit) {
        // stderr.writeln("getNode");
        // stderr.writeln(lit);
        // stderr.writeln(nodes.array.filter!(n => n.literal == lit));
        return nodes.array.filter!(n => n.literal == lit).front;
    }

    Literal find1UIP(Node start, Node end) {
        foreach_reverse(node; getTopologicallySorted(start, end)) {
            ImplicationGraph tmpGraph = ImplicationGraph(this);
            if(node in tmpGraph.predecessors)
                foreach(predecessor; tmpGraph.predecessors[node])
                    tmpGraph.successors[predecessor].removeKey(node);
            if(node in tmpGraph.successors)
                foreach(successor; tmpGraph.successors[node])
                    tmpGraph.predecessors[successor].removeKey(node);
            
            Node[] queue = [start];
            while(!queue.empty) {
                Node n = queue.front;
                queue.popFront();
                if(end in tmpGraph.successors) return node.literal;
                if(n in tmpGraph.successors)
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
            if(n !in tmpGraph.successors) continue;
            stderr.writeln(n);
            stderr.writeln(tmpGraph.successors);
            foreach(successor; tmpGraph.successors[n].array) {
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
        foreach(clause; clauses) {
            this.clauses[clause.id] = clause;
            if(clause.isUnitClause) unitClauses.insert(clause.id);
            availClauses.insert(clause.id);
            stderr.writefln("%d: %s", clause.id, clause);
        }
        this.originalClauses = this.clauses.dup;
        usedIDNum = clauses.length;
        unassignedVariables = redBlackTree!long(iota(1, clauses.length).array.to!(long[]));
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
                stderr.writefln("Deduce done. nodes: %(%s, %)", implicationGraph.nodes.array.map!(
                    p => format("(%d, %d)", p[0], p[1])
                ));
                if(status == SAT) return implicationGraph.nodes.array.map!(node => node.literal).array;
                if(status == CONFLICT) {
                    auto res = analyzeConflict();
                    if(res.dlevel == 0) return [];
                    backtrack(res.dlevel - 1);
                    addConflictClause(res.conflict);
                }
                else break;
            }
        }
    }

    void decideNextBranch() {
        history ~= new CDCLSolver(this);

        stderr.writefln("unassigned: %s", unassignedVariables);
        Literal lit = unassignedVariables.front;
        unassignedVariables.removeKey(lit);
        stderr.writefln("decision literal: %d", lit);
        currentLevel++;
        assignLiteral(lit);
        implicationGraph.newestDecisionLiteral = lit;
    }

    SolverStatus deduce() {
        while(!unitClauses.empty) {
            stderr.writeln("=== deduce continues");
            stderr.writefln("%((%s) ∧ %)", clauses.values.filter!(c => c.id in availClauses).array.sort!((a, b) => a.id < b.id));
            // stderr.writefln("unit clauses: %s", unitClauses);
            Clause.ID clsID = unitClauses.front;
            unitClauses.removeKey(clsID);
            Literal lit = clauses[clsID].unitLiteral;
            if(iota(0, currentLevel+1).map!(l => ImplicationGraph.Node(-lit, l))
                .any!(n => n in implicationGraph.nodes)) {
                stderr.writeln("GENERATE CONFLICT!");
                assignLiteral(LAMBDA, lit);
                addEdge(-lit, LAMBDA, 0);
                addEdge(lit, LAMBDA, 0);
                return SolverStatus.CONFLICT;
            }
            // stderr.writefln("!unit clauses: %s", unitClauses);
            assignLiteral(lit);
            // stderr.writefln(">unit clauses: %s", unitClauses);
            foreach(oclit; this.originalClauses[clsID].literals.array.filter!(oclit => oclit != lit))
                addEdge(oclit, lit, clsID);
        }
            

        if(unassignedVariables.empty) return SolverStatus.SAT;
        else return SolverStatus.OK;
    }

    alias analyzeConflictResult = Tuple!(size_t, "dlevel", Clause, "conflict");
    analyzeConflictResult analyzeConflict() {
        with(ImplicationGraph) {
            // if(implicationGraph.predecessors[Node(LAMBDA, currentLevel)].front.dlevel == 0)
            if(currentLevel == 0)
                return analyzeConflictResult(0, Clause(0, null));
            Node start = Node(implicationGraph.newestDecisionLiteral, currentLevel);
            Node end = Node(LAMBDA, currentLevel);
            Clause conflict = newClause(-implicationGraph.find1UIP(start, end));
            return analyzeConflictResult(currentLevel, conflict);
        }
    }

    void backtrack(size_t dlevel) {
        stderr.writefln("backtrack from %d to %d", currentLevel, dlevel);
        stderr.writefln("history length: %d, currentLevel: %d", this.history.length, currentLevel);
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
        stderr.writefln("conflict clause: %s", conflict);
        assert(conflict.id !in clauses);
        clauses[conflict.id] = conflict;
        originalClauses[conflict.id] = conflict;
        availClauses.insert(conflict.id);
        if(conflict.isUnitClause) unitClauses.insert(conflict.id);
    }

    void assignLiteral(T...)(T literals) {
        with(this.implicationGraph) foreach(lit; literals) {
            addNode(lit, this.currentLevel);
            removeClausesContaining(lit);
            removeLiteralFromClauses(-lit);
            unassignedVariables.removeKey(abs(lit));
            // stderr.writefln("availClauses: %s", availClauses);
            availClauses.array
                        .filter!(clauseID => clauses[clauseID].isUnitClause)
                        .each!(clauseID => unitClauses.insert(clauseID));
        }
    }

    void addNode(Literal lit, size_t dlevel) {
        stderr.writefln("new node: %s, at level %s", lit, dlevel);
        implicationGraph.nodes.insert(ImplicationGraph.Node(lit, dlevel));
    }

    void addEdge(Literal from, Literal to, Clause.ID clauseID) {
        with(ImplicationGraph) {
            stderr.writefln("Add edge from %s to %s", from, to);
            Node fromNode = implicationGraph.getNode(from), toNode = implicationGraph.getNode(to);
            if(fromNode !in implicationGraph.successors)
                implicationGraph.successors[fromNode] = redBlackTree!Node;
            implicationGraph.successors[fromNode].insert(toNode);
            if(fromNode !in implicationGraph.predecessors)
                implicationGraph.predecessors[toNode] = redBlackTree!Node;
            implicationGraph.predecessors[toNode].insert(fromNode);
            implicationGraph.edges[fromNode][toNode] = clauseID;
        }
    }

    void removeClausesContaining(Literal lit) {
        // stderr.writefln("these will be removed: %(%d, %)", availClauses.array.filter!(clauseID => lit in clauses[clauseID]));
        foreach(clauseID; availClauses.array.filter!(clauseID => lit in clauses[clauseID])) {
            availClauses.removeKey(clauseID);
            unitClauses.removeKey(clauseID);
        }
    }
    void removeLiteralFromClauses(Literal lit) {
        // stderr.writefln("this literal will be removed: %d", lit);
        // stderr.writeln(availClauses.array);
        foreach(clauseID; availClauses) {
            // stderr.writeln(clauses[clauseID]);
            if(!clauses[clauseID].isUnitClause)
                clauses[clauseID].removeLiteral(lit);
            // stderr.writeln(clauses[clauseID]);
            if(clauses[clauseID].isUnitClause)
                unitClauses.insert(clauseID);
            if(clauses[clauseID].isEmptyClause)
                unitClauses.removeKey(clauseID);
        }
    }
}