module solvers.cdcl;
import cnf : CNF, Clause, Literal;
import dimacs: Preamble, parseResult;
import std.container : RedBlackTree, redBlackTree;
import std.typecons : Tuple;
import std.algorithm : each, any, sort, filter, map;
import std.range : front, popFront, iota, enumerate, empty;
import std.math : abs;
import std.string : format;
import std.stdio : File, stdin;
import std.array : join, split, array;
import std.conv : to;

import std.stdio;

alias Set(T) = RedBlackTree!T;

/// LAMBDA は conflict node の意。
const Literal LAMBDA = 0;

private Clause.ID usedIDNum;
Clause.ID nextClauseID() {
    return ++usedIDNum;
}

struct ImplicationGraph {
    /// dlevel とは、decision level のことをさす。
    alias Node = Tuple!(Literal, "literal", size_t, "dlevel");

    Set!Node nodes = redBlackTree!Node;
    Set!Node[Node] successors;
    Set!Node[Node] predecessors;
    Clause.ID[Node][Node] edges;

    Literal[] decisionLiterals;

    this(ImplicationGraph graph) {
        this.nodes = graph.nodes.dup;
        foreach(key, value; graph.successors)
            this.successors[key] = value.dup;
        foreach(key, value; graph.predecessors)
            this.predecessors[key] = value.dup;
        foreach(key, value; graph.edges)
            this.edges[key] = value.dup;
        
        this.decisionLiterals = graph.decisionLiterals.dup;
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
        assert(start in nodes && end in nodes);
        auto topSorted = getTopologicallySorted(start, end);
        import std.algorithm : canFind;
        debug stderr.writefln("sorted: %(%s %)", topSorted.map!(n => format("(%s, %s)", n.literal, n.dlevel)));
        if(!topSorted.canFind(start) || !topSorted.canFind(end)) return 0;
        
        if(topSorted.length < 2) return topSorted[0].literal;
        foreach_reverse(node; topSorted.filter!(n => n != start && n != end).array) {
            ImplicationGraph tmpGraph = ImplicationGraph(this);
            if(node in tmpGraph.predecessors)
                foreach(predecessor; tmpGraph.predecessors[node])
                    tmpGraph.successors[predecessor].removeKey(node);
            if(node in tmpGraph.successors)
                foreach(successor; tmpGraph.successors[node])
                    tmpGraph.predecessors[successor].removeKey(node);
            
            bool flag = true;
            Node[] queue = [start];
            while(!queue.empty) {
                // debug stderr.writefln("queue: %(%s %)", queue);
                Node n = queue.front;
                queue.popFront();
                if(n in tmpGraph.successors && end in tmpGraph.successors[n]) flag = false;
                if(n in tmpGraph.successors)
                    queue ~= tmpGraph.successors[n].array;
            }
            if(flag) return node.literal;
        }
        // decision literal
        return start.literal;
    }

    Node[] getTopologicallySorted(Node start, Node end) {
        Node[] topologicallySorted;
        Set!Node visited = redBlackTree!Node;
        ImplicationGraph tmpGraph = ImplicationGraph(this);

        void visit(Node n) {
            if(visited.insert(n)) {
                if(n in tmpGraph.successors)
                    foreach(m; tmpGraph.successors[n])
                        visit(m);
                topologicallySorted ~= n;    
            }
        }

        visit(start);

        debug stderr.writeln(topologicallySorted);
        return topologicallySorted;
    }

}

/// CDCL を実装した Solver
class CDCLSolver {
    Clause[Clause.ID] clauses;
    Set!(long) unassignedVariables = redBlackTree!long;
    auto availClauses = redBlackTree!("a > b", Clause.ID);
    ImplicationGraph implicationGraph;
    size_t currentLevel;

    auto unitClauses = redBlackTree!("a > b", Clause.ID);
    Clause[Clause.ID] originalClauses;
    Literal[] decisionVariables;
    bool generateGraph = false;
    Preamble preamble;

    CDCLSolver[] history;

    this() {}

    void initialize(parseResult res) {
        auto clauses = res.clauses;
        foreach(clause; clauses) {
            this.clauses[clause.id] = clause;
            if(clause.isUnitClause) unitClauses.insert(clause.id);
            availClauses.insert(clause.id);
            debug stderr.writefln("%d: %s", clause.id, clause);
        }
        foreach(key, value; this.clauses) {
            this.originalClauses[key] = Clause(value);
        }
        usedIDNum = clauses.length;
        unassignedVariables = redBlackTree!long(iota(1, res.preamble.variables+1).array.to!(long[]));
        this.preamble = res.preamble;
    }

    /// for deep copy
    this(CDCLSolver solver) {
        foreach(key, value; solver.clauses)
            this.clauses[key] = Clause(value);
        this.unassignedVariables = solver.unassignedVariables.dup;
        this.availClauses = solver.availClauses.dup;
        this.implicationGraph = ImplicationGraph(solver.implicationGraph);
        this.currentLevel = solver.currentLevel;
        this.decisionVariables = solver.decisionVariables.dup;
    }

    enum SolverStatus {
        SAT,
        CONFLICT,
        OK
    }

    Literal[] solve() {
        debug stderr.writefln("given clauses: %s", this.clauses.values);
        if(this.clauses.values.any!(c => c.literals.length == 0)) return null;
        while(true) {
            decideNextBranch();
            with(SolverStatus) while(true) {
                SolverStatus status = deduce();
                if(status == SolverStatus.CONFLICT)
                    toDOT(true);
                debug stderr.writefln("Deduce done. nodes: %(%s, %)", implicationGraph.nodes.array.map!(
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

        debug stderr.writefln("unassigned: %s", unassignedVariables);
        Literal lit = unassignedVariables.front;
        unassignedVariables.removeKey(lit);
        debug stderr.writefln("decision literal: %d", lit);
        currentLevel++;
        assignLiteral(lit);
        decisionVariables ~= lit;
        implicationGraph.decisionLiterals ~= lit;
    }

    SolverStatus deduce() {
        while(!unitClauses.empty) {
            // stderr.writefln("clauses: %(%s, %)", originalClauses.values);
            // stderr.writeln("=== deduce continues");
            // stderr.writefln("%(%s ∧ %)", clauses.values.filter!(c => c.id in availClauses).array.sort!((a, b) => a.id < b.id));
            // stderr.writefln("unit clauses: %s", unitClauses);
            Clause.ID clsID = unitClauses.front;
            unitClauses.removeKey(clsID);
            Literal lit = clauses[clsID].unitLiteral;
            if(iota(0, currentLevel+1).map!(l => ImplicationGraph.Node(-lit, l))
                .any!(n => n in implicationGraph.nodes)) {
                debug stderr.writeln("GENERATE CONFLICT!");
                assignLiteral(LAMBDA, lit);
                addEdge(-lit, LAMBDA, 0);
                addEdge(lit, LAMBDA, 0);
                
                foreach(pred; this.originalClauses[clsID].literals.array.filter!(pred => pred != lit))
                    addEdge(pred, lit, clsID);
                return SolverStatus.CONFLICT;
            }
            // stderr.writefln("!unit clauses: %s", unitClauses);
            assignLiteral(lit);
            // stderr.writefln(">unit clauses: %s", unitClauses);
            foreach(oclit; this.originalClauses[clsID].literals.array.filter!(oclit => oclit != lit))
                addEdge(oclit, lit, clsID);
            toDOT(false);
        }
        if(unassignedVariables.empty) return SolverStatus.SAT;
        else return SolverStatus.OK;
    }

    alias analyzeConflictResult = Tuple!(size_t, "dlevel", Clause, "conflict");
    analyzeConflictResult analyzeConflict() {
        auto level = currentLevel;
        with(ImplicationGraph) while(true) {
            // if(implicationGraph.predecessors[Node(LAMBDA, currentLevel)].front.dlevel == 0)
            if(level == 0)
                return analyzeConflictResult(0, Clause(0, []));
            
            Node start = Node(implicationGraph.decisionLiterals[level - 1], level);
            Node end = Node(LAMBDA, currentLevel);
            auto lit = implicationGraph.find1UIP(start, end);
            if(lit == 0) {
                level--;
                continue;
            }
            Clause conflict = newClause(-implicationGraph.find1UIP(start, end));
            return analyzeConflictResult(currentLevel, conflict);
        }
    }

    void backtrack(size_t dlevel) {
        debug stderr.writefln("backtrack from %d to %d", currentLevel, dlevel);
        debug stderr.writefln("history length: %d, currentLevel: %d", this.history.length, currentLevel);
        assert(this.history.length == currentLevel);
        CDCLSolver oldSolver = this.history[dlevel];
        this.history = this.history[0..dlevel];

        this.clauses = oldSolver.clauses;
        this.unassignedVariables = oldSolver.unassignedVariables;
        this.availClauses = oldSolver.availClauses;
        this.unitClauses = oldSolver.unitClauses.dup;
        this.decisionVariables = oldSolver.decisionVariables;
        this.implicationGraph = oldSolver.implicationGraph;
        this.currentLevel = oldSolver.currentLevel;

        this.unitClauses.clear();
        availClauses.array
                        .filter!(clauseID => clauses[clauseID].isUnitClause)
                        .each!(clauseID => unitClauses.insert(clauseID));
    }

    Clause newClause(T...)(T literals) {
        usedIDNum++;
        return Clause(usedIDNum, redBlackTree!Literal(literals));
    }

    void addConflictClause(Clause conflict) {
        debug stderr.writefln("conflict clause: %s", conflict);
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
        debug stderr.writefln("new node: %s, at level %s", lit, dlevel);
        implicationGraph.nodes.insert(ImplicationGraph.Node(lit, dlevel));
    }

    void addEdge(Literal from, Literal to, Clause.ID clauseID) {
        with(ImplicationGraph) {
            debug stderr.writefln("Add edge from %s to %s", from, to);
            Node fromNode = implicationGraph.getNode(-from), toNode = implicationGraph.getNode(to);
            if(fromNode !in implicationGraph.successors)
                implicationGraph.successors[fromNode] = redBlackTree!Node;
            implicationGraph.successors[fromNode].insert(toNode);
            if(toNode !in implicationGraph.predecessors)
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

    
    private int dotCounter;
    void toDOT(bool conflict) {
        if(!generateGraph) return;
        string res = "digraph cdcl {\n";
        res ~= "graph [layout = dot];\n";
        if(conflict) res ~= "0 [label = \"Λ\"];\n";
        foreach(variable; decisionVariables)
            res ~= format("%d [shape = record, label = \"Decision variable %d at level %d\"];\n", variable, variable, implicationGraph.getNode(variable).dlevel);
        foreach(variable; implicationGraph.nodes.array.
        filter!(n => this.originalClauses.array.
        filter!(c => c.id > preamble.clauses).
        array.any!(c => n.literal in c)))
            res ~= format("%d [shape = parallelogram, label = \"%d from learnt clause\", fillcolor = \"#cde0b4\"];\n", variable.literal, variable.literal);

        // stderr.writeln(implicationGraph.edges);
        foreach(from, tos; implicationGraph.edges) {
            foreach(to, clause; tos) {
                res ~= format("%s -> %s [label = \"%s\"];\n", from.literal, to.literal, clause == 0 ? "" : this.originalClauses[clause].toString);
            }
        }

        res ~= "}\n";
        import std.file;
        std.file.write(format("%d.dot", dotCounter), res);
        dotCounter++;
    }
}

// TODO: ちゃんと共通させてかけるようにする

// TODO: currently loading only from stdin; perhaps from file?
void error(A...)(string msg, A args)
{
    throw new DIMACSReadException(format(msg, args));
}

class DIMACSReadException : Exception
{
    this(string msg)
    {
        super(msg);
    }
}
