module solvers.cdcl;
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

    this(ID id, Set!Literal literals) {
        this.id = id;
        this.literals = literals;
    }
    this(Clause clause) {
        this.id = clause.id;
        this.literals = clause.literals.dup;
    }
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
        if(literals.length == 0) return "(empty)";
        else return format("(%(%d ∨ %))", literals.array);
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
// Clause parseInput(File f = stdin) {
//     return f.byLine.filter!(line => line[0] != 'c' && line[0] != 'p').join(" ").split.map!(to!long).array.split(0).filter!(arr => !arr.empty).array.enumerate.map!(p => Clause(p.index+1, redBlackTree!Literal(p.value))).array;
// }

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
        foreach(key, value; graph.successors)
            this.successors[key] = value.dup;
        foreach(key, value; graph.predecessors)
            this.predecessors[key] = value.dup;
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
            // stderr.writeln(n);
            // stderr.writeln(tmpGraph.successors);
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
    auto availClauses = redBlackTree!("a > b", Clause.ID);
    ImplicationGraph implicationGraph;
    size_t currentLevel;

    auto unitClauses = redBlackTree!("a > b", Clause.ID);
    Clause[Clause.ID] originalClauses;
    Literal[] decisionVariables;

    CDCLSolver[] history;

    this() {}

    void initialize(parseResult res) {
        auto clauses = res.clauses;
        foreach(clause; clauses) {
            this.clauses[clause.id] = clause;
            if(clause.isUnitClause) unitClauses.insert(clause.id);
            availClauses.insert(clause.id);
            stderr.writefln("%d: %s", clause.id, clause);
        }
        foreach(key, value; this.clauses) {
            this.originalClauses[key] = Clause(value);
        }
        usedIDNum = clauses.length;
        unassignedVariables = redBlackTree!long(iota(1, res.preamble.variables+1).array.to!(long[]));
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
        stderr.writefln("given clauses: %s", this.clauses.values);
        if(this.clauses.values.any!(c => c.literals.length == 0)) return null;
        while(true) {
            decideNextBranch();
            with(SolverStatus) while(true) {
                SolverStatus status = deduce();
                toDOT(status == SolverStatus.CONFLICT);
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
        decisionVariables ~= lit;
        implicationGraph.newestDecisionLiteral = lit;
    }

    SolverStatus deduce() {
        while(!unitClauses.empty) {
            // stderr.writefln("clauses: %(%s, %)", originalClauses.values);
            stderr.writeln("=== deduce continues");
            stderr.writefln("%(%s ∧ %)", clauses.values.filter!(c => c.id in availClauses).array.sort!((a, b) => a.id < b.id));
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
        this.unitClauses = oldSolver.unitClauses.dup;
        this.decisionVariables = oldSolver.decisionVariables;
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

    Preamble parsePreamble(File f = stdin)
    {
        string[] inp;

        // comments appear in the input is ignored
        do
        {
            inp = f.readln.split;
        }
        while (inp.length < 1 || inp[0] == "c");

        if (inp[0] != "p")
        {
            error("Unknown command: %s", inp[0]);
            assert(0);
        }

        else
        {
            if (inp.length != 4)
                error("Not enough arguments");

            if (inp[1] != "cnf")
                error("Given format \"%s\" not supported", inp[1]);

            size_t variables, clauses;
            try
            {
                variables = inp[2].to!size_t, clauses = inp[3].to!size_t;
            }
            catch (Exception e)
            {
                error("Numbers in preamble couldn't be parsed");
            }
            return Preamble(variables, clauses);
        }
    }
    struct Preamble
    {
        size_t variables;
        size_t clauses;
    }
    alias parseResult = Tuple!(Clause[], "clauses", Preamble, "preamble");
    parseResult parseClauses(File f = stdin)
    {
        Preamble preamble = parsePreamble(f);
        Clause[] clauses;
        Literal[] literals;

        // read until EOF then ...
        long[] tokens;
        try
        {
            tokens = f.byLineCopy.array.join(' ').split.to!(long[]);
        }
        catch (Exception e)
        {
            error("Malformed input");
        }

        foreach (token; tokens)
        {
            if (token == 0)
            {
                if (clauses.length >= preamble.clauses)
                    error("Too many clauses");

                Clause clause = newClause(literals);
                clauses ~= clause;
                literals = null;
                continue;
            }
            if (abs(token) > preamble.variables)
                error("Given %d but variable bound is %d", abs(token), preamble.variables);

            Literal literal = token;
            literals ~= literal;
        }
        if (!literals.empty)
            error("Unexpected End of File");

        return parseResult(clauses, preamble);
    
    }
    private int dotCounter;
    void toDOT(bool conflict) {
        string res = "digraph cdcl {\n";
        if(conflict) res ~= "0 [label = \"Λ\"];\n";
        foreach(variable; decisionVariables)
            res ~= format("%d [shape = record, label = \"Decision variable %d at level %d\"];\n", variable, variable, implicationGraph.getNode(variable).dlevel);

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
