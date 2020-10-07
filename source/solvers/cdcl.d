module solvers.cdcl;
import cnf : CNF, Clause, Literal, Set;
import dimacs : Preamble, parseResult;
import std.container : RedBlackTree, redBlackTree;
import std.typecons : Tuple;
import std.algorithm : each, any, sort, filter, map, countUntil, min, count, all;
import std.range : front, popFront, iota, enumerate, empty, retro;
import std.math : abs;
import std.string : format;
import std.stdio : File, stdin;
import std.array : join, split, array;
import std.conv : to;
import std.variant : Algebraic;

import std.stdio;

/// LAMBDA は conflict node の意。
const Literal LAMBDA = 0;

private Clause.ID usedIDNum;
Clause.ID nextClauseID()
{
    return ++usedIDNum;
}

struct ImplicationGraph
{
    /// dlevel とは、decision level のことをさす。
    alias Node = Tuple!(Literal, "literal", size_t, "dlevel");

    Set!Node nodes;
    Set!Node[Node] successors;
    Set!Node[Node] predecessors;
    Clause.ID[Node][Node] edges;

    Literal[] decisionLiterals;

    void initalize()
    {
        nodes = redBlackTree!Node;
    }

    this(ImplicationGraph graph)
    {
        this.nodes = graph.nodes.dup;
        foreach (key, value; graph.successors)
            this.successors[key] = value.dup;
        foreach (key, value; graph.predecessors)
            this.predecessors[key] = value.dup;
        foreach (key, value; graph.edges)
            this.edges[key] = value.dup;

        this.decisionLiterals = graph.decisionLiterals.dup;
    }

    void removeLevel(size_t dlevel)
    {
        foreach (node; nodes)
        {
            if (node.dlevel >= dlevel)
                nodes.removeKey(node);
        }
        foreach (key, value; successors)
        {
            if (key.dlevel >= dlevel)
                successors.remove(key);
            foreach (node; value)
            {
                if (node.dlevel >= dlevel)
                    value.removeKey(node);
            }
        }
        foreach (key, value; predecessors)
        {
            if (key.dlevel >= dlevel)
                successors.remove(key);
            foreach (node; value)
            {
                if (node.dlevel >= dlevel)
                    value.removeKey(node);
            }
        }
        foreach (key, value; edges)
        {
            if (key.dlevel >= dlevel)
            {
                edges.remove(key);
                continue;
            }
            foreach (key2, _; value)
            {
                if (key2.dlevel >= dlevel)
                {
                    value.remove(key2);
                }
            }
        }
    }

    Node getNode(Literal lit)
    {
        // stderr.writeln("getNode");
        // stderr.writeln(lit);
        // stderr.writeln(nodes.array.filter!(n => n.literal == lit));
        auto tmp = nodes.array.filter!(n => n.literal == lit);
        assert(tmp.count == 1);
        return tmp.front;
    }

    Set!Node get1UIPCut(size_t dlevel)
    {
        Set!Node res = redBlackTree!Node;

        Set!Node visited = redBlackTree!Node;

        Node[] queue = [Node(0, dlevel)];
        bool found1UIP = false;
        immutable Node decisionNode = Node(decisionLiterals[$ - 1], dlevel);
        bool is1UIPDecisionNode = false;

        while (!found1UIP)
        {
            Node[] nextQueue;
            foreach (Node n; queue)
            {
                if (n in predecessors)
                {
                    foreach (pred; predecessors[n])
                    {
                        if (pred == decisionNode)
                            is1UIPDecisionNode = true;
                        if (visited.insert(pred))
                        {
                            if (pred.dlevel != dlevel)
                                res.insert(pred);
                            else
                                nextQueue ~= pred;
                        }
                    }
                }
            }
            if (!is1UIPDecisionNode && nextQueue.length == 1)
            {
                found1UIP = true;
                res.insert(nextQueue[0]);
            }
            else if (nextQueue.length == 0)
            {
                found1UIP = true;
                res.insert(decisionNode);
            }
            queue = nextQueue;
            debug stderr.writefln("nextQueue: %s", nextQueue);
        }

        return res;
    }

    Node find1UIP(Node start, Node end, Node[] topSorted)
    {
        assert(start in nodes && end in nodes);
        import std.algorithm : canFind;

        Node[] queue;
        queue ~= predecessors[end].array.filter!(node => node.dlevel == end.dlevel).array;
        while (queue.length != 1)
        {
            assert(queue.length != 0);
            Set!Node nextQueue = redBlackTree!Node;
            foreach (node; queue)
            {
                if (node in predecessors)
                    foreach (pred; predecessors[node])
                    {
                        if (pred.dlevel == end.dlevel)
                        {
                            nextQueue.insert(pred);
                        }
                    }
            }
            queue = nextQueue.array;
        }
        return queue[0];
    }

    Node[] getTopologicallySorted()
    {
        Node[] topologicallySorted;
        Set!Node visited = redBlackTree!Node;
        ImplicationGraph tmpGraph = ImplicationGraph(this);

        void visit(Node n)
        {
            if (visited.insert(n))
            {
                if (n in tmpGraph.successors)
                    foreach (m; tmpGraph.successors[n])
                        visit(m);
                topologicallySorted ~= n;
            }
        }

        foreach (dlevel, lit; decisionLiterals)
            visit(Node(lit, dlevel + 1));
        foreach (node; nodes)
            visit(node);

        // debug stderr.writeln(topologicallySorted);
        return topologicallySorted;
    }

    Set!Node getReachablesFrom(Node node)
    {
        Set!Node reachableNodes = redBlackTree!Node;

        Node[] queue;
        queue ~= node;

        while (!queue.empty)
        {
            Node n = queue.front;
            queue.popFront();
            if (reachableNodes.insert(n))
            {
                if (n in successors)
                    foreach (succ; successors[n])
                        queue ~= succ;
            }
        }

        return reachableNodes;
    }

    void transformToConflictGraph(size_t level)
    {
        Set!Node conflictGraphNodes = redBlackTree!Node;
        Node[] queue;
        queue ~= Node(0, level);

        while (!queue.empty)
        {
            Node n = queue.front;
            queue.popFront();
            if (conflictGraphNodes.insert(n))
            {
                if (n in predecessors)
                    foreach (pred; predecessors[n])
                        queue ~= pred;
            }
        }

        Set!Node[Node] successors_;
        Set!Node[Node] predecessors_;
        Clause.ID[Node][Node] edges_;

        foreach (n; conflictGraphNodes)
        {
            if (n in successors)
                foreach (node; successors[n])
                    if (node in conflictGraphNodes)
                    {
                        if (n !in successors_)
                            successors_[n] = redBlackTree!Node;
                        successors_[n].insert(node);
                    }
            if (n in predecessors)
                foreach (node; predecessors[n])
                    if (node in conflictGraphNodes)
                    {
                        if (n !in predecessors_)
                            predecessors_[n] = redBlackTree!Node;
                        predecessors_[n].insert(node);
                    }
        }

        foreach (from, tos; successors_)
            foreach (to; tos)
                edges_[from][to] = edges[from][to];

        nodes = conflictGraphNodes;
        successors = successors_;
        predecessors = predecessors_;
        edges = edges_;
    }
}

alias CDCLSolverResult = Algebraic!(Literal[], typeof(null));

/// CDCL を実装した Solver
class CDCLSolver
{
    Clause[Clause.ID] clauses;
    Set!(long) unassignedVariables;
    auto availClauses = redBlackTree!("a > b", Clause.ID);
    ImplicationGraph implicationGraph;
    size_t currentLevel;

    auto unitClauses = redBlackTree!("a > b", Clause.ID);
    Clause[Clause.ID] originalClauses;
    Literal[] decisionVariables;
    bool generateGraph = false;
    Preamble preamble;
    ulong variableNum;

    Literal[] assignedLiterals;
    Clause.ID[] reasons;
    ulong[] assignedNumPerLevel;
    parseResult inp;

    this()
    {
        implicationGraph.initalize();
    }

    void initialize(parseResult res)
    {
        this.inp = inp;

        availClauses.clear();
        unitClauses.clear();
        implicationGraph = ImplicationGraph();
        implicationGraph.initalize();
        currentLevel = 0;
        originalClauses = null;
        decisionVariables = [];
        assignedLiterals = [];
        assignedNumPerLevel = [];

        auto clauses = res.clauses;
        foreach (clause; clauses)
        {
            this.clauses[clause.id] = clause;
            if (clause.isUnitClause)
                unitClauses.insert(clause.id);
            availClauses.insert(clause.id);
            debug stderr.writefln("%d: %s", clause.id, clause);
        }
        foreach (key, value; this.clauses)
        {
            this.originalClauses[key] = Clause(value);
        }
        usedIDNum = clauses.length;
        unassignedVariables = redBlackTree!long(iota(1, variableNum + 1).array.to!(long[]));
        debug stderr.writefln("*** %s", unassignedVariables);
        this.preamble = res.preamble;
    }

    /// for deep copy
    this(CDCLSolver solver)
    {
        foreach (key, value; solver.clauses)
            this.clauses[key] = Clause(value);
        this.unassignedVariables = solver.unassignedVariables.dup;
        this.availClauses = solver.availClauses.dup;
        this.implicationGraph = ImplicationGraph(solver.implicationGraph);
        this.currentLevel = solver.currentLevel;
        this.decisionVariables = solver.decisionVariables.dup;
    }

    enum SolverStatus
    {
        SAT,
        CONFLICT,
        OK
    }

    CDCLSolverResult solve()
    {
        debug stderr.writefln("given clauses: %s", this.clauses.values);

        if (this.clauses.values.any!(c => c.literals.length == 0))
            return CDCLSolverResult(null);
        if (this.preamble.variables == 0 && this.preamble.clauses == 0)
            return CDCLSolverResult(cast(Literal[])[]);
        while (true)
        {
            while (true)
            {
                SolverStatus status = deduce();
                if (status == SolverStatus.CONFLICT)
                    toDOT(true);
                debug stderr.writefln("Deduce done. nodes: %(%s, %)",
                        implicationGraph.nodes.array.map!(p => format("(%d, %d)", p[0], p[1])));
                if (status == SolverStatus.SAT)
                    return CDCLSolverResult(implicationGraph.nodes.array.map!(node => node.literal)
                            .array);
                if (status == SolverStatus.CONFLICT)
                {
                    auto res = analyzeConflict();
                    if (res.blevel == -1)
                        return CDCLSolverResult(null);

                    //debug stderr.writefln("conflict clause: %s", res.conflict);
                    addConflictClause(res.conflict);
                    backtrack(res.blevel);
                }
                else
                    break;
            }
            decideNextBranch();
        }
    }

    void decideNextBranch()
    {
        // debug stderr.writefln("unassigned: %s", unassignedVariables);
        Literal lit = unassignedVariables.front;
        debug stderr.writefln("decision literal: %d", lit);
        currentLevel++;
        assignedNumPerLevel ~= assignedLiterals.length;
        assignLiteral(lit);
        reasons ~= 0;
        decisionVariables ~= lit;
        implicationGraph.decisionLiterals ~= lit;
    }

    SolverStatus deduce()
    {
        while (!unitClauses.empty)
        {
            // stderr.writefln("clauses: %(%s, %)", originalClauses.values);
            // stderr.writeln("=== deduce continues");
            // stderr.writefln("%(%s ∧ %)", clauses.values.filter!(c => c.id in availClauses).array.sort!((a, b) => a.id < b.id));
            // stderr.writefln("unit clauses: %(%s, %)", unitClauses.array.map!(id => clauses[id]));
            Clause.ID clsID = unitClauses.front;
            unitClauses.removeKey(clsID);
            Literal lit = clauses[clsID].unitLiteral;
            if (iota(0, currentLevel + 1).map!(l => ImplicationGraph.Node(-lit, l))
                    .any!(n => n in implicationGraph.nodes))
            {
                // debug stderr.writeln("GENERATE CONFLICT!");
                assignLiteral(LAMBDA, lit);
                reasons ~= 0;
                addEdge(-lit, LAMBDA, 0);
                addEdge(lit, LAMBDA, 0);

                foreach (pred; this.originalClauses[clsID].literals.array.filter!(
                        pred => pred != lit))
                    addEdge(pred, lit, clsID);
                implicationGraph.transformToConflictGraph(currentLevel);
                return SolverStatus.CONFLICT;
            }
            // stderr.writefln("!unit clauses: %s", unitClauses);
            assignLiteral(lit);
            reasons ~= clsID;
            // stderr.writefln(">unit clauses: %s", unitClauses);
            foreach (oclit; this.originalClauses[clsID].literals.array.filter!(
                    oclit => oclit != lit))
                addEdge(oclit, lit, clsID);
            toDOT(false);
        }
        if (unassignedVariables.empty)
            return SolverStatus.SAT;
        else
            return SolverStatus.OK;
    }

    alias analyzeConflictResult = Tuple!(long, "blevel", Clause, "conflict");
    analyzeConflictResult analyzeConflict()
    {
        auto level = currentLevel;

        while (true)
        {
            // if(implicationGraph.predecessors[Node(LAMBDA, currentLevel)].front.dlevel == 0)
            if (level == 0)
                return analyzeConflictResult(-1, Clause(0, []));

            auto reasonNodes = implicationGraph.get1UIPCut(currentLevel);

            long blevel;
            if (reasonNodes.array.length >= 2)
                blevel = reasonNodes.array
                    .map!(node => node.dlevel)
                    .array
                    .sort!("a > b")[1];
            else
                blevel = 0;

            debug stderr.writefln("reasonNodes: %(%s %)",
                    reasonNodes.array.map!(c => format("(%s, %s)", c[0], c[1])));

            auto learningLiterals = reasonNodes.array.map!(node => -node.literal).array;
            Clause conflict = newClause(learningLiterals);
            return analyzeConflictResult(blevel, conflict);
        }
    }

    void backtrack(size_t dlevel)
    {
        Clause[ulong] originalClauses = this.originalClauses;
        Clause[] clauses;
        foreach (i; 1 .. this.originalClauses.length + 1)
            clauses ~= Clause(this.originalClauses[i]);
        parseResult* inp = &this.inp;
        (*inp).clauses = clauses;

        auto assignedLiterals = this.assignedLiterals.dup;
        auto assignedNumPerLevel = this.assignedNumPerLevel;

        this.initialize(*inp);
        this.originalClauses = originalClauses;

        foreach (i; 0 .. assignedNumPerLevel[dlevel])
        {
            assignLiteral(assignedLiterals[i]);
            if (reasons[i] == 0)
            {
                decisionVariables ~= assignedLiterals[i].abs;
            }
            else
            {
                foreach (oclit; this.originalClauses[reasons[i]].literals.array.filter!(
                        oclit => oclit != assignedLiterals[i]))
                    addEdge(oclit, assignedLiterals[i], reasons[i]);
            }
        }
    }

    Clause newClause(T...)(T literals)
    {
        usedIDNum++;
        return Clause(usedIDNum, redBlackTree!Literal(literals));
    }

    void addConflictClause(Clause conflict)
    {
        debug stderr.writefln("conflict clause[%d]: %s", conflict.id, conflict);
        assert(conflict.id !in clauses);
        // debug stderr.writefln("originalClauses: %s", originalClauses.values);
        assert(!originalClauses.values.any!(c => c.literals == conflict.literals));
        originalClauses[conflict.id] = Clause(conflict);
        availClauses.insert(conflict.id);
    }

    void assignLiteral(T...)(T literals)
    {
        debug
        {
            stderr.writefln("assignLiteral: %s", literals);
            stderr.writeln(unassignedVariables);
            if (literals[0] != 0)
                assert(literals[0].abs in unassignedVariables);
        }
        foreach (lit; literals)
        {
            addNode(lit, this.currentLevel);
            removeClausesContaining(lit);
            removeLiteralFromClauses(-lit);
            unassignedVariables.removeKey(abs(lit));
            // stderr.writefln("availClauses: %s", availClauses);
            // availClauses.array
            //     .filter!(clauseID => clauses[clauseID].isUnitClause)
            //     .each!(clauseID => unitClauses.insert(clauseID));
        }
    }

    void addNode(Literal lit, size_t dlevel)
    {
        debug stderr.writefln("new node: %s, at level %s", lit, dlevel);
        implicationGraph.nodes.insert(ImplicationGraph.Node(lit, dlevel));
    }

    void addEdge(Literal from, Literal to, Clause.ID clauseID)
    {
        alias Node = ImplicationGraph.Node;

        debug stderr.writefln("Add edge from %s to %s", -from, to);
        Node fromNode = implicationGraph.getNode(-from), toNode = implicationGraph.getNode(to);
        if (fromNode !in implicationGraph.successors)
            implicationGraph.successors[fromNode] = redBlackTree!Node;
        implicationGraph.successors[fromNode].insert(toNode);
        if (toNode !in implicationGraph.predecessors)
            implicationGraph.predecessors[toNode] = redBlackTree!Node;
        implicationGraph.predecessors[toNode].insert(fromNode);
        implicationGraph.edges[fromNode][toNode] = clauseID;

    }

    void removeClausesContaining(Literal lit)
    {
        // stderr.writefln("these will be removed: %(%d, %)", availClauses.array.filter!(clauseID => lit in clauses[clauseID]));
        foreach (clauseID; availClauses.array.filter!(clauseID => lit in clauses[clauseID]))
        {
            availClauses.removeKey(clauseID);
            unitClauses.removeKey(clauseID);
        }
    }

    void removeLiteralFromClauses(Literal lit)
    {
        // stderr.writefln("this literal will be removed: %d", lit);
        // stderr.writeln(availClauses.array);
        foreach (clauseID; availClauses)
        {
            // stderr.writeln(clauses[clauseID]);
            if (!clauses[clauseID].isUnitClause)
                clauses[clauseID].removeLiteral(lit);
            // stderr.writeln(clauses[clauseID]);
            if (clauses[clauseID].isUnitClause)
                unitClauses.insert(clauseID);
            if (clauses[clauseID].isEmptyClause)
                unitClauses.removeKey(clauseID);
        }
    }

    private int dotCounter;
    void toDOT(bool conflict)
    {
        if (conflict)
            debug stderr.writefln("conflict exported: %d", dotCounter);
        if (!generateGraph)
            return;
        string res = "digraph cdcl {\n";
        res ~= "graph [layout = dot];\n";
        if (conflict)
            res ~= "\"0@%d\" [label = \"Λ\"];\n".format(currentLevel);
        foreach (level, variable; decisionVariables)
            res ~= format("\"%d@%d\" [shape = record, label = \"Decision variable %d at level %d\"];\n",
                    variable, level + 1, variable, level + 1);
        // foreach (variable; implicationGraph.nodes.array.filter!(n => this.originalClauses
        //         .array
        //         .filter!(c => c.id > preamble.clauses)
        //         .array
        //         .any!(c => n.literal in c)))
        //     res ~= format(
        //             "\"%d@%d\" [shape = parallelogram, label = \"%d@%d from learnt clause\", fillcolor = \"#cde0b4\"];\n",
        //             variable.literal, variable.dlevel, variable.literal, variable.dlevel);

        // stderr.writeln(implicationGraph.edges);
        foreach (from, tos; implicationGraph.edges)
        {
            foreach (to, clause; tos)
            {
                res ~= format("\"%s@%d\" -> \"%s@%d\" [label = \"%s\"];\n", from.literal, from.dlevel,
                        to.literal, to.dlevel, clause == 0 ? "" : (clause >= preamble.clauses
                            ? "L:" : "") ~ this.originalClauses[clause].toString);
            }
        }

        res ~= "}\n";
        import std.file;

        std.file.write(format("%d.dot", dotCounter), res);
        dotCounter++;
    }
}

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
