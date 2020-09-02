module solvers.cdcl;
import cnf : CNF, Clause, Literal;
import dimacs : Preamble, parseResult;
import std.container : RedBlackTree, redBlackTree;
import std.typecons : Tuple;
import std.algorithm : each, any, sort, filter, map, countUntil, min, count;
import std.range : front, popFront, iota, enumerate, empty, retro;
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
Clause.ID nextClauseID()
{
    return ++usedIDNum;
}

struct ImplicationGraph
{
    /// dlevel とは、decision level のことをさす。
    alias Node = Tuple!(Literal, "literal", size_t, "dlevel");

    Set!Node nodes = redBlackTree!Node;
    Set!Node[Node] successors;
    Set!Node[Node] predecessors;
    Clause.ID[Node][Node] edges;

    Literal[] decisionLiterals;

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

    Node find1UIP(Node start, Node end, Node[] topSorted)
    {
        assert(start in nodes && end in nodes);
        import std.algorithm : canFind;

        // debug stderr.writefln("sorted: %(%s %)",
        //         topSorted.map!(n => format("(%s, %s)", n.literal, n.dlevel)));
        if (!topSorted.canFind(start) || !topSorted.canFind(end))
            return end;

        foreach_reverse (node; topSorted.filter!(n => n != start && n != end).array)
        {
            ImplicationGraph tmpGraph = ImplicationGraph(this);
            if (node in tmpGraph.predecessors)
                foreach (predecessor; tmpGraph.predecessors[node])
                    tmpGraph.successors[predecessor].removeKey(node);
            if (node in tmpGraph.successors)
                foreach (successor; tmpGraph.successors[node])
                    tmpGraph.predecessors[successor].removeKey(node);

            bool flag = true;
            Node[] queue = [start];
            while (!queue.empty)
            {
                // debug stderr.writefln("queue: %(%s %)", queue);
                Node n = queue.front;
                queue.popFront();
                if (n in tmpGraph.successors && end in tmpGraph.successors[n])
                    flag = false;
                if (n in tmpGraph.successors)
                    queue ~= tmpGraph.successors[n].array;
            }
            if (flag)
                return node;
        }
        // decision literal
        return start;
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
}

/// CDCL を実装した Solver
class CDCLSolver
{
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

    this()
    {
    }

    void initialize(parseResult res)
    {
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
        unassignedVariables = redBlackTree!long(iota(1,
                res.preamble.variables + 1).array.to!(long[]));
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

    Literal[] solve()
    {
        debug stderr.writefln("given clauses: %s", this.clauses.values);
        if (this.clauses.values.any!(c => c.literals.length == 0))
            return null;
        while (true)
        {
            while (true)
            {
                SolverStatus status = deduce();
                if (status == SolverStatus.CONFLICT)
                    toDOT(true);
                // debug stderr.writefln("Deduce done. nodes: %(%s, %)",
                //         implicationGraph.nodes.array.map!(p => format("(%d, %d)", p[0], p[1])));
                if (status == SolverStatus.SAT)
                    return implicationGraph.nodes.array.map!(node => node.literal).array;
                if (status == SolverStatus.CONFLICT)
                {
                    auto res = analyzeConflict();
                    if (res.blevel == -1)
                        return [];

                    //debug stderr.writefln("conflict clause: %s", res.conflict);
                    backtrack(res.blevel);
                    addConflictClause(res.conflict);
                }
                else
                    break;
            }
            decideNextBranch();
        }
    }

    void decideNextBranch()
    {
        history ~= new CDCLSolver(this);

        // debug stderr.writefln("unassigned: %s", unassignedVariables);
        Literal lit = unassignedVariables.front;
        unassignedVariables.removeKey(lit);
        // debug stderr.writefln("decision literal: %d", lit);
        currentLevel++;
        assignLiteral(lit);
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
            // stderr.writefln("unit clauses: %s", unitClauses);
            Clause.ID clsID = unitClauses.front;
            unitClauses.removeKey(clsID);
            Literal lit = clauses[clsID].unitLiteral;
            if (iota(0, currentLevel + 1).map!(l => ImplicationGraph.Node(-lit, l))
                    .any!(n => n in implicationGraph.nodes))
            {
                // debug stderr.writeln("GENERATE CONFLICT!");
                assignLiteral(LAMBDA, lit);
                addEdge(-lit, LAMBDA, 0);
                addEdge(lit, LAMBDA, 0);

                foreach (pred; this.originalClauses[clsID].literals.array.filter!(
                        pred => pred != lit))
                    addEdge(pred, lit, clsID);
                return SolverStatus.CONFLICT;
            }
            // stderr.writefln("!unit clauses: %s", unitClauses);
            assignLiteral(lit);
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

            alias Node = ImplicationGraph.Node;

            Node start = Node(implicationGraph.decisionLiterals[level - 1], level);
            Node end = Node(LAMBDA, currentLevel);
            Node[] topologicallySorted = implicationGraph.getTopologicallySorted();
            auto fuip = implicationGraph.find1UIP(start, end, topologicallySorted);
            if (fuip.literal == 0)
            {
                level--;
                continue;
            }
            debug stderr.writefln("1UIP: %s", fuip);
            // auto indexOf1UIP = countUntil(topologicallySorted, fuip);
            // auto reasonSide = redBlackTree!Node(topologicallySorted[min(indexOf1UIP,
            //             $ - implicationGraph.decisionLiterals.length) .. $].array);
            auto reachablesFrom1UIP = implicationGraph.getReachablesFrom(fuip);
            // debug stderr.writefln("reachableFrom1UIP: %s",
            //         reachablesFrom1UIP.array.map!(c => format("(%s, %s)", c[0], c[1])));
            auto reasonNodes = implicationGraph.successors[fuip].array
                .map!(node => implicationGraph.predecessors[node].array)
                .join
                .filter!(node => node !in reachablesFrom1UIP || node == fuip)
                .array
                .redBlackTree!Node;

            if (reasonNodes.array.any!(node => Node(-node.literal, node.dlevel) in reasonNodes))
                return analyzeConflictResult(-1, Clause(0, []));

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
        dlevel = min(history.length - 1, dlevel);
        debug stderr.writefln("backtrack from %d to %d", currentLevel, dlevel);
        debug stderr.writefln("history length: %d, currentLevel: %d",
                this.history.length, currentLevel);
        assert(this.history.length == currentLevel);
        CDCLSolver oldSolver = this.history[dlevel];
        this.history = this.history[0 .. dlevel];

        this.clauses = oldSolver.clauses;
        this.unassignedVariables = oldSolver.unassignedVariables;
        this.availClauses = oldSolver.availClauses;
        this.decisionVariables = oldSolver.decisionVariables;
        this.implicationGraph = oldSolver.implicationGraph;
        this.currentLevel = oldSolver.currentLevel;

        this.unitClauses.clear();
        availClauses.array
            .filter!(clauseID => clauses[clauseID].isUnitClause)
            .each!(clauseID => unitClauses.insert(clauseID));
    }

    Clause newClause(T...)(T literals)
    {
        usedIDNum++;
        return Clause(usedIDNum, redBlackTree!Literal(literals));
    }

    void addConflictClause(Clause conflict)
    {
        debug stderr.writefln("conflict clause: %s", conflict);
        assert(conflict.id !in clauses);
        // debug stderr.writefln("originalClauses: %s", originalClauses.values);
        assert(!originalClauses.values.any!(c => c.literals == conflict.literals));
        originalClauses[conflict.id] = Clause(conflict);
        availClauses.insert(conflict.id);

        foreach (dlevel; 0 .. currentLevel)
        {
            history[dlevel].clauses[conflict.id] = Clause(conflict);
            foreach (node; history[dlevel].implicationGraph.nodes)
                history[dlevel].clauses[conflict.id].removeLiteral(-node.literal);
            if (history[dlevel].clauses[conflict.id].isUnitClause)
                history[dlevel].unitClauses.insert(conflict.id);
        }

        foreach (node; implicationGraph.nodes.array.filter!(node => node.literal != 0))
            conflict.removeLiteral(-node.literal);

        clauses[conflict.id] = conflict;
        if (conflict.isUnitClause)
            unitClauses.insert(conflict.id);
        debug stderr.writefln("conflictClauseApplied: %s", conflict);
    }

    void assignLiteral(T...)(T literals)
    {
        foreach (lit; literals)
        {
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

    void addNode(Literal lit, size_t dlevel)
    {
        // debug stderr.writefln("new node: %s, at level %s", lit, dlevel);
        implicationGraph.nodes.insert(ImplicationGraph.Node(lit, dlevel));
    }

    void addEdge(Literal from, Literal to, Clause.ID clauseID)
    {
        alias Node = ImplicationGraph.Node;

        // debug stderr.writefln("Add edge from %s to %s", from, to);
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
            res ~= "0 [label = \"Λ\"];\n";
        foreach (variable; decisionVariables)
            res ~= format("%d [shape = record, label = \"Decision variable %d at level %d\"];\n",
                    variable, variable, implicationGraph.getNode(variable).dlevel);
        foreach (variable; implicationGraph.nodes.array.filter!(n => this.originalClauses
                .array
                .filter!(c => c.id > preamble.clauses)
                .array
                .any!(c => n.literal in c)))
            res ~= format("%d [shape = parallelogram, label = \"%d from learnt clause\", fillcolor = \"#cde0b4\"];\n",
                    variable.literal, variable.literal);

        // stderr.writeln(implicationGraph.edges);
        foreach (from, tos; implicationGraph.edges)
        {
            foreach (to, clause; tos)
            {
                res ~= format("%s -> %s [label = \"%s\"];\n", from.literal, to.literal, clause == 0
                        ? "" : (clause >= preamble.clauses
                            ? "L:" : "" ~ this.originalClauses[clause].toString));
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
