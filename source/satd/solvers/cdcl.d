module satd.solvers.cdcl;
import satd.cnf : CNF, Clause, Literal, Set;
import satd.dimacs : Preamble, parseResult;
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

    /// 与えられた implication graph を deep copy するためのコンストラクタ
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

    /// 与えられた decision level 以上の頂点やそれに繋がっている辺を削除します。
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

    /// 与えられたリテラルを持つ頂点を取得します。
    Node getNode(Literal lit)
    {
        auto tmp = nodes.array.filter!(n => n.literal == lit);
        assert(tmp.count == 1);
        return tmp.front;
    }

    /// 1UIP cut を取得します。
    Set!Node get1UIPCut()
    {
        Set!Node res = redBlackTree!Node;

        Set!Node visited = redBlackTree!Node;

        const ulong dlevel = decisionLiterals.length;

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
            // debug stderr.writefln("nextQueue: %s", nextQueue);
        }

        return res;
    }

    /++
     + implication graph を conflict graph の制約を満たすように変形します。
     + この関数呼出後のグラフは以下の制約のすべてを満たしていることが保証されています。
     +
     + 1. Λ とただ一つの conflict variable を含んでいる。
     + 2. 任意の頂点について、Λ への道が存在する。
     + 3. Λ を除くすべての頂点 l について、それが decision literal であるか、または
     +    (l_1 or l_2 or ... or l_k or l) が既知の節として存在して、かつ
     +    not l_1, not l_2, ..., not l_k が predecessor としてグラフに存在する。
     +/
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

/// CDCL を実装したソルバー
class CDCLSolver
{
    Clause[Clause.ID] clauses;
    Set!(long) unassignedVariables = redBlackTree!long;
    /// まだ充足されていない節の ID の集合
    auto availClauses = redBlackTree!("a > b", Clause.ID);
    ImplicationGraph implicationGraph;
    /// implication graph 上の頂点の decision level の最大値
    size_t currentLevel;

    auto unitClauses = redBlackTree!("a > b", Clause.ID);
    Set!(Clause.ID)[Literal] clausesContainingLiteral;
    /// CNF の単純化が適用されていない形の節
    Clause[Clause.ID] originalClauses;
    Literal[] decisionVariables;
    bool generateGraph = false;
    bool generateAnotherGraph = false;
    Preamble preamble;

    /// ソルバーの状態が各 decision level に対応して保持されている配列
    CDCLSolver[] history;

    bool restart = false;
    long restartThreshold = 100;
    double restartMult = 1.5;
    ulong conflictCount;

    private Clause.ID usedIDNum;

    Clause.ID nextClauseID()
    {
        return ++usedIDNum;
    }

    this()
    {
        implicationGraph.initalize();
    }

    /// 読み込んだ CNF の情報を元にソルバーを初期化します。
    void initialize(parseResult res)
    {
        auto clauses = res.clauses;
        foreach (clause; clauses)
        {
            this.clauses[clause.id] = clause;
            if (clause.isUnitClause)
                unitClauses.insert(clause.id);
            availClauses.insert(clause.id);

            foreach (literal; clause.literals.array)
            {
                if (literal !in clausesContainingLiteral)
                    clausesContainingLiteral[literal] = redBlackTree!(Clause.ID);
                clausesContainingLiteral[literal].insert(clause.id);
            }

            // debug stderr.writefln("%d: %s", clause.id, clause);
        }
        clausesContainingLiteral[0] = redBlackTree!(Clause.ID);

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

    /// 問題を与えて初期化したソルバーで実行すると、その問題を解いて結果を返します。
    CDCLSolverResult solve()
    {
        // debug stderr.writefln("given clauses: %s", this.clauses.values);

        if (this.clauses.values.any!(c => c.literals.length == 0))
            return CDCLSolverResult(null);
        if (this.preamble.variables == 0 && this.preamble.clauses == 0)
            return CDCLSolverResult(cast(Literal[])[]);
        while (true)
        {
            while (true)
            {
                immutable SolverStatus status = deduce();
                // debug stderr.writefln("Deduce done. nodes: %(%s, %)",
                // implicationGraph.nodes.array.map!(p => format("(%d, %d)", p[0], p[1])));
                if (status == SolverStatus.SAT)
                    return CDCLSolverResult(implicationGraph.nodes.array.map!(node => node.literal)
                            .array);
                if (status == SolverStatus.CONFLICT)
                {
                    toDOT(true);
                    auto res = analyzeConflict();
                    if (res.blevel == -1)
                        return CDCLSolverResult(null);

                    backtrack(res.blevel);
                    addConflictClause(res.conflict);
                    conflictCount++;

                    // リスタートが有効であり、conflict の回数が閾値に達していたならば、リスタートを実施します。
                    if (restart && conflictCount == restartThreshold)
                    {
                        writefln("c restart. conflicted %d times", conflictCount);
                        backtrack(0);
                        restartThreshold = cast(long)(cast(double) restartThreshold * restartMult);
                    }
                }
                else
                    break;
            }
            decideNextBranch();
        }
    }

    /// 真偽値が未割り当ての変数を1つ選んで真を割り当てます。
    void decideNextBranch()
    {
        // 現在のソルバーの状態を保存します。
        history ~= new CDCLSolver(this);

        Literal lit = unassignedVariables.front;
        // debug stderr.writefln("decision literal: %d", lit);
        currentLevel++;
        assignLiteral(lit);
        decisionVariables ~= lit;
        implicationGraph.decisionLiterals ~= lit;
    }

    /++
     + 単位伝播を繰り返します。
     + 途中で矛盾が生じたら CONFLICT を返します。
     + 矛盾なくすべての変数に真偽値を割り当てられたら SAT を返します。
     + それ以外の場合には OK を返します。
     +/
    SolverStatus deduce()
    {
        while (!unitClauses.empty)
        {
            // debug stderr.writefln("unitClauses: %s", unitClauses);

            Clause.ID clsID = unitClauses.front;
            unitClauses.removeKey(clsID);
            Literal lit = clauses[clsID].unitLiteral;
            if (iota(0, currentLevel + 1).map!(l => ImplicationGraph.Node(-lit, l))
                    .any!(n => n in implicationGraph.nodes))
            {
                assignLiteral(LAMBDA, lit);
                addEdge(-lit, LAMBDA, 0);
                addEdge(lit, LAMBDA, 0);

                foreach (pred; this.originalClauses[clsID].literals.array.filter!(
                        pred => pred != lit))
                    addEdge(pred, lit, clsID);
                implicationGraph.transformToConflictGraph(currentLevel);
                return SolverStatus.CONFLICT;
            }
            assignLiteral(lit);
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
    /++
     + 矛盾を分析します。
     + Returns: バックトラック先のレベルと学習節
     +/
    analyzeConflictResult analyzeConflict()
    {
        while (true)
        {
            if (currentLevel == 0)
                return analyzeConflictResult(-1, Clause(0, []));

            auto reasonNodes = implicationGraph.get1UIPCut();

            long blevel;
            if (reasonNodes.array.length >= 2)
                blevel = reasonNodes.array
                    .map!(node => node.dlevel)
                    .array
                    .sort!("a > b")[1];
            else
                blevel = 0;

            // debug stderr.writefln("reasonNodes: %(%s %)",
            // reasonNodes.array.map!(c => format("(%s, %s)", c[0], c[1])));

            auto learningLiterals = reasonNodes.array.map!(node => -node.literal).array;
            Clause conflict = newClause(learningLiterals);
            return analyzeConflictResult(blevel, conflict);
        }
    }

    /++
     + 与えられたレベルまでバックトラックします。
     + 具体的には、ソルバーの状態を与えられたレベルのときのソルバーの状態まで復元します。
     +/
    void backtrack(size_t dlevel)
    {
        dlevel = min(history.length - 1, dlevel);
        // debug stderr.writefln("backtrack from %d to %d", currentLevel, dlevel);
        // debug stderr.writefln("history length: %d, currentLevel: %d",
        // this.history.length, currentLevel);
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
        // debug stderr.writefln("availClauses: %(%s, %)", availClauses.array.map!(id => clauses[id]));
    }

    /++
     + ソルバーの状態を、真偽値割り当てがなされていない初期状態にリセットします。
     + 初期化時以外で追加された制約はそのまま追加された状態を維持します。
     +/
    void reset()
    {
        backtrack(0);
    }

    /// 与えられたリテラルを含んだ新しい節を作成します。
    Clause newClause(T...)(T literals)
    {
        return Clause(redBlackTree!Literal(literals));
    }

    /// 与えられたリテラルの集合に対応する新しい節を作成します。
    Clause newClause(T)(Set!T literals) if (isIntegral!T)
    {
        return Clause(literals);
    }

    /// 与えられた節をソルバーの制約として追加します。
    void addClause(Clause clause)
    {
        usedIDNum++;
        clause.id = usedIDNum;

        assert(clause.id !in clauses);
        originalClauses[clause.id] = Clause(clause);
        availClauses.insert(clause.id);

        foreach (dlevel; 0 .. currentLevel)
        {
            history[dlevel].clauses[clause.id] = Clause(clause);
            foreach (node; history[dlevel].implicationGraph.nodes)
                history[dlevel].clauses[clause.id].removeLiteral(-node.literal);
            if (history[dlevel].clauses[clause.id].isUnitClause)
                history[dlevel].unitClauses.insert(clause.id);
            history[dlevel].availClauses.insert(clause.id);
        }
        foreach (literal; clause.literals)
            clausesContainingLiteral[literal].insert(clause.id);

        foreach (node; implicationGraph.nodes.array.filter!(node => node.literal != 0))
            clause.removeLiteral(-node.literal);

        clauses[clause.id] = clause;
        if (clause.isUnitClause)
            unitClauses.insert(clause.id);
    }

    /// 与えられた節を学習節として追加します。
    void addConflictClause(Clause conflict)
    {
        // debug stderr.writefln("conflict clause: %s", conflict);
        assert(!originalClauses.values.any!(c => c.literals == conflict.literals));
        addClause(conflict);
        // debug stderr.writefln("conflictClauseApplied: %s", conflict);
    }

    /// 与えられたリテラルが真になるように変数への真偽値割り当てを行います。
    void assignLiteral(T...)(T literals)
    {
        debug
        {
            // debug stderr.writefln("assignLiteral: %s", literals);
            // debug stderr.writeln(unassignedVariables);
            if (literals[0] != 0)
                assert(literals[0].abs in unassignedVariables);
        }
        foreach (lit; literals)
        {
            addNode(lit, this.currentLevel);
            removeClausesContaining(lit);
            removeLiteralFromClauses(-lit);
            unassignedVariables.removeKey(abs(lit));
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

        // debug stderr.writefln("Add edge from %s to %s", -from, to);
        Node fromNode = implicationGraph.getNode(-from), toNode = implicationGraph.getNode(to);
        if (fromNode !in implicationGraph.successors)
            implicationGraph.successors[fromNode] = redBlackTree!Node;
        implicationGraph.successors[fromNode].insert(toNode);
        if (toNode !in implicationGraph.predecessors)
            implicationGraph.predecessors[toNode] = redBlackTree!Node;
        implicationGraph.predecessors[toNode].insert(fromNode);
        implicationGraph.edges[fromNode][toNode] = clauseID;

    }

    /// 与えられたリテラルを含む節を削除します。
    void removeClausesContaining(Literal lit)
    {
        if (lit !in clausesContainingLiteral)
            return;
        foreach (clauseID; clausesContainingLiteral[lit].array.filter!(cid => cid in availClauses))
        {
            availClauses.removeKey(clauseID);
            unitClauses.removeKey(clauseID);
        }
    }

    /// 与えられたリテラルをそれぞれの節の中から削除します。
    void removeLiteralFromClauses(Literal lit)
    {
        if (lit !in clausesContainingLiteral)
            return;
        foreach (clauseID; clausesContainingLiteral[lit].array.filter!(cid => cid in availClauses))
        {
            if (!clauses[clauseID].isUnitClause)
                clauses[clauseID].removeLiteral(lit);
            if (clauses[clauseID].isUnitClause)
                unitClauses.insert(clauseID);
            if (clauses[clauseID].isEmptyClause)
                unitClauses.removeKey(clauseID);
        }
    }

    private int dotCounter;
    /++
     + implication graph の状態を DOT 言語で出力します。
     + ファイル名は 1.dot, 2.dot, … のように続きます。
     +/
    void toDOT(bool conflict)
    {
        // if (conflict)
        // debug stderr.writefln("conflict exported: %d", dotCounter);
        if (!generateGraph && !generateAnotherGraph)
            return;
        if (implicationGraph.edges.length == 0)
            return;

        string dotSource;
        if (generateGraph)
            dotSource = generateGraph1(conflict);
        else
            dotSource = generateGraph2(conflict);

        import std.file : write;

        write(format("%d.dot", dotCounter), dotSource);
        dotCounter++;
    }

    /// implication graph の定義に即した形のグラフを表す DOT 言語のソースを返します。
    string generateGraph1(bool conflict)
    {
        string res = "digraph cdcl {\nnode[style=filled, fillcolor=white];\n";
        res ~= "graph [layout = dot];\n";
        if (conflict)
            res ~= "\"0@%d\" [label = \"Λ\"];\n".format(currentLevel);
        foreach (level, variable; decisionVariables)
            res ~= format("\"%d@%d\" [shape = record, label = \"%d@%d\"];\n",
                    variable, level + 1, variable, level + 1);

        foreach (from, tos; implicationGraph.edges)
        {
            foreach (to, clause; tos)
            {
                res ~= format("\"%s@%d\" -> \"%s@%d\" [label = \"%s\"];\n", from.literal, from.dlevel,
                        to.literal, to.dlevel, clause == 0 ? "" : (clause > preamble.clauses
                            ? "L:" : "") ~ this.originalClauses[clause].toString);
            }
        }

        res ~= "}\n";
        return res;
    }

    /// implication graph を元に、単位伝播で用いられた節も頂点にしたグラフの DOT 言語のソースを返します。
    string generateGraph2(bool conflict)
    {
        string label(string content, string color)
        {
            return "<font color=\"" ~ color ~ "\">" ~ content ~ "</font>";
        }

        string generateClauseLabel(Clause.ID cl, Literal implicated)
        {
            if (cl == 0)
                return "conflict";

            auto literals = this.originalClauses[cl].literals.array;
            Literal[] l, r;
            auto tmp = literals.split(implicated);
            l = tmp[0], r = tmp[1];
            string ls = l.empty ? "" : format("%(%d ∨%) ∨ ", l);
            string rs = r.empty ? "" : format(" ∨ %(%d ∨%)", r);
            string res = "(%s%s%s)".format(ls, label(implicated.to!string, "black"), rs);
            if (cl > preamble.clauses)
                return "L:" ~ res;
            else
                return res;
        }

        string res = "digraph cdcl {\nnode[style=filled, fillcolor=white];\n";
        res ~= "graph [layout = dot, bgcolor=\"#eaeaea\"];\n";
        if (conflict)
            res ~= "\"0@%d\" [label = \"Λ\"];\n".format(currentLevel);
        foreach (level, variable; decisionVariables)
            res ~= format("\"%d@%d\" [shape = record, label = \"%d@%d\"];\n",
                    variable, level + 1, variable, level + 1);

        alias T = Tuple!(Clause.ID, "clauseID", Literal, "implicated");
        T[] clausesAndImplicateds;

        foreach (_, tos; implicationGraph.edges)
            foreach (to, clause; tos)
                clausesAndImplicateds ~= T(clause, to.literal);

        foreach (p; clausesAndImplicateds)
            if (p.clauseID != 0)
                res ~= format("\"cls%d\" [shape = invtrapezium, fontcolor=gray60, label=<%s>];\n",
                        p.clauseID, generateClauseLabel(p.clauseID, p.implicated));

        auto clauseRendered = redBlackTree!(Clause.ID);

        foreach (from, tos; implicationGraph.edges)
        {
            foreach (to, clause; tos)
            {
                if (clause == 0)
                    res ~= format("\"%s@%d\" -> \"%s@%d\"\n", from.literal,
                            from.dlevel, to.literal, to.dlevel);
                else
                {
                    res ~= format("\"%d@%d\" -> \"cls%d\"\n", from.literal, from.dlevel, clause);
                    if (clauseRendered.insert(clause))
                        res ~= format("\"cls%d\" -> \"%d@%d\"\n", clause, to.literal, to.dlevel);
                }
            }
        }

        res ~= "}\n";
        return res;
    }
}
