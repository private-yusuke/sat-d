import std.stdio;
import dimacs;
import cnf;
import solvers.dpll;
import assignment;
import std.algorithm : each;
import solvers.cdcl;
import std.file : getcwd;
import std.string : chomp, join;
import tseytin;
import std.math : abs;
import std.getopt;

int main(string[] args)
{
	// auto a = parseClauses();
	// auto cnf = CNF(a.clauses, a.preamble);
	// auto res = solvers.dpll.solve(cnf);
	// solverResultToString(res).writeln;
	// return;

	// write("testcase file: ");
	// stdout.flush();
	bool renderGraph, isTseytin, benchmark;
	string filepath;
	auto helpInfo = getopt(args, "graph|G", "output .dot files", &renderGraph,
			"benchmark|B", "run benchmark", &benchmark,
			"file", &filepath, "tseytin|tseitin|T", "enable tseytin transformation", &isTseytin);

	if (helpInfo.helpWanted)
	{
		defaultGetoptPrinter("sat-d is a small SAT solver implementation written in D.",
				helpInfo.options);
		return 0;
	}

	CDCLSolver solver = new CDCLSolver();
	CDCLSolverResult res;

	if (isTseytin)
	{
		auto formula = args[$ - 1];
		auto tseytin = tseytinTransform(formula);
		solver.initialize(tseytin.parseResult);
		res = solver.solve();
		auto literals = res.peek!(Literal[]);
		if (literals is null)
		{
			writeln("UNSAT");
			return 0;
		}
		else
		{
			bool[string] assignment;
			bool[Literal] litToTruth;
			foreach (lit; *literals)
			{
				litToTruth[abs(lit)] = lit > 0;
			}
			foreach (var, lit; tseytin.varToLiteral)
			{
				assignment[var] = litToTruth[lit];
			}
			assignment.writeln;
			return 0;
		}
	}
	auto cls = filepath ? parseClauses(File(filepath)) : parseClauses();
	solver.initialize(cls);
	solver.generateGraph = renderGraph;
	if (benchmark)
	{
		import std.datetime.stopwatch;

		StopWatch watch;
		watch.start;
		res = solver.solve();
		watch.stop;
		writefln("%s,%f", res.peek!(typeof(null)) ? "UNSAT" : "SAT",
				watch.peek.total!"usecs" / 1e6);
		return 0;
	}

	auto result = solver.solve();
	if (result.peek!(typeof(null)))
		writeln("s UNSATISFIABLE");
	else
	{
		auto assignment = result.peek!(Literal[]);
		writefln("v %(%d %)", *assignment ~ 0);
		writeln("s SATISFIABLE");
	}
	return 0;
}
