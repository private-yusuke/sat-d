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

int main(string[] args)
{
	// auto a = parseClauses();
	// auto cnf = CNF(a.clauses, a.preamble);
	// auto res = solvers.dpll.solve(cnf);
	// solverResultToString(res).writeln;
	// return;

	// write("testcase file: ");
	// stdout.flush();

	CDCLSolver solver = new CDCLSolver();
	CDCLSolverResult res;
	// solver.initialize(solver.parseClauses(File("testcase/graph-ordering-5.cnf")));

	if (args.length >= 2 && args[1] == "tseytin")
	{
		if (args.length == 2)
		{
			stderr.writeln("Usage: sat-d tseytin <formula>");
			return 1;
		}
		auto formula = args[2 .. $].join(' ');
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
	if (args.length >= 2 && args[1] == "true")
		solver.generateGraph = true;
	if (args.length >= 2 && args[1] == "benchmark")
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
	solver.initialize(parseClauses());
	// CDCLSolver solver = new CDCLSolver(parseInput());

	auto result = solver.solve();
	if (result.peek!(typeof(null)))
		writeln("s UNSATISFIABLE");
	else
	{
		writeln("s SATISFIABLE");
		result.writeln;
	}
	return 0;
}
