import std.stdio;
// import dimacs;
// import solvers.dpll;
// import assignment;
// import std.algorithm : each;
import solvers.cdcl;
import std.file : getcwd;
import std.string : chomp;

void main(string[] args)
{
	// auto res = parseClauses().solve;
	// solverResultToString(res).writeln;
	// write("testcase file: ");
	// stdout.flush();
	
	CDCLSolver solver = new CDCLSolver();
	// solver.initialize(solver.parseClauses(File("testcase/graph-ordering-5.cnf")));
	solver.initialize(solver.parseClauses());

	if(args.length >= 2 && args[1] == "true") solver.generateGraph = true;
	// CDCLSolver solver = new CDCLSolver(parseInput());
	import std.datetime.stopwatch;

	StopWatch watch;
	watch.start();
	auto result = solver.solve();
	watch.stop();
	watch.peek.total!"usecs".writeln;
	// if(result == []) writeln("s UNSATISFIABLE");
	// else {
	// 	writeln("s SATISFIABLE");
	// 	result.writeln;
	// }
}
