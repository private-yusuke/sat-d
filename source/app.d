import std.stdio;
// import dimacs;
// import solvers.dpll;
// import assignment;
// import std.algorithm : each;
import solvers.cdcl;
import std.file : getcwd;
import std.string : chomp;

void main()
{
	// auto res = parseClauses().solve;
	// solverResultToString(res).writeln;
	// write("testcase file: ");
	// stdout.flush();
	CDCLSolver solver = new CDCLSolver(parseInput());
	auto result = solver.solve();
	if(result == null) writeln("s UNSATISFIABLE");
	else writeln("s SATISFIABLE");
}
