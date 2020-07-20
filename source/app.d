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
	write("testcase file: ");
	stdout.flush();
	new CDCLSolver(parseInput(File(getcwd() ~ "/" ~ readln.chomp)));
}
