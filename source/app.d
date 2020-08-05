import std.stdio;
import dimacs;
import cnf;
import solvers.dpll;
import assignment;
import std.algorithm : each;
import solvers.cdcl;
import std.file : getcwd;
import std.string : chomp;

void main(string[] args)
{
	// auto a = parseClauses();
	// auto cnf = CNF(a.clauses, a.preamble);
	// auto res = solvers.dpll.solve(cnf);
	// solverResultToString(res).writeln;
	// return;
	
	// write("testcase file: ");
	// stdout.flush();
	
	CDCLSolver solver = new CDCLSolver();
	// solver.initialize(solver.parseClauses(File("testcase/graph-ordering-5.cnf")));
	solver.initialize(parseClauses());

	if(args.length >= 2 && args[1] == "true") solver.generateGraph = true;
	// CDCLSolver solver = new CDCLSolver(parseInput());

	auto result = solver.solve();
	if(result == []) writeln("s UNSATISFIABLE");
	else {
		writeln("s SATISFIABLE");
		result.writeln;
	}
	
}
