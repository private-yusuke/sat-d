import std.stdio;
import dimacs;
import solvers.dpll;
import assignment;
import std.algorithm : each;

void main()
{
	auto res = parseClauses().solve;
	solverResultToString(res).writeln;
}
