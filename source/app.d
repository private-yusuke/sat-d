import std.stdio;
import dimacs;
import solvers.dpll;
import assignment;
import std.algorithm : each;

void main()
{
	auto res = parseClauses().solve;
	if (res.peek!Assignment)
	{
		writeln("SAT");
		res.get!0.writeln;
	}
	else
		writeln("UNSAT");

}
