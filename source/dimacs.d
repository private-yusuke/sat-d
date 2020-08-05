module dimacs;
import cnf;
import solvers.dpll : SolverResult, Null;
import std.stdio : readln, stdin, writeln;
import std.array : array, join;
import std.string : split;
import std.conv : to;
import std.math : abs;
import std.range : empty;
import std.stdio : stdin, File;
import std.typecons : Tuple;

public:

/*
 * "p FORMAT VARIABLES CLAUSES"
 * FORMAT must be "cnf"
 * VARIABLES and CLAUSES must be positive integers
*/
Preamble parsePreamble(File f = stdin)
{
    string[] inp;

    // comments appear in the input is ignored
    do
    {
        inp = f.readln.split;
    }
    while (inp.length < 1 || inp[0] == "c");

    if (inp[0] != "p")
    {
        error("Unknown command: %s", inp[0]);
        assert(0);
    }

    else
    {
        if (inp.length != 4)
            error("Not enough arguments");

        if (inp[1] != "cnf")
            error("Given format \"%s\" not supported", inp[1]);

        size_t variables, clauses;
        try
        {
            variables = inp[2].to!size_t, clauses = inp[3].to!size_t;
        }
        catch (Exception e)
        {
            error("Numbers in preamble couldn't be parsed");
        }
        return Preamble(variables, clauses);
    }
}
struct Preamble
{
    size_t variables;
    size_t clauses;
}
alias parseResult = Tuple!(Clause[], "clauses", Preamble, "preamble");
parseResult parseClauses(File f = stdin)
{
    Preamble preamble = parsePreamble(f);
    Clause[] clauses;
    Literal[] literals;
    Clause.ID id = 1;

    // read until EOF then ...
    long[] tokens;
    try
    {
        tokens = f.byLineCopy.array.join(' ').split.to!(long[]);
    }
    catch (Exception e)
    {
        error("Malformed input");
    }

    foreach (token; tokens)
    {
        if (token == 0)
        {
            if (clauses.length >= preamble.clauses)
                error("Too many clauses");

            Clause clause = Clause(id, literals);
            clauses ~= clause;
            literals = null;
            id++;
            continue;
        }
        if (abs(token) > preamble.variables)
            error("Given %d but variable bound is %d", abs(token), preamble.variables);

        Literal literal = token;
        literals ~= literal;
    }
    if (!literals.empty)
        error("Unexpected End of File");

    return parseResult(clauses, preamble);

}

string solverResultToString(SolverResult sr)
{
    if (sr.peek!Null)
        return "s UNSATISFIABLE";
    return format("s SATISFIABLE\n%s", sr.get!0.toDIMACSFormat());
}

private:

import std.string : format;

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
