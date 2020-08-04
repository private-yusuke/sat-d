module dimacs;
import cnf;
import solvers.dpll : SolverResult, Null;
import std.stdio : readln, stdin, writeln;
import std.array : array, join;
import std.string : split;
import std.conv : to;
import std.math : abs;
import std.range : empty;

public:

/*
 * "p FORMAT VARIABLES CLAUSES"
 * FORMAT must be "cnf"
 * VARIABLES and CLAUSES must be positive integers
*/
struct Preamble
{
    size_t variables;
    size_t clauses;
}

// TODO: currently loading only from stdin; perhaps from file?
Preamble parsePreamble()
{
    string[] inp;

    // comments appear in the input is ignored
    do
    {
        inp = readln.split;
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

// TODO: same parsePreamble
CNF parseClauses()
{
    Preamble preamble = parsePreamble();
    Clause[] clauses;
    Literal[] literals;

    // read until EOF then ...
    long[] tokens;
    try
    {
        tokens = stdin.byLineCopy.array.join(' ').split.to!(long[]);
    }
    catch (Exception e)
    {
        error("Malformed input");
    }

    Clause.ID clauseID;
    foreach (token; tokens)
    {
        if (token == 0)
        {
            if (clauses.length >= preamble.clauses)
                error("Too many clauses");

            Clause clause = Clause(clauseID, literals);
            clauses ~= clause;
            literals = null;
            clauseID++;
            continue;
        }
        if (abs(token) > preamble.variables)
            error("Given %d but variable bound is %d", abs(token), preamble.variables);

        Literal literal = token;
        literals ~= literal;
    }
    if (!literals.empty)
        error("Unexpected End of File");

    return CNF(clauses, preamble);
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
