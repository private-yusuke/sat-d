import std;

void main() {
    auto n = readln.chomp.to!int;
    auto board = readMatrix!long(n);

    auto lg = new LiteralGenerator(n);
    auto constraints = generateSudokuTableConstraint(lg, false);
    
    foreach(x; 0..n) foreach(y; 0..n)
        if(board[x][y] != 0)
            constraints ~= new Clause(lg.s(x, y, board[x][y]-1));

    writefln("p cnf %d %d", n^^3, constraints.count);
    constraints.map!(c => toDIMACS(c)).each!writeln;
}

T[][] readMatrix(T)(ulong h) {
    return iota(h).map!(v => readln.split.to!(T[])).array;    
}

alias Set(T) = RedBlackTree!T;

alias Literal = long;
alias Clause = Set!Literal;

class LiteralGenerator {
    ulong n;
    this(ulong n) {
        this.n = n;
    }

    /**
       Here we represent s_{xyz} as a literal (x*n^2 + y*n^1 + z*n^0) + 1.
    */
    Literal s(ulong x, ulong y, ulong z) {
        return x*n^^2 + y*n^^1 + z*n^^0 + 1;
    }
}

/// n: width/height of the table
Clause[] generateSudokuTableConstraint(LiteralGenerator lg, bool extended = false) {
    /// assert n is a square number
    assert(lg.n.to!real.sqrt.round.pow(2) == lg.n);
    auto m = lg.n.to!real.sqrt.round.to!ulong, n = lg.n;

    Clause[] res;
    auto s = &(new LiteralGenerator(n).s);
    
    // ===== minimal encoding =====
    /// 1st constraint
    foreach(x; 0..n) foreach(y; 0..n)
        res ~= new Clause(iota(n).map!(z => s(x, y, z)).array);
    
    /// 2nd constraint
    foreach(y; 0..n) foreach(z; 0..n) foreach(x; 0..n-1) foreach(i; x+1..n)
        res ~= new Clause(-s(x, y, z), -s(i, y, z));

    /// 3rd constraint
    foreach(x; 0..n) foreach(z; 0..n) foreach(y; 0..n-1) foreach(i; y+1..n)
        res ~= new Clause(-s(x, y, z), -s(x, i, z));

    /// constraint 4-1
    foreach(z; 0..n) foreach(i; 0..m) foreach(j; 0..m) foreach(x; 0..m) foreach(y; 0..m) foreach(k; y+1..m)
        res ~= new Clause(-s(m*i+x, m*j+y, z), -s(m*i+x, m*j+k, z));

    /// constraint 4-2
    foreach(z; 0..n) foreach(i; 0..m) foreach(j; 0..m) foreach(x; 0..m) foreach(y; 0..m) foreach(k; x+1..m) foreach(l; 0..m)
        res ~= new Clause(-s(m*i+x, m*j+y, z), -s(m*i+k, m*j+l, z));

    // ===== extended encoding =====

    if(!extended) return res;

    /// 1st constraint
    foreach(x; 0..n) foreach(y; 0..n) foreach(z; 0..n-1) foreach(i; z+1..n)
        res ~= new Clause(-s(x, y, z), -s(x, y, i));
    
    /// 2nd constraint
    foreach(y; 0..n) foreach(z; 0..n)
        res ~= new Clause(iota(n).map!(x => s(x, y, z)));
    
    /// 3rd constraint
    foreach(x; 0..n) foreach(z; 0..n)
        res ~= new Clause(iota(n).map!(y => s(x, y, z)));

    /// 4th constraint
    foreach(i; 0..m) foreach(j; 0..m) foreach(x; 0..m) foreach(y; 0..m)
        res ~= new Clause(iota(n).map!(z => s(m*i+x, m*j+y, z)));
    
    return res;
}

string toDIMACS(Clause c) {
    return format("%(%d %) 0", c.array);
}