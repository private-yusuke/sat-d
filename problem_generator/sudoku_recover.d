import std;

int main(string[] args) {
    auto lits = readln.split[1..$].to!(long[]);
    auto maxl = lits.map!(v => v.abs).reduce!max;
    auto n = maxl.to!real.cbrt.to!ulong;

    auto board = new long[][](n, n);

    foreach(lit; lits) {
        if(lit > 0) {
            lit--;
            auto x = lit / (n ^^ 2), y = (lit / (n ^^ 1)) % n, z = lit % n;
            board[x][y] = z+1;
            // writefln("%d*%d + %d*%d + %d = %d", x, n^^2, y, n, z, lit);
        }
    }
    
    board.each!(col => writefln("%(%d %)", col));

    return 0;
}