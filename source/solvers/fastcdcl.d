module solvers.fastcdcl;

import std.algorithm : filter, sort, uniq, swap;
import std.range : array;
import std.container : redBlackTree, RedBlackTree;
import std.math : abs;

alias Set(T) = RedBlackTree!T;

enum Lifted
{
    UNDEF,
    TRUE,
    FALSE
}

Lifted lbool(bool b)
{
    if (b == true)
        return Lifted.TRUE;
    else
        return Lifted.FALSE;
}

class Literal
{
    long x;
    ulong ind;
    static Literal lit_Undef;
    static Set!Literal lits;
    static ulong[long] litIndex_;
    static ulong index(Literal lit)
    {
        assert(lit in lits);
        return litIndex_[lit.x];
    }

    static this()
    {
        lit_Undef = mkLit(0, true);
        lits = redBlackTree!Literal;
    }

    static Literal mkLit(long var, bool sign)
    {
        Literal l = new Literal;
        l.x = var << 1 + cast(long) sign;
        if (!lits.insert(l))
            l.ind = index(l);
        else
            l.ind = litIndex_[l.x] = lits.length;
        return l;
    }

    auto opUnary(string op)()
    {
        if (op == "-")
        {
            Literal q;
            q.x = this.x ^ 1;
            return q;
        }
        assert(0);
    }

    bool opEquals(R)(const R other) const
    {
        return this.l == R.l;
    }

    bool sign()
    {
        return this.x & 1;
    }

    long var()
    {
        return this.x >> 1;
    }
}

class Clause
{
    bool learnt;
    Literal[] lits;

}

class FastCDCLSolver
{
    bool[] model;

    Clause[] constr;
    Clause[] learnts;

    Clause[][] watches;
    Clause[][] undos;
    Literal[] propQ;

    Lifted[] assigns;
    Literal[] trail;
    size_t[] trail_lim;
    Clause[] reason;
    long[] level;

    Lifted value(Literal x)
    {
        Lifted lif = assigns[abs(x.x)];
        if (x.x < 0)
        {
            if (lif == Lifted.TRUE)
                lif = Lifted.FALSE;
            else if (lif == Lifted.FALSE)
                lif = Lifted.TRUE;
        }
        return lif;
    }

    long decisionLevel()
    {
        return trail_lim.length;
    }

    bool addClause(Literal[] literals);
    bool simplifyDB();

    void newVar()
    {
        watches.length += 2;
        undos.length++;
        reason ~= null;
        assigns ~= Lifted.UNDEF;
        level ~= -1;
    }

    bool newClause(Literal[] ps, bool learnt, out Clause out_clause)
    {
        ps.sort();

        if (!learnt)
        {
            Literal p;
            long j;
            foreach (i; 0 .. ps.length)
            {
                if (value(ps[i]) == Lifted.TRUE || ps[i] == -p)
                    return true;
                else if (value(ps[i]) != Lifted.FALSE && ps[i] != p)
                {
                    ps[j] = p = ps[i];
                    j++;
                }
            }
        }
        ps.length = i - j;

        if (ps.length == 0)
            return false;
        else if (ps.length == 1)
            return enqueue(ps[0]);
        else
        {
            Clause c = new Clause;
            swap(ps, c.lits);
            c.learnt = learnt;

            this.watches[-c.lits[0]] ~= c;
            this.watches[-c.lits[1]] ~= c;
            out_clause = c;
            return true;
        }
    }

    bool enqueue(Literal p, Clause from = null)
    {
        if (value(p) != Lifted.UNDEF)
        {
            if (value(p) == Lifted.FALSE)
                return false;
            else
                return true;
        }
        else
        {
            assigns[p.var] = lbool(!p.sign);
            level[p.var] = decisionLevel();
            reason[p.var] = from;
            trail ~= p;
            propQ ~= p;
            return true;
        }
    }

    bool assume(Literal p)
    {
        trail_lim ~= trail.length;
        return enqueue(p);
    }

    void undoOne()
    {
        Literal p = trail.back;
        long x = p.var;
        assigns[x] = Lifted.UNDEF;
        reason[x] = null;
        level[x] = -1;
        trail.popBack();
        undos[x].clear();
    }

    void cancel()
    {
        size_t c = trail.length - trail_lim.length;
        foreach (_; 0 .. c)
            undoOne();
        trail_lim.popBack();

    }

    void cancelUntil(int level)
    {
        while (decisionLevel() > level)
            cancel();
    }
}
