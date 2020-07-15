module solvers.cdcl;

import cnf : IDType, Literal, Clause, CNF;
import assignment, dimacs;
import std.variant : Algebraic;
import std.typecons : Tuple;
import std.algorithm : map, canFind;
import std.array;
import std.range:empty;

debug import std.stdio;

alias Null = typeof(null);
alias SolverResult = Algebraic!(Assignment, Null);

alias Option(T) = Algebraic!(T, Null);
alias unitPropagateResult = Tuple!(Clause[IDType], "clauses", Assignment, "assignment");

alias Decimal = double;

class CDCLSolver {
    public:

    Clause[] clauses;
    size_t variableNum, clauseNum;

    this(CNF cnf, Preamble preamble) {
        this.clauses = cnf.allClauses.values;
        this.variableNum = preamble.variables;
        this.clauseNum = preamble.clauses;
    }

    SolverResult solve() {
        return SolverResult(null);
    }

    private:

    Decimal[IDType] VSIDSCounter;
     
    /// 各 literal が現れる回数を集めた counter を生成する
    auto initVSIDS() {
        Decimal[IDType] counter;
        foreach(x; -this.variableNum..this.variableNum+1) {
            counter[x] = 0;
        }
        foreach(clause; this.clauses) {
            foreach(literal; clause.literals) {
                counter[literal.id]++;
            }
        }
        return counter;
    }

    /++ conflict clause 内にある literal の出現回数を counter に increment する。
        すると、この literal が選ばれる確率が増える。
    +/
    auto conflictVSIDS(Decimal[IDType] counter, Clause conflictClause) {
        foreach(literal; conflictClause.literals) {
            counter[literal.id]++;
        }
        return counter;
    }

    auto decayVSIDS(Decimal[IDType] counter) {
        foreach(i; -this.variableNum..this.variableNum+1) {
            counter[i] = counter[i] * 0.95;
        }
    }

    Literal decideVSIDS(Decimal[IDType] counter, Literal[] usedVariables) {
        Decimal max;
        Literal variable;
        foreach(IDType i; -this.variableNum..this.variableNum+1) {
            Literal lit = Literal(i);
            if(counter[i] >= max && !usedVariables.canFind(lit) && !usedVariables.canFind(-lit)) {
                max = counter[i];
                variable = lit;
            }
        }
        return variable;
    }

    Clause[IDType] BCP(Clause[IDType] clauses, Literal literal) {
        Clause[IDType] newClauses = clauses.dup;
        foreach_reverse(k, x; newClauses) {
            if(literal in x.literals) {
                newClauses.remove(k);
            }
            if(-literal in x.literals) {
                x.removeLiteral(-literal);
                if (x.literals.empty) return null;
            }
        }
        return newClauses;
    }

    Option!unitPropagateResult unitPropagate(Clause[IDType] clauses) {
        Assignment assignment;
        bool flag = true;
        while(flag) {
            flag = false;
            foreach(k, x; clauses) {
                if(x.isUnit) {
                    clauses = BCP(clauses, x.unitLiteral);
                    assignment.assign(x.unitLiteral);
                    flag = true;
                }
                /// propagate 後に UNSAT だったら
                if(clauses == null) {
                    return Option!unitPropagateResult(null);
                }
                if(clauses.empty) {
                    return Option!unitPropagateResult(unitPropagateResult(clauses, assignment));
                }
            }
        }
        return Option!unitPropagateResult(unitPropagateResult(clauses, assignment));
    }

    alias createWatchListResult = Tuple!(IDType[][Literal], "watchedLiteralFromLiteralToClause", Literal[][IDType], "watchedLiteralFromClauseToLiteral");
    createWatchListResult createWatchList(Clause[IDType] clauses, Literal[] usedLiterals) {
        IDType[][Literal] watchedLiteralFromLiteralToClause;
        Literal[][IDType] watchedLiteralFromClauseToLiteral;
        foreach(i; -this.variableNum..this.variableNum+1) {
            watchedLiteralFromLiteralToClause[Literal()] = [];
        }
        foreach(i; 0..clauses.length) {
            Literal[] watchedLiterals;
            bool first = true;
            Literal A, B;
            foreach(j; clauses[i].literals) {
                if(usedLiterals.canFind(j)) {
                    if(first) {
                        A = j;
                        first = false;
                        continue;
                    } else { /// B is the second watched literal of the clause
                        B = j;
                        break;
                    }
                }
                watchedLiterals = [A, B];
                watchedLiteralFromClauseToLiteral[i] ~= watchedLiterals;
                watchedLiteralFromLiteralToClause[A] ~= i;
                watchedLiteralFromLiteralToClause[B] ~= i;
            }
        }
        return createWatchListResult(watchedLiteralFromLiteralToClause, watchedLiteralFromClauseToLiteral);
    }

    alias twoLiteralWatchPropagateResult = Tuple!(Clause[IDType],"affectedClause", IDType[IDType][], "watchedLiteralFromLiteralToClause");

    twoLiteralWatchPropagateResult twoLiteralWatchPropagate(Clause[IDType] clauses,
        IDType[][IDType] watchedLiteralFromLiteralToClause, IDType[][IDType] watchedLiteralFromClauseToLiteral,
        Literal[] usedLiterals, Literal literal) {

        Literal[] propList = [literal];
        while(!propList.empty) {
            literal = propList.front;
            propList.popFront();
            foreach_reverse(affectedClauseNum; watchedLiteralFromLiteralToClause[-literal.id]) {
                Clause affectedClause = Clause(clauses[affectedClauseNum]);
                Literal A = watchedLiteralFromClauseToLiteral[affectedClauseNum][0];
                Literal B = watchedLiteralFromClauseToLiteral[affectedClauseNum][1];
                Literal Aprev = A, Bprev = B;

            }
        }
        assert(0);
    }

    alias StatusResult = Tuple!(string, "status", Literal[], "usedLiterals", Literal, "A", Literal, "B", Literal, "unit");

    StatusResult checkStatus(Clause clause, Literal[] usedLiterals, Literal A, Literal B) {
        Literal unit = Literal(0);
        if(usedLiterals.canFind(A) || usedLiterals.canFind(B)) {
            return StatusResult("Satisfied", usedLiterals, A, B, unit);
        }
        Literal[] symbols;
        foreach(lit; clause.literals) {
            if(!usedLiterals.canFind(-lit)) {
                symbols ~= lit;
            }
            if(usedLiterals.canFind(lit)) {
                if(!usedLiterals.canFind(-lit)) {
                    return StatusResult("Satisfied", usedLiterals, A, lit, unit);
                }
                return StatusResult("Satisfied", usedLiterals, lit, B, unit);
            }
        }
        if(symbols.length == 1) {
            return StatusResult("Unit", usedLiterals, A, B, symbols[0]);
        }
        if(symbols.length == 0) {
            return StatusResult("Unsatisfied", usedLiterals, A, B, unit);
        } else {
            return StatusResult("Unresolved", usedLiterals, symbols[0], symbols[1], unit);
        }
    }

    Literal[] analyzeConflict(Literal[] decidePos) {
        return decidePos.map!(v => -v).array;
    }

    void assign(Literal literal, ref Literal[] usedLiterals, ref Literal[] decidePos) {
        
    }
}