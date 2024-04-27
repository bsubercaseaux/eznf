class Implication:
    def __init__(self, implicant, implicate):
        sem_implicant = SemCNF(implicant)
        sem_implicate = SemCNF(implicate)
        self._semcnf = Or(Not(sem_implicant), sem_implicate)

    def to_clauses(self) -> list[list[int]]:
        return self._semcnf.to_clauses()


class SemClause:
    def __init__(self, lits):
        self.literals = lits

    def to_clause(self) -> list[int]:
        return self.literals


class SemCNF:
    def __init__(self, base):
        if isinstance(base, SemClause):
            self.clauses = [base]
        elif isinstance(base, list):
            self.clauses = base
        elif isinstance(base, SemCNF):
            self.clauses = base.clauses
        elif isinstance(base, int):
            self.clauses = [SemClause([base])]
        else:
            raise TypeError(
                "SemCNF can only be initialized with a SemClause, a list of SemClauses, a SemCNF or an int"
            )

    def to_clauses(self) -> list[list[int]]:
        return [clause.to_clause() for clause in self.clauses]


def Or(left, right):
    left = SemCNF(left)
    right = SemCNF(right)

    # so far only implemented for two clauses
    assert len(left.clauses) == 1
    assert len(right.clauses) == 1
    return SemCNF([SemClause(left.clauses[0].literals + right.clauses[0].literals)])


def And(left, right) -> SemCNF:
    left = SemCNF(left)
    right = SemCNF(right)

    return SemCNF(left.clauses + right.clauses)


def Not(param):
    # so far only implemented for collection of unit clauses
    semcnf = SemCNF(param)
    ans = []
    for clause in semcnf.clauses:
        assert len(clause.literals) == 1
        ans.append(-clause.literals[0])
    return SemCNF([SemClause(ans)])
