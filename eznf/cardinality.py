import itertools
from typing import List
from eznf import utils


class CExactly:
    def __init__(self, k: int, variables, modeler) -> None:
        self.k = k
        self.variables = variables
        self.modeler = modeler

    def to_clauses(self) -> List[List[int]]:
        clauses = []
        if len(self.variables) < self.k:
            return [[]]
        if len(self.variables) == self.k:
            return [[n] for n in utils.to_numerical(self.variables, self.modeler)]
        if self.k == 1:
            at_least = utils.to_numerical(self.variables, self.modeler)
            clauses.append(at_least)
            clauses += CAtMostOne(self.variables, self.modeler).to_clauses()
            return clauses
        
        hsh = hash(tuple(self.variables))
        vnames = f"__auxcount_{hsh}"
        cvars = CountingVars(
            vnames, utils.to_numerical(self.variables, self.modeler), self.modeler
        )
        return cvars.added_clauses + [[self.modeler.v(f"{vnames}_{self.k}")]]


class CAtMostOne:
    def __init__(self, variables, modeler) -> None:
        self.variables = utils.to_numerical(variables, modeler)
        self.modeler = modeler

    def to_clauses_naive(self) -> List[List[int]]:
        clauses = []
        for v1, v2 in itertools.combinations(self.variables, 2):
            clauses.append([-v1, -v2])
        return clauses

    def to_clauses(self) -> List[List[int]]:
        if len(self.variables) <= 4:
            return self.to_clauses_naive()
        else:
            new_aux_var = self.modeler.add_var(
                f"__aux_atmostone_{self.modeler.n_vars()}",
                "auxiliary variable for at most one constraint",
            )
            head = self.variables[:3] + [new_aux_var]
            tail = self.variables[3:] + [-new_aux_var]
            return (
                CAtMostOne(head, self.modeler).to_clauses()
                + CAtMostOne(tail, self.modeler).to_clauses()
            )

    def to_clauses_o(self) -> List[List[int]]:
        if len(self.variables) <= 4:
            return self.to_clauses_naive()
    
        new_aux_var = self.modeler.add_var(
            f"__aux_atmostone_{self.modeler.n_vars()}",
            "auxiliary variable for at most one constraint",
        )
        head = self.variables[:3] + [new_aux_var]
        tail = [-new_aux_var] + self.variables[3:]
        return (
            CAtMostOne(head, self.modeler).to_clauses_o()
            + CAtMostOne(tail, self.modeler).to_clauses_o()
        )

    def to_clauses_2(self) -> List[List[int]]:
        if len(self.variables) <= 4:
            return self.to_clauses_naive()
        
        new_aux_var = self.modeler.add_var(
            f"__aux_atmostone_{self.modeler.n_vars()}",
            "auxiliary variable for at most one constraint",
        )
        half = len(self.variables) // 2
        head = self.variables[:half] + [new_aux_var]
        tail = self.variables[half:] + [-new_aux_var]
        return (
            CAtMostOne(head, self.modeler).to_clauses_2()
            + CAtMostOne(tail, self.modeler).to_clauses_2()
        )


class CAtMost:
    def __init__(self, k: int, variables, modeler) -> None:
        self.k = k
        self.variables = utils.to_numerical(variables, modeler)
        self.modeler = modeler

    def to_clauses(self) -> List[List[int]]:
        if self.k == 1:
            return CAtMostOne(self.variables, self.modeler).to_clauses()
        else:
            hsh = hash(tuple(self.variables))
            vnames = f"__auxcount_{hsh}"
            cvars = CountingVars(
                vnames, self.variables, self.modeler, upper_bound=self.k + 1
            )
            return cvars.added_clauses + [[-self.modeler.v(f"{vnames}_{self.k+1}")]]


class GConstraint:
    def __init__(self, bound, guard, variables, modeler) -> None:
        self.bound = bound
        self.guard = guard
        self.variables = variables
        self.modeler = modeler

    def to_str(self) -> str:
        lits = [self.bound] + utils.to_numerical([self.guard], self.modeler) + utils.to_numerical(self.variables, self.modeler)
        return "g " + " ".join(map(str, lits))


class KConstraint:
    def __init__(self, bound, variables, modeler) -> None:
        self.bound = bound
        self.modeler = modeler
        self.variables = variables

    def to_str(self) -> str:
        lits = [self.bound] + utils.to_numerical(self.variables, self.modeler)
        return "k " + " ".join(map(str, lits))


class CountingVars:
    def __init__(
        self, varname_base, variables, modeler, upper_bound=None
    ) -> None:
        self.variables = variables
        self.modeler = modeler
        self.varname_base = varname_base
        self.added_clauses = []

        def v(i):
            return self.variables[i]

        # build counting variables
        def ub(i):
            return min(
                i + 1, upper_bound if upper_bound is not None else len(self.variables)
            )
            
        n_aux_vars = 0
        for i in range(len(self.variables)):
            for j in range(ub(i) + 1):
                self.modeler.add_var(
                    f"{self.varname_base}_{i, j}",
                    f"""auxiliary variable for counting constraint
                        over {self.varname_base}_{i}. Semantics mean that
                        exactly {j} variables are true until index {i} included""",
                )
                n_aux_vars += 1
        # print(f"created {n_aux_vars} auxiliary variables")
       
            #  print(f"created variable {self.varname_base}_{i, j}")

        def aux(i, j):
            return self.modeler.v(f"{self.varname_base}_{i, j}")

        def add_cls(cls):
            self.modeler.add_clause(cls)
            self.added_clauses.append(cls)

        # Build constraints according to Sinz encoder in O(N*K) many clauses.
        # the first variable is defined explicitly
        add_cls([-v(0), aux(0, 1)])
        add_cls([v(0), -aux(0, 1)])
        add_cls([-v(0), -aux(0, 0)])
        add_cls([v(0), aux(0, 0)])

        # A(i, j) <==> (A(i-1, j-1) ^ v(i)) v (A(i-1, j) ^ ~v(i))

        for i in range(1, len(self.variables)):
            for j in range(1, ub(i) + 1):
                # aux(i-1, j-1) ^ v(i) => aux(i, j)
                add_cls([-v(i), -aux(i - 1, j - 1), aux(i, j)])
                # aux(i-1, j-1) ^ ~v(i) => aux(i, j-1)
                add_cls([v(i), -aux(i - 1, j - 1), aux(i, j - 1)])
                # aux(i, j) => aux(i-1, j) or aux(i-1, j-1)
                # note that if j > i, then aux(i-1, j) is not defined.
                # add_cls([-aux(i, j), aux(i - 1, j - 1)] + ([aux(i - 1, j)] if j <= i else []))

            # aux(i, ub(i)) => aux(i+1, ub(i))
            if upper_bound is not None and i >= upper_bound:
                add_cls([-aux(i - 1, upper_bound), aux(i, upper_bound)])

        # at most one aux(i, j)
        for i in range(len(self.variables)):
            # print(f"i = {i}")
            self.modeler.at_most_one([aux(i, j) for j in range(ub(i) + 1)])
            # for j in range(ub(i) + 1):
            #     for k in range(j + 1, ub(i) + 1):
            #         add_cls([-aux(i, j), -aux(i, k)])

        # non-decreasing for bounded counts.        
        for j in range(ub(len(self.variables)) + 1):
            self.modeler.add_var(
                f"{self.varname_base}_{j}",
                f"total count = {j} for variables {self.varname_base}",
            )
            add_cls(
                [
                    -aux(len(self.variables) - 1, j),
                    self.modeler.v(f"{self.varname_base}_{j}"),
                ]
            )
            add_cls(
                [
                    aux(len(self.variables) - 1, j),
                    -self.modeler.v(f"{self.varname_base}_{j}"),
                ]
            )
