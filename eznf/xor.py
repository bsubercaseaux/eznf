import itertools

class XORVar:
    def __init__(self, left, right) -> None:
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"XOR({self.left}, {self.right})"

    def __repr__(self) -> str:
        return self.__str__()


class XORDisjunction:
    def __init__(self, xor_vars, modeler) -> None:
        self.xor_vars = xor_vars
        self.modeler = modeler

    def to_clauses(self, auxiliary=True):
        clauses = []

        if auxiliary:

            for xor_var in self.xor_vars:
                left, right = self.modeler.v(xor_var.left), self.modeler.v(
                    xor_var.right
                )
                if self.modeler.v(f"__aux_xor_{left}_{right}") is None:
                    self.modeler.add_var(
                        f"__aux_xor_{left}_{right}",
                        "auxiliary variable for xor disjunction",
                    )
                    xvar = self.modeler.v(f"__aux_xor_{left}_{right}")

                    clauses.append([-xvar, left, right])
                    clauses.append([-xvar, -left, -right])
                    clauses.append([xvar, left, -right])
                    clauses.append([xvar, -left, right])
            new_clause = []
            for xor_var in self.xor_vars:
                left, right = self.modeler.v(xor_var.left), self.modeler.v(
                    xor_var.right
                )
                new_clause.append(self.modeler.v(f"__aux_xor_{left}_{right}"))

            clauses.append(new_clause)

        else:
            # We have OR_i (a_i xor b_i) and want to translate to CNF without auxiliary variables.
            # What assignments would falsify this?
            # essentially those that for each i choose a value v_i and have a_i = b_i = v_i.
            # a_i -> ~b_i or (OR_{j=i+1} (a_j xor b_j))
            # ~a_i or ~b_i or (OR_{j=i+1} (a_j xor b_j))
            for cmb in itertools.product([1, -1], repeat=len(self.xor_vars)):
                clause = []
                for idx, el in enumerate(self.xor_vars):
                    left, right = self.modeler.v(el.left), self.modeler.v(el.right)
                    clause.extend([cmb[idx] * left, cmb[idx] * right])
                clauses.append(clause)
        return clauses
