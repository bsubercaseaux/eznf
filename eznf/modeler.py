import itertools
import time
from subprocess import TimeoutExpired, check_output, CalledProcessError, STDOUT
from eznf import eznf_parser


class Modeler:
    def __init__(self, input_filename=None) -> None:
        self.reset()
        if input_filename is not None:
            self.load(input_filename)

    def load(self, input_filename) -> None:
        with open(input_filename, "r") as file:
            for line in file:
                if line[0] == "c":
                    continue
                elif line[0] == "p":
                    tokens = line.split(" ")
                    if tokens[1] == "cnf":
                        self._max_sat = False
                    elif tokens[1] == "wcnf":
                        self._max_sat = True
                    else:
                        raise TypeError("Unknown file type")
                    n_vars = int(tokens[2])
                    for i in range(n_vars):
                        self.add_var(f"__unnamed_{i}", f"unnamed variable {i}")
                else:  # clause
                    clause = list(map(int, line.split(" ")[:-1]))
                    self.add_clause(clause)

    def reset(self) -> None:
        self._varmap = {}
        self._rvarmap = {}
        self._clauses = []
        self._kconstraints = []
        self._gconstraints = []
        self._semvars = {}
        self._max_sat = False
        self._clause_weights = {}

    def add_var(self, name, description="no description", var_number=None) -> None:
        if name in self._varmap:
            print(f"[Warning]: Variable {name} already exists")
            return
        if var_number is None:
            self._varmap[name] = (len(self._varmap) + 1, description)
        else:
            assert var_number not in self._rvarmap
            self._varmap[name] = (var_number, description)

        self._rvarmap[self._varmap[name][0]] = name
        return self._varmap[name][0]

    def add_svar(self, name, semantic_type, description="no_description", **kwargs):
        if name in self._semvars:
            return self._semvars[name]
        if semantic_type == "ORDER_INTERVAL":
            assert "interval" in kwargs
            self._semvars[name] = OrderInterval(
                self, name, description, kwargs["interval"], kwargs["active_length"]
            )
            return self._semvars[name]
        elif semantic_type == "XOR":
            assert "left" in kwargs
            assert "right" in kwargs
            self._semvars[name] = XOR_var(kwargs["left"], kwargs["right"])
            return self._semvars[name]
        elif semantic_type == "COUNTING_VARS":
            self._semvars[name] = CountingVars(name, kwargs["variables"], self)
        else:
            raise TypeError("Unknown semantic type")

    def add_sclause(self, sclause) -> None:
        self.add_clauses(sclause.to_clauses())

    def constraint(self, constraint: str) -> None:
        clauses = eznf_parser.str_to_clauses(constraint)
        for clause in clauses:
            self.add_clause(clause)

    def add_soft_clause(self, clause) -> None:
        self._clauses.append(clause)
        if self._max_sat is False:
            # transform to max sat
            self._max_sat = True
            for prev_clause in self._clauses:
                self._clause_weights[tuple(prev_clause)] = "HARD"
        self._clause_weights[tuple(clause)] = "SOFT"

    def add_xor_disjunction(self, xor_disjunction, auxiliary=True) -> None:
        new_clauses = xor_disjunction.to_clauses(auxiliary)
        self.add_clauses(new_clauses)

    def v(self, name, introduce_if_absent=False) -> int:
        if name not in self._varmap:
            if introduce_if_absent:
                self.add_var(name, description="implictly introduced variable")
                return self._varmap[name][0]
            return None
        return self._varmap[name][0]

    def lit_to_str(self, lit: int) -> str:
        if lit > 0:
            return f"{self._rvarmap[lit]}"
        else:
            return f"~{self._rvarmap[-lit]}"

    def n_clauses(self) -> int:
        return len(self._clauses)

    def n_vars(self) -> int:
        return len(self._varmap)

    def cube_and_conquer(self, cube_generator, output_file="cubes.icnf") -> None:
        cubes = cube_generator()
        with open(output_file, "w") as file:
            file.write("p inccnf\n")
            for clause in self._clauses:
                file.write(" ".join(map(str, clause)) + " 0\n")
            for cube in cubes:
                file.write("a " + " ".join(map(str, cube)) + " 0\n")

    def interval_contains(self, name, value) -> int:
        order_interval = self._semvars[name]
        return order_interval.contains(value)

    def add_clause(self, clause) -> None:
        if self._max_sat:
            self._clause_weights[tuple(clause)] = "HARD"
        numerical_clause = to_numerical(clause, self)
        numerical_clause = clause_filter(numerical_clause)
        if numerical_clause == "SKIP":
            return
        for lit in numerical_clause:
            if abs(lit) not in self._rvarmap:
                self.add_var(
                    f"_anonymous_var_by_number_{abs(lit)}", var_number=abs(lit)
                )

        self._clauses.append(numerical_clause)

    def add_clauses(self, clauses) -> None:
        for clause in clauses:
            self.add_clause(clause)

    def add_gconstraint(self, bound, guard, variables) -> None:
        g_constraint = GConstraint(bound, guard, variables)
        self._gconstraints.append(g_constraint)

    def add_kconstraint(self, bound, variables) -> None:
        k_constraint = KConstraint(bound, variables, modeler=self)
        self._kconstraints.append(k_constraint)

    def exactly_one(self, variables) -> None:
        self.add_clauses(CExactly(1, variables, self).to_clauses())

    def at_most_one(self, variables, type="3-chunks") -> None:
        if type == "naive":
            self.add_clauses(CAtMostOne(variables, self).to_clauses_naive())
        elif type == "bin-tree":
            self.add_clauses(CAtMostOne(variables, self).to_clauses_2())
        elif type == "3-chunks":
            self.add_clauses(CAtMostOne(variables, self).to_clauses())
        else:
            self.add_clauses(CAtMostOne(variables, self).to_clauses_o())

    def at_most_k(self, variables, k) -> None:
        if k >= len(variables):
            return  # nothing to enforce in this case; it's vacuously true
        # print("entering at most k")
        # print(f"len vars = {len(variables)}, k = {k}")
        self.add_clauses(CAtMost(k, variables, self).to_clauses())
        # print("exiting at most k")

    def at_least_k(self, variables, k) -> None:
        if k == 1:
            print("warning: inefficiency in the encoding!")

        # sum_{v in variables} v >= k
        # sum_{v in variables} -v <= |variables| - k
        num_variables = to_numerical(variables, self)
        neg_variables = [-var for var in num_variables]
        self.at_most_k(neg_variables, len(variables) - k)

    def serialize(self, basename) -> None:
        self.serialize_encoding(basename)
        self.serialize_decoder(basename + ".dec")

    def serialize_encoding(self, filename, clauses=None) -> None:
        if clauses is None:
            clauses = self._clauses
        knf_constraints = self._gconstraints + self._kconstraints

        with open(filename, "w") as file:
            if self._max_sat:
                top = len(clauses) + 1  # not entirely sure about this yet.
                file.write(
                    "p wcnf {} {} {}\n".format(len(self._varmap), len(clauses), top)
                )
                for clause in clauses:
                    clause_weight = (
                        top if self._clause_weights[tuple(clause)] == "HARD" else 1
                    )
                    file.write(" ".join(map(str, [clause_weight] + clause)) + " 0\n")
            elif len(knf_constraints):
                file.write(
                    "p knf {} {}\n".format(
                        len(self._varmap), len(clauses) + len(knf_constraints)
                    )
                )
                for clause in clauses:
                    file.write(" ".join(map(str, clause)) + " 0\n")
                for knf_constraint in knf_constraints:
                    file.write(knf_constraint.to_str() + " 0\n")

            else:
                file.write("p cnf {} {}\n".format(self.max_var_number(), len(clauses)))
                for clause in clauses:
                    file.write(" ".join(map(str, clause)) + " 0\n")

    def max_var_number(self) -> int:
        mx = 0
        for clause in self._clauses:
            mx = max(mx, max([abs(lit) for lit in clause]))
        return mx

    def serialize_decoder(self, filename) -> None:
        pass

    def decode_from_sol(self, sol_filename, output_builder) -> str:
        lit_valuation = {}
        with open(sol_filename, "r") as sol:
            for line in sol:
                if line[0] == "v":
                    tokens = line[:-1].split(" ")  # skip newline
                    relevant_tokens = tokens[1:]
                    for token in relevant_tokens:
                        int_token = int(token)
                        if int_token == 0:
                            continue
                        lit_valuation[abs(int_token)] = int_token > 0
        sem_valuation = {}
        for lit_name, (lit, _) in self._varmap.items():
            if lit in lit_valuation:
                sem_valuation[lit_name] = lit_valuation[lit]
            else:
                # print(f"[Warning]: variable {lit_name} exists in the encoding, but not in the provided solution")
                sem_valuation[lit_name] = False
        for sem_name, sem_var in self._semvars.items():
            if isinstance(sem_var, OrderInterval):
                sem_valuation[sem_name] = OrderIntervalValuation(sem_var, lit_valuation)
        return output_builder(sem_valuation)

    def solve_and_decode(self, output_builder, solver="kissat") -> None:
        lit_valuation = {}
        self.serialize("tmp.cnf")
        output, return_code = system_call([solver, f"tmp.cnf"])
        if return_code != 10:
            print(
                f"return code = {return_code}, UNSAT formula does not allow decoding."
            )
            return

        for line in output.split("\n"):
            if len(line) > 0 and line[0] == "v":
                tokens = line.split(" ")  # skip newline
                relevant_tokens = tokens[1:]
                for token in relevant_tokens:
                    int_token = int(token)
                    if int_token == 0:
                        continue
                    lit_valuation[abs(int_token)] = int_token > 0
        sem_valuation = {}
        for lit_name, (lit, _) in self._varmap.items():
            sem_valuation[lit_name] = lit_valuation[lit]

        # for sem_name, sem_var in self._semvars.items():
        #     sem_valuation[sem_name] = OrderIntervalValuation(sem_var, lit_valuation)
        output_builder(sem_valuation)

    def solve_with_proof(self, timeout=None):
        tmp_filename = "__tmp.cnf"
        self.serialize(tmp_filename)
        proof_filename = "__proof.drat"
        output, return_code, elapsed_time = timed_run_shell(
            ["kissat", tmp_filename, proof_filename, "--no-binary"], timeout=timeout
        )
        proof = []
        with open(proof_filename, "r") as file:
            for line in file:
                proof.append(line.split(" ")[:-1])
        return proof, elapsed_time

    def debug(self, filename) -> None:
        output, return_code = system_call(["cadical", f"{filename}"])
        # if not success:
        #     print("Something failed with the system call to cadical")
        #     return
        if return_code == 10:
            print(
                "The formula was found to be SAT. If it should be UNSAT, press enter to continue debugging."
            )
            nxt = input()
            if len(nxt) > 0:
                return
            v_lines = [
                line for line in output.split("\n") if len(line) >= 1 and line[0] == "v"
            ]
            lit_map = {}
            for v_line in v_lines:
                tokens = v_line.split(" ")
                for token in tokens[1:]:
                    lit_map[abs(int(token))] = True if int(token) > 0 else False

            lit_print = input(
                "Press 'p' to print the positive literals, and t to print the total valuation "
            )
            if lit_print == "t":
                print("### Satisfying assignment ###")
                for lit_name, (lit, _) in self._varmap.items():
                    print(f"{lit_name} = {lit_map[lit]}")
            elif lit_print == "p":
                print("### Satisfying assignment ###")
                for lit_name, (lit, _) in self._varmap.items():
                    if lit_map[lit]:
                        print(f"{lit_name} = {lit_map[lit]}")

        elif return_code == 20:
            print(
                "The formula was found to be UNSAT. If it should be SAT, press enter to continue debugging."
            )
            nxt = input()
            if len(nxt) > 0:
                return
            else:
                # raise NotImplementedError("Debugging UNSAT formulas is not implemented yet")
                # minimize unsat core naively.
                # let's try to remove clauses one by one and see if the formula is still unsat.
                clauses = self._clauses
                while True:
                    for i in range(len(clauses)):
                        t_clauses = clauses[:i] + clauses[i + 1 :]
                        self.serialize_encoding("tmp.cnf", t_clauses)
                        output, return_code = system_call(["cadical", "tmp.cnf"])
                        if return_code == 20:
                            print(f"Removed clause {i} ")
                            clauses = t_clauses
                            break
                    else:
                        print("No more clauses to remove")
                        print("Remaining # of clauses:", len(clauses))

                        break
                clause_print = input("Press 'c' to print the clauses. ")
                if clause_print == "c":
                    print("### Clauses ###")
                    self.print_clauses(clauses)
                invalidate_assigment = input(
                    "Press enter to see what clauses are unsatisfied by an input assignment. "
                )
                relevant_lits = set()
                assignment = {}
                for clause in clauses:
                    for lit in clause:
                        relevant_lits.add(max(lit, -lit))
                for lit in relevant_lits:
                    lit_val = input(f"variable: {self.lit_to_str(lit)} [0/1]: ")
                    assignment[lit] = lit_val == "1"
                print(assignment)
                for clause in clauses:
                    works = False
                    for lit in clause:
                        if assignment[max(lit, -lit)] == (lit > 0):
                            works = True
                            break
                    if not works:
                        print(f"Unsatisfied clause: {self.clause_as_str(clause)}")
                        # self.print_clause(clause)

            # filtered_clauses_var = input("type the name of a vairable to filter clauses. ")
            # lit = self._varmap[filtered_clauses_var][0]
            # for clause in self._clauses:
            #   if lit in clause or -lit in clause:
            #       print([self.lit_to_str(lit) for lit in clause])

    def print_clause(self, clause):
        print([self.lit_to_str(lit) for lit in clause])

    def clause_as_str(self, clause):
        return str([self.lit_to_str(lit) for lit in clause])

    def print_clauses(self, clauses=None) -> None:
        if clauses is None:
            clauses = self._clauses
        for clause in clauses:
            self.print_clause(clause)


class XOR_var:
    def __init__(self, left, right) -> None:
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"XOR({self.left}, {self.right})"

    def __repr__(self) -> str:
        return self.__str__()


def to_numerical(clause, modeler: Modeler) -> [int]:
    numerical_clause = []
    for slit in clause:
        if type(slit) == str:
            if slit[0] == "~" or slit[0] == "-":
                numerical_clause.append(-modeler.v(slit[1:], introduce_if_absent=True))
            else:
                numerical_clause.append(modeler.v(slit, introduce_if_absent=True))
        elif type(slit) == int:
            numerical_clause.append(slit)
        else:
            raise TypeError("Unknown type in clause")
    return numerical_clause


def clause_filter(clause: [int]) -> [int]:
    literal_set = set(clause)
    for lit in clause:
        if (-lit) in literal_set:
            return "SKIP"
    return list(literal_set)


class CExactly:
    def __init__(self, k: int, variables, modeler) -> None:
        self.k = k
        self.variables = variables
        self.modeler = modeler

    def to_clauses(self) -> [[int]]:
        clauses = []
        if self.k == 1:
            at_least = to_numerical(self.variables, self.modeler)
            clauses.append(at_least)
            clauses += CAtMostOne(self.variables, self.modeler).to_clauses()
            return clauses
        else:
            raise NotImplementedError("CExactly is only implemented for k=1")


class CAtMostOne:
    def __init__(self, variables, modeler: Modeler) -> None:
        self.variables = to_numerical(variables, modeler)
        self.modeler = modeler

    def to_clauses_naive(self) -> [[int]]:
        clauses = []
        for v1, v2 in itertools.combinations(self.variables, 2):
            clauses.append([-v1, -v2])
        return clauses

    def to_clauses(self) -> [[int]]:
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

    def to_clauses_o(self) -> [[int]]:
        if len(self.variables) <= 4:
            return self.to_clauses_naive()
        else:
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

    def to_clauses_2(self) -> [[int]]:
        if len(self.variables) <= 4:
            return self.to_clauses_naive()
        else:
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
    def __init__(self, k: int, variables, modeler: Modeler) -> None:
        self.k = k
        self.variables = to_numerical(variables, modeler)
        self.modeler = modeler

    def to_clauses(self) -> [[int]]:
        if self.k == 1:
            return CAtMostOne(self.variables, self.modeler).to_clauses()
        else:
            hsh = hash(tuple(self.variables))
            vnames = f"__auxcount_{hsh}"
            cvars = CountingVars(
                vnames, self.variables, self.modeler, upper_bound=self.k + 1
            )
            return cvars.added_clauses + [[-self.modeler.v(f"__vnames_{self.k+1}")]]


class GConstraint:
    def __init__(self, bound, guard, variables) -> None:
        self.bound = bound
        self.guard = guard
        self.variables = variables

    def to_str(self) -> str:
        lits = [self.bound] + [self.guard] + self.variables
        return "g " + " ".join(map(str, lits))


class KConstraint:
    def __init__(self, bound, variables, modeler) -> None:
        self.bound = bound
        self.modeler = modeler
        self.variables = variables

    def to_str(self) -> str:
        lits = [self.bound] + to_numerical(self.variables, self.modeler)
        return "k " + " ".join(map(str, lits))


class CountingVars:
    def __init__(
        self, varname_base, variables, modeler: Modeler, upper_bound=None
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

        for i in range(len(self.variables)):
            for j in range(ub(i) + 1):
                self.modeler.add_var(
                    f"{self.varname_base}_{i, j}",
                    f"auxiliary variable for counting constraint over {self.varname_base}_{i}. Semantics mean that exactly {j} variables are true until index {i} included",
                )
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


class XOR_disjunction:
    def __init__(self, xor_vars, modeler: Modeler) -> None:
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
            # new_clause = [self.modeler.v(f"__aux_xor_{xor_var.left}_{xor_var.right}") for xor_var in self.xor_vars]
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


class OrderInterval:
    def __init__(self, modeler, name, description, interval, active_length) -> None:
        self._name = name
        self._description = description
        self._interval = interval
        self.max_vars = []
        self.min_vars = []

        for i in range(interval[0], interval[1]):
            modeler.add_var(
                f"__max_interval:{name}_{i}",
                f"{i}-th variable of the max-order-interval encoding for {name}",
            )
            modeler.add_var(
                f"__min_interval:{name}_{i}",
                f"{i}-th variable of the min-order-interval encoding for {name}",
            )

            self.max_vars.append(modeler.v(f"__max_interval:{name}_{i}"))
            self.min_vars.append(modeler.v(f"__min_interval:{name}_{i}"))

        for i in range(interval[0], interval[1]):

            if i > interval[0]:
                # max: 1 at pos i implies 1 at pos i-1
                modeler.add_clause([-self.max_vars[i], self.max_vars[i - 1]])
            if i + 1 < interval[1]:
                # min: 1 at pos i implies 1 at pos i+1
                modeler.add_clause([-self.min_vars[i], self.min_vars[i + 1]])

        # given j >= active_length-1
        # max must be true until active_length - 1
        # given i + active_length < interval[1]
        # min must be activel at interval[1] - active_length
        if isinstance(active_length, int):
            modeler.add_clause([self.max_vars[active_length - 1]])
            modeler.add_clause([self.min_vars[interval[1] - active_length]])
        else:
            # active_length is a functional variable.
            # active_length = (var, if_true, if_false)
            variable, if_true, if_false = active_length
            modeler.add_clause([-modeler.v(variable), self.max_vars[if_true - 1]])
            modeler.add_clause([modeler.v(variable), self.max_vars[if_false - 1]])
            modeler.add_clause(
                [-modeler.v(variable), self.min_vars[interval[1] - if_true]]
            )
            modeler.add_clause(
                [modeler.v(variable), self.min_vars[interval[1] - if_false]]
            )

        # active range restrictions
        # range [i, j] <-> min is true from i, max is true until j
        # min[i] -> range starts at most at i
        #        -> range ends at most at i+active_length-1
        #        -> max[i+active_length] is false
        # ~min[i] -> range starts at least at i+1
        #         -> range ends at least at i+active_length
        #        -> max[i+active_length] is true
        if isinstance(active_length, int):
            for i in range(interval[0], interval[1]):
                if i + active_length < interval[1]:
                    modeler.add_clause(
                        [-self.min_vars[i], -self.max_vars[i + active_length]]
                    )
                    modeler.add_clause(
                        [self.min_vars[i], self.max_vars[i + active_length]]
                    )
        else:
            variable, if_true, if_false = active_length
            for i in range(interval[0], interval[1]):
                if i + if_true < interval[1]:
                    modeler.add_clause(
                        [
                            -modeler.v(variable),
                            -self.min_vars[i],
                            -self.max_vars[i + if_true],
                        ]
                    )
                    modeler.add_clause(
                        [
                            -modeler.v(variable),
                            self.min_vars[i],
                            self.max_vars[i + if_true],
                        ]
                    )
                if i + if_false < interval[1]:
                    modeler.add_clause(
                        [
                            modeler.v(variable),
                            -self.min_vars[i],
                            -self.max_vars[i + if_false],
                        ]
                    )
                    modeler.add_clause(
                        [
                            modeler.v(variable),
                            self.min_vars[i],
                            self.max_vars[i + if_false],
                        ]
                    )

    def contains(self, index) -> [int]:
        return SemCNF(
            [SemClause([self.min_vars[index]]), SemClause([self.max_vars[index]])]
        )


class OrderIntervalValuation:
    def __init__(self, order_interval, lit_valuation) -> None:
        self._order_interval = order_interval
        self._lit_valuation = lit_valuation
        self.active_range = []
        for index in range(order_interval._interval[0], order_interval._interval[1]):
            if (
                self._lit_valuation[order_interval.min_vars[index]]
                and self._lit_valuation[order_interval.max_vars[index]]
            ):
                self.active_range.append(index)


class Implication:
    def __init__(self, implicant, implicate):
        sem_implicant = SemCNF(implicant)
        sem_implicate = SemCNF(implicate)
        self._semcnf = Or(Not(sem_implicant), sem_implicate)

    def to_clauses(self) -> [[int]]:
        return self._semcnf.to_clauses()


class SemClause:
    def __init__(self, lits):
        self.literals = lits

    def to_clause(self) -> [int]:
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

    def to_clauses(self) -> [[int]]:
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


def system_call(command, timeout=None):
    """
    params:
        command: list of strings, ex. ["ls", "-l"]
        timeout: number of seconds to wait for the command to complete.
    returns: output, return_code
    """
    try:
        output = check_output(command, stderr=STDOUT, timeout=timeout).decode()
        return_code = 0
    except CalledProcessError as e:
        output = e.output.decode()
        return_code = e.returncode
    except TimeoutExpired:
        output = "Command timed out after {} seconds".format(timeout)
        return_code = (
            -1
        )  # You can use any number that is not a valid return code for a success or normal failure
    return output, return_code


def timed_run_shell(commands, timeout=None):
    """
    params:
        command: list of strings, ex. ["ls", "-l"]
        timeout: number of seconds to wait for the command to complete.
    returns: output, return_code
    """
    start_time = time.perf_counter_ns()
    output, return_code = system_call(commands, timeout=timeout)
    elapsed_time = time.perf_counter_ns() - start_time
    return output, return_code, elapsed_time
