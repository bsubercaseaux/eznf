from eznf import eznf_parser
from eznf import utils
from eznf import cardinality
from eznf import order_interval
from eznf import constants
from eznf import xor


class Modeler:
    def __init__(self, input_filename=None) -> None:
        self.reset()
        if input_filename is not None:
            self.load(input_filename)

    def load(self, input_filename) -> None:
        with open(input_filename, "r", encoding="utf-8") as file:
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
        self._qbf = False
        self._qbf_var_blocks = []
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

    def add_existential_var(
        self, name, description="no description", var_number=None
    ) -> None:
        self.add_var(name, description, var_number)
        if self._qbf is False:
            self._qbf = True
        if len(self._qbf_var_blocks) == 0 or self._qbf_var_blocks[-1][0] == "a":
            self._qbf_var_blocks.append(["e", self._varmap[name][0]])
        else:
            self._qbf_var_blocks[-1].append(self._varmap[name][0])

    def add_universal_var(
        self, name, description="no description", var_number=None
    ) -> None:
        self.add_var(name, description, var_number)
        if self._qbf is False:
            self._qbf = True
        if len(self._qbf_var_blocks) == 0 or self._qbf_var_blocks[-1][0] == "e":
            self._qbf_var_blocks.append(["a", self._varmap[name][0]])
        else:
            self._qbf_var_blocks[-1].append(self._varmap[name][0])

    def add_svar(self, name, semantic_type, description="no_description", **kwargs):
        if name in self._semvars:
            return self._semvars[name]
        if semantic_type == "ORDER_INTERVAL":
            assert "interval" in kwargs
            self._semvars[name] = order_interval.OrderInterval(
                self, name, description, kwargs["interval"], kwargs["active_length"]
            )
            return self._semvars[name]
        elif semantic_type == "XOR":
            assert "left" in kwargs
            assert "right" in kwargs
            self._semvars[name] = xor.XORVar(kwargs["left"], kwargs["right"])
            return self._semvars[name]
        elif semantic_type == "COUNTING_VARS":
            self._semvars[name] = cardinality.CountingVars(
                name, kwargs["variables"], self
            )
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
            raise KeyError(f"Variable {name} not found")
        return self._varmap[name][0]
     
    def has_var(self, name) -> bool:
        return name in self._varmap

    def lit_to_str(self, lit: int) -> str:
        if lit > 0:
            return f"{self._rvarmap[lit]}"
        else:
            return f"-{self._rvarmap[-lit]}"

    def get_clauses(self) -> list:
        """ returns the clauses currently in the modeler."""
        return self._clauses

    def get_vars(self) -> list:
        """ returns the variables currently in the modeler.
            each variable is a tuple (name, number, description).
        """
        ans = []
        for name, (number, description) in self._varmap.items():
            ans.append((name, number, description))
        return ans

    def n_clauses(self) -> int:
        """ number of clauses."""
        return len(self._clauses)

    def n_vars(self) -> int:
        """ number of used variables.
            NOTE: this is different from the max variable index used.
        Returns:
            int: total number of different variables, including auxiliary ones.
        """
        return len(self._varmap)

    def cube_and_conquer(self, cube_generator, output_file="cubes.icnf") -> None:
        cubes = cube_generator()
        with open(output_file, "w", encoding="utf-8") as file:
            file.write("p inccnf\n")
            for clause in self._clauses:
                file.write(" ".join(map(str, clause)) + " 0\n")
            for cube in cubes:
                file.write("a " + " ".join(map(str, cube)) + " 0\n")

    def interval_contains(self, name, value) -> int:
        o_interval = self._semvars[name]
        return o_interval.contains(value)

    def add_clause(self, clause) -> None:
        if self._max_sat:
            self._clause_weights[tuple(clause)] = "HARD"
        numerical_clause = utils.to_numerical(clause, self)
        numerical_clause = utils.clause_filter(numerical_clause)
        if numerical_clause == "SKIP":
            return
        for lit in numerical_clause:
            if abs(lit) not in self._rvarmap:
                self.add_var(
                    f"_anonymous_var_by_number_{abs(lit)}", var_number=abs(lit)
                )
        for cl in self._clauses:
            if set(cl) == set(numerical_clause):
                return
        self._clauses.append(numerical_clause)

    def add_clauses(self, clauses) -> None:
        for clause in clauses:
            self.add_clause(clause)

    def add_gconstraint(self, bound, guard, variables) -> None:
        g_constraint = cardinality.GConstraint(bound, guard, variables)
        self._gconstraints.append(g_constraint)

    def add_kconstraint(self, bound, variables) -> None:
        k_constraint = cardinality.KConstraint(bound, variables, modeler=self)
        self._kconstraints.append(k_constraint)

    def exactly_one(self, variables) -> None:
        self.add_clauses(cardinality.CExactly(1, variables, self).to_clauses())
        
    def exactly_k(self, variables, k) -> None:
        self.add_clauses(cardinality.CExactly(k, variables, self).to_clauses())

    def at_most_one(self, variables, constraint_type="3-chunks") -> None:
        if constraint_type == "naive":
            self.add_clauses(cardinality.CAtMostOne(variables, self).to_clauses_naive())
        elif constraint_type == "bin-tree":
            self.add_clauses(cardinality.CAtMostOne(variables, self).to_clauses_2())
        elif constraint_type == "3-chunks":
            self.add_clauses(cardinality.CAtMostOne(variables, self).to_clauses())
        else:
            self.add_clauses(cardinality.CAtMostOne(variables, self).to_clauses_o())

    def at_most_k(self, variables, k) -> None:
        if k >= len(variables):
            return  # nothing to enforce in this case; it's vacuously true
        # print("entering at most k")
        # print(f"len vars = {len(variables)}, k = {k}")
        self.add_clauses(cardinality.CAtMost(k, variables, self).to_clauses())
        # print("exiting at most k")

    def at_least_k(self, variables, k) -> None:
        if k == 1:
            print("warning: inefficiency in the encoding!")

        # sum_{v in variables} v >= k
        # sum_{v in variables} -v <= |variables| - k
        num_variables = utils.to_numerical(variables, self)
        neg_variables = [-var for var in num_variables]
        self.at_most_k(neg_variables, len(variables) - k)

    def serialize(self, basename) -> None:
        self.serialize_encoding(basename)
        self.serialize_decoder(basename + ".dec")

    def serialize_encoding(self, filename, clauses=None) -> None:
        if clauses is None:
            clauses = self._clauses
        knf_constraints = self._gconstraints + self._kconstraints
        max_var = self.max_var_number()

        with open(filename, "w", encoding="utf-8") as file:
            if self._max_sat:
                top = len(clauses) + 1  # not entirely sure about this yet.
                file.write(f"p wcnf {max_var} {len(clauses)} {top}\n")
                for clause in clauses:
                    clause_weight = (
                        top if self._clause_weights[tuple(clause)] == "HARD" else 1
                    )
                    file.write(" ".join(map(str, [clause_weight] + clause)) + " 0\n")
            elif len(knf_constraints) > 0:
                file.write(f"p knf {max_var} {len(clauses) + len(knf_constraints)}\n")
                for clause in clauses:
                    file.write(" ".join(map(str, clause)) + " 0\n")
                for knf_constraint in knf_constraints:
                    file.write(knf_constraint.to_str() + " 0\n")
            elif self._qbf:
                file.write(f"p cnf {max_var} {len(clauses)}\n")
                for block in self._qbf_var_blocks:
                    file.write(" ".join(map(str, block)) + " 0\n")
                for clause in clauses:
                    file.write(" ".join(map(str, clause)) + " 0\n")
            else:
                file.write(f"p cnf {max_var} {len(clauses)}\n")
                for clause in clauses:
                    file.write(" ".join(map(str, clause)) + " 0\n")

    def max_var_number(self) -> int:
        mx = 0
        for clause in self._clauses:
            mx = max(mx, *[abs(lit) for lit in clause])
        return mx

    def serialize_decoder(self, filename) -> None:
        pass

    def decode_from_sol(self, sol_filename, output_builder) -> str:
        lit_valuation = {}
        with open(sol_filename, "r", encoding="utf-8") as sol:
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
                sem_valuation[lit_name] = False
        for sem_name, sem_var in self._semvars.items():
            if isinstance(sem_var, order_interval.OrderInterval):
                sem_valuation[sem_name] = order_interval.OrderIntervalValuation(
                    sem_var, lit_valuation
                )
        return output_builder(sem_valuation)

    def solve_and_decode(self, output_builder, solver="kissat") -> None:
        lit_valuation = {}
        self.serialize(constants.TMP_FILENAME)
        output, return_code = utils.system_call([solver, constants.TMP_FILENAME])
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
        _, _, elapsed_time = utils.timed_run_shell(
            ["kissat", tmp_filename, proof_filename, "--no-binary"], timeout=timeout
        )
        proof = []
        with open(proof_filename, "r", encoding="utf-8") as file:
            for line in file:
                proof.append(line.split(" ")[:-1])
        return proof, elapsed_time

    def debug(self, filename) -> None:
        output, return_code = utils.system_call(["cadical", f"{filename}"])
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
                        output, return_code = utils.system_call(["cadical", "tmp.cnf"])
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
                input(
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
