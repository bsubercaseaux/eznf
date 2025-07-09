from eznf import eznf_parser
from eznf import utils
from eznf import cardinality
from eznf import order_interval
from eznf import constants
from eznf import xor
from eznf import equivars
from eznf.solver_output import SolverOutput


class Modeler:
    """
    The `Modeler` class represents a modeler for propositional logic formulas.
    It provides methods for loading formulas, adding variables and clauses,
    and performing various operations on the formulas.

    Attributes:
        _varmap (dict): A dictionary mapping variable names to their corresponding numbers and descriptions.
        _rvarmap (dict): A dictionary mapping variable numbers to their corresponding names.
        _clauses (list): A list of clauses in the modeler.
        _kconstraints (list): A list of cardinality constraints in the modeler.
        _gconstraints (list): A list of generalized constraints in the modeler.
        _semvars (dict): A dictionary mapping semantic variable names to their corresponding objects.
        _max_sat (bool): A boolean indicating whether the modeler is in MaxSAT mode.
        _qbf (bool): A boolean indicating whether the modeler is in QBF mode.
        _qbf_var_blocks (list): A list of quantifier blocks in the modeler.
        _clause_weights (dict): A dictionary mapping clauses to their corresponding weights.

    Methods:
        __init__(self, input_filename=None): Initializes a new instance of the Modeler class.
        load(self, input_filename): Loads a formula from a file.
        reset(self): Resets the modeler to its initial state.
        add_var(self, name, description="no description", var_number=None): Adds a variable to the modeler.
        add_existential_var(self, name, description="no description", var_number=None): Adds an existential variable to the modeler.
        add_universal_var(self, name, description="no description", var_number=None): Adds a universal variable to the modeler.
        add_svar(self, name, semantic_type, description="no_description", **kwargs): Adds a semantic variable to the modeler.
        add_sclause(self, sclause): Adds a semantic clause to the modeler.
        constraint(self, constraint): Adds a constraint to the modeler.
        add_soft_clause(self, clause): Adds a soft clause to the modeler.
        add_xor_disjunction(self, xor_disjunction, auxiliary=True): Adds an XOR disjunction to the modeler.
        v(self, name, introduce_if_absent=False): Returns the number of a variable given its name.
        has_var(self, name): Checks if a variable exists in the modeler.
        lit_to_str(self, lit): Converts a literal to its string representation.
        get_clauses(self): Returns the clauses currently in the modeler.
        get_vars(self): Returns the variables currently in the modeler.
        n_clauses(self): Returns the number of clauses in the modeler.
        n_vars(self): Returns the number of used variables in the modeler.
        cube_and_conquer(self, cube_generator, output_file="cubes.icnf"): Generates cubes from the modeler and writes them to a file.
        interval_contains(self, name, value): Checks if an interval variable contains a value.
        add_clause(self, clause): Adds a clause to the modeler.
        add_clauses(self, clauses): Adds multiple clauses to the modeler.
        add_gconstraint(self, bound, guard, variables): Adds a generalized constraint to the modeler.
        add_kconstraint(self, bound, variables): Adds a cardinality constraint to the modeler.
        exactly_one(self, variables): Adds an exactly-one constraint to the modeler.
        exactly_k(self, variables, k): Adds an exactly-k constraint to the modeler.
        at_most_one(self, variables, constraint_type="3-chunks"): Adds an at-most-one constraint to the modeler.
        at_most_k(self, variables, k): Adds an at-most-k constraint to the modeler.
        at_least_k(self, variables, k): Adds an at-least-k constraint to the modeler.
        serialize(self, basename): Serializes the modeler to files.
        serialize_encoding(self, filename, clauses=None): Serializes the encoding part of the modeler to a file.
        serialize_decoder(self, filename): Serializes the decoder part of the modeler to a file.
    """

    def __init__(self, input_filename=None) -> None:
        self.reset()
        if input_filename is not None:
            self.load(input_filename)

    def load(self, input_filename) -> None:
        """
        Load a CNF or WCNF file into the modeler.

        Args:
            input_filename (str): The path to the input file.

        Raises:
            TypeError: If the file type is unknown.

        Returns:
            None
        """
        with open(input_filename, "r", encoding="utf-8") as file:
            for line in file:
                if line[0] == "c":
                    continue
                if line[0] == "p":
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
        """
        Resets the state of the modeler.

        This method clears all the internal data structures and 
        resets the modeler to its initial state.

        Returns:
            None
        """
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
        self._equivars = equivars.EquivalenceVarPool()

    def add_var(self, name, description="no description", var_number=None) -> None:
        """
        Adds a variable to the modeler.

        Args:
            name (str): The name of the variable.
            description (str, optional): The description of the variable. Defaults to
                "no description".
            var_number (int, optional): The variable number. 
                If not provided, it will be assigned automatically.

        Returns:
            None

        Raises:
            AssertionError: If var_number is provided and already exists in the modeler.

        """
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

    def add_var_equivalence(self, var1, var2) -> None:
        """
        Adds an equivalence relation between two variables.
        
        This method uses the equivalence variable pool to manage variable equivalences.
        
        Args:
            var1 (str | int): The name of the first variable.
            var2 (str | int): The name of the second variable.
            
        Returns:
            None
        """
        svar1 = var1
        svar2 = var2
        if isinstance(var1, int):
            svar1 = self._rvarmap[abs(var1)]
            if var1 < 0:
                svar1 = "-" + svar1
        if isinstance(var2, int):
            svar2 = self._rvarmap[abs(var2)]
            if var2 < 0:
                svar2 = "-" + svar2
        self._equivars.add_equivalence(svar1, svar2)

    def add_existential_var(
        self, name, description="no description", var_number=None
    ) -> None:
        """
        Adds an existential variable to the modeler for QBF formulas.
        
        Args:
            name (str): The name of the variable.
            description (str, optional): The description of the variable. Defaults to
                "no description".
            var_number (int, optional): The variable number. 
                If not provided, it will be assigned automatically.
                
        Returns:
            None
        """
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
        """
        Adds a universal variable to the modeler for QBF formulas.
        
        Args:
            name (str): The name of the variable.
            description (str, optional): The description of the variable. Defaults to
                "no description".
            var_number (int, optional): The variable number. 
                If not provided, it will be assigned automatically.
                
        Returns:
            None
        """
        self.add_var(name, description, var_number)
        if self._qbf is False:
            self._qbf = True
        if len(self._qbf_var_blocks) == 0 or self._qbf_var_blocks[-1][0] == "e":
            self._qbf_var_blocks.append(["a", self._varmap[name][0]])
        else:
            self._qbf_var_blocks[-1].append(self._varmap[name][0])

    def add_svar(self, name, semantic_type, description="no_description", **kwargs):
        """
        Adds a semantic variable to the modeler.
        
        Semantic variables represent higher-level constraints and can be of different types:
        - ORDER_INTERVAL: Represents an interval with ordering constraints
        - XOR: Represents an XOR relationship between two variables
        - COUNTING_VARS: Represents variables used for cardinality constraints
        
        Args:
            name (str): The name of the semantic variable.
            semantic_type (str): The type of semantic variable. One of "ORDER_INTERVAL", "XOR", or "COUNTING_VARS".
            description (str, optional): The description of the variable. Defaults to "no_description".
            **kwargs: Additional arguments depending on the semantic type.
                For ORDER_INTERVAL: "interval" and "active_length" are required.
                For XOR: "left" and "right" are required.
                For COUNTING_VARS: "variables" is required.
                
        Returns:
            The created semantic variable object.
            
        Raises:
            TypeError: If the semantic type is unknown.
            AssertionError: If required kwargs are missing for a specific semantic type.
        """
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
        """
        Adds a semantic clause to the modeler.
        
        A semantic clause is first converted to standard CNF clauses and then added to the modeler.
        
        Args:
            sclause: A semantic clause object with a to_clauses() method that converts it to CNF.
            
        Returns:
            None
        """
        self.add_clauses(sclause.to_clauses())

    def constraint(self, constraint: str) -> None:
        """
        Adds a constraint specified as a string to the modeler.
        
        The constraint string is parsed into CNF clauses using the eznf_parser,
        and each resulting clause is added to the modeler.
        
        Args:
            constraint (str): A string representation of the logical constraint.
                              For example: "x -> y" or "x <-> (y | z)"
            
        Returns:
            None
        """
        clauses = eznf_parser.str_to_clauses(constraint)
        # for debugging
        # print(f"adding constraint {constraint}")
        for clause in clauses:
            # print("clause:", clause)
            # print(self.clause_as_str(clause))
            self.add_clause(clause)
       

    def add_soft_clause(self, clause, weight=None) -> None:
        """
        Adds a soft clause to the modeler for MaxSAT problems.
        
        If this is the first soft clause, the modeler is converted to MaxSAT mode
        and all previous clauses are marked as hard constraints.
        
        Args:
            clause (list): A list of literals representing the clause.
            weight (int, optional): The weight of the soft clause.

        Returns:
            None
        """
        self._clauses.append(utils.to_numerical(clause, self))
        if self._max_sat is False:
            # transform to max sat
            self._max_sat = True
            for prev_clause in self._clauses:
                self._clause_weights[tuple(prev_clause)] = "HARD"
        self._clause_weights[tuple(utils.to_numerical(clause, self))] = 1 if weight is None else weight

    def add_xor_disjunction(self, xor_disjunction, auxiliary=True) -> None:
        """
        Adds an XOR disjunction to the modeler.
        
        Args:
            xor_disjunction: An XOR disjunction object with a to_clauses method.
            auxiliary (bool, optional): Whether to use auxiliary variables in the encoding.
                                        Defaults to True.
            
        Returns:
            None
        """
        new_clauses = xor_disjunction.to_clauses(auxiliary)
        self.add_clauses(new_clauses)

    def v(self, name, introduce_if_absent=False) -> int:
        """
        Returns the number of a literal given its name.
        
        Args:
            name (str): The name of the literal.
            introduce_if_absent (bool, optional): If True and the variable doesn't exist,
                                               create it. Defaults to False.
            
        Returns:
            int: The number associated to the literal (negative if negated).
            
        Raises:
            KeyError: If the variable doesn't exist and introduce_if_absent is False.
        """
        sgn = 1
        if name[0] == "-": 
            name = name[1:]
            sgn = -1
        
        if name not in self._varmap:
            if introduce_if_absent:
                self.add_var(name, description="implictly introduced variable")
                print(f"Warning: Variable {name} used but not found, introducing it now.")
                return self._varmap[name][0]
            raise KeyError(f"Variable {name} not found")
        return self._varmap[name][0] * sgn

    def has_var(self, name) -> bool:
        """
        Checks if a variable exists in the modeler.
        
        Args:
            name (str): The name of the variable to check.
            
        Returns:
            bool: True if the variable exists, False otherwise.
        """
        return name in self._varmap

    def lit_to_str(self, lit: int) -> str:
        """
        Converts a literal to its string representation.
        
        Args:
            lit (int): The literal to convert. Positive number for the variable,
                      negative number for its negation.
            
        Returns:
            str: The string representation of the literal.
                For positive literals, returns the variable name.
                For negative literals, returns the variable name with a '-' prefix.
        """
        if lit > 0:
            return f"{self._rvarmap[lit]}"
        else:
            return f"-{self._rvarmap[-lit]}"

    def get_clauses(self, no_dups=False) -> list:
        """returns the clauses currently in the modeler.
            no_dups: whether to eliminate duplicate clauses"""
        if no_dups:
            cls_set = set()
            filtered_cls = []
            for clause in self._clauses:
                sorted_clause = tuple(sorted(clause))
                if sorted_clause not in cls_set:
                    filtered_cls.append(clause)
                    cls_set.add(sorted_clause)
            return filtered_cls
        return self._clauses

    def get_vars(self) -> list:
        """returns the variables currently in the modeler.
        each variable is a tuple (name, number, description).
        """
        ans = []
        for name, (number, description) in self._varmap.items():
            ans.append((name, number, description))
        return ans

    def n_clauses(self) -> int:
        """number of clauses."""
        return len(self._clauses)

    def n_vars(self) -> int:
        """number of used variables.
            NOTE: this is different from the max variable index used.
        Returns:
            int: total number of different variables, including auxiliary ones.
        """
        return len(self._varmap)

    def cube_and_conquer(self, cube_generator, output_file="cubes.icnf") -> None:
        """
        Generates cubes from the modeler and writes them to a file for cube-and-conquer solving.
        
        This method implements the cube-and-conquer paradigm for SAT solving, where the problem
        is first split into smaller subproblems (cubes) that can be solved independently.
        
        Args:
            cube_generator: A function that returns a list of cubes (lists of literals).
            output_file (str, optional): The path to the output file. Defaults to "cubes.icnf".
            
        Returns:
            None
        """
        cubes = cube_generator()
        with open(output_file, "w", encoding="utf-8") as file:
            file.write("p inccnf\n")
            for clause in self._clauses:
                file.write(" ".join(map(str, clause)) + " 0\n")
            for cube in cubes:
                file.write("a " + " ".join(map(str, cube)) + " 0\n")

    def interval_contains(self, name, value) -> int:
        """
        Checks if an interval variable contains a specific value.
        
        Args:
            name (str): The name of the interval variable.
            value: The value to check for containment in the interval.
            
        Returns:
            int: The literal representing the containment relationship.
        """
        o_interval = self._semvars[name]
        return o_interval.contains(value)

    def add_clause(self, clause: list, introduce_if_absent = False) -> None:
        """
        Adds a clause to the modeler.
        
        Args:
            clause (list): A list of literals representing the clause. Literals can be
                          integers or strings (variable names with optional - prefix).
            
        Returns:
            None
            
        Note:
            This method handles conversion of string literals to numerical form.
            It automatically creates anonymous variables for unknown literal numbers.
            If in MaxSAT mode, the clause is marked as a hard constraint.
        """
        if not self._equivars.is_empty():
            clause_post_equiv = []
            for lit in clause:
               
                if isinstance(lit, int):
                    var_name = ("-" if lit < 0 else "") + self._rvarmap[abs(lit)]
                else:
                    var_name = lit
                if self._equivars.has_var(var_name):
                    clause_post_equiv.append(self._equivars.get_representative(var_name))
                else:
                    clause_post_equiv.append(lit)
            clause = clause_post_equiv  

    
        numerical_clause = utils.to_numerical(clause, self, introduce_if_absent=introduce_if_absent)
        numerical_clause = utils.clause_filter(numerical_clause)
        if self._max_sat:
            self._clause_weights[tuple(numerical_clause)] = "HARD"
        if numerical_clause == "SKIP":
            print(f"Warning: Clause {clause} is trivially true, skipping it")
            return
        for lit in numerical_clause:
            if abs(lit) not in self._rvarmap:
                # TODO: Warning: variable not found
                print(f"Warning: Variable {lit} not found in clause {clause}, introducing anonymous variable")
                self.add_var(
                    f"_anonymous_var_by_number_{abs(lit)}", var_number=abs(lit)
                )
            # for cl in self._clauses:
            #     if set(cl) == set(numerical_clause):
            #         return
        self._clauses.append(numerical_clause)
        
    def remove_clause(self, clause: list) -> None:
        """
        Removes a clause from the modeler.
        
        Args:
            clause (list): A list of literals representing the clause to remove.
            
        Returns:
            None
            
        Raises:
            NotImplementedError: If attempting to remove clauses in MaxSAT mode.
            ValueError: If the clause is not found in the modeler.
        """
        if self._max_sat:
            raise NotImplementedError("Removing clauses in MaxSAT is not implemented yet")
            
        numerical_clause = utils.to_numerical(clause, self)
        numerical_clause = utils.clause_filter(numerical_clause)
        
        self._clauses.remove(numerical_clause)
        
    def add_clauses(self, clauses) -> None:
        """
        Adds multiple clauses to the modeler.
        
        Args:
            clauses (list): A list of clauses, where each clause is a list of literals.
            
        Returns:
            None
        """
        for clause in clauses:
            self.add_clause(clause)


    def add_gconstraint(self, bound, guard, variables) -> None:
        """
        if guard: sum(variables) >= bound
        """
        g_constraint = cardinality.GConstraint(bound, guard, variables, modeler=self)
        self._gconstraints.append(g_constraint)

    def add_kconstraint(self, bound, variables) -> None:
        """sum(variables) >= bound

        Args:
            bound (_type_): _description_
            variables (_type_): _description_
        """
        k_constraint = cardinality.KConstraint(bound, variables, modeler=self)
        self._kconstraints.append(k_constraint)
        
    def add_gconstraint_le(self, bound, guard, variables) -> None:
        """
        if guard: sum(variables) <= bound
        """
        neg_variables = [-v for v in utils.to_numerical(variables, self)]
        neg_bound = len(variables) - bound
        self.add_gconstraint(neg_bound, guard, neg_variables)
        
    def add_kconstraint_le(self, bound, variables) -> None:
        """sum(variables) <= bound"""
        if bound >= len(variables):
            print(f"Warning: k-constraint with bound {bound} is vacuously true")
            return
        neg_variables = [-v for v in utils.to_numerical(variables, self)]
        neg_bound = len(variables) - bound
        self.add_kconstraint(neg_bound, neg_variables)
        

    def exactly_one(self, variables) -> None:
        """
        Adds an exactly-one constraint to the modeler.
        
        This constraint ensures that exactly one of the given variables is true.
        
        Args:
            variables (list): A list of variables (can be names or numbers).
            
        Returns:
            None
        """
        self.add_clauses(cardinality.CExactly(1, variables, self).to_clauses())

    def exactly_k(self, variables, k) -> None:
        """
        Adds an exactly-k constraint to the modeler.
        
        This constraint ensures that exactly k of the given variables are true.
        
        Args:
            variables (list): A list of variables (can be names or numbers).
            k (int): The number of variables that should be true.
            
        Returns:
            None
        """
        self.add_clauses(cardinality.CExactly(k, variables, self).to_clauses())

    def at_most_one(self, variables, constraint_type="3-chunks") -> None:
        """
        Adds an at-most-one constraint to the modeler.
        
        This constraint ensures that at most one of the given variables is true.
        Several encoding strategies are available, with different trade-offs between
        clause size, number of clauses, and auxiliary variables.
        
        Args:
            variables (list): A list of variables (can be names or numbers).
            constraint_type (str, optional): The encoding strategy to use. Options are:
                - "naive": Pairwise encoding (O(n²) clauses, no auxiliary variables)
                - "bin-tree": Binary tree encoding
                - "3-chunks": Commander encoding with chunks of size 3 (default)
                - Any other value: Commander encoding with optimal chunk size
            
        Returns:
            None
        """
        if constraint_type == "naive":
            self.add_clauses(cardinality.CAtMostOne(variables, self).to_clauses_naive())
        elif constraint_type == "bin-tree":
            self.add_clauses(cardinality.CAtMostOne(variables, self).to_clauses_2())
        elif constraint_type == "3-chunks":
            self.add_clauses(cardinality.CAtMostOne(variables, self).to_clauses())
        else:
            self.add_clauses(cardinality.CAtMostOne(variables, self).to_clauses_o())

    def at_most_k(self, variables, k) -> None:
        """
        Adds an at-most-k constraint to the modeler.
        
        This constraint ensures that at most k of the given variables are true.
        
        Args:
            variables (list): A list of variables (can be names or numbers).
            k (int): The maximum number of variables that can be true.
            
        Returns:
            None
            
        Note:
            If k >= len(variables), the constraint is vacuously true and nothing is added.
        """
        if k >= len(variables):
            return  # nothing to enforce in this case; it's vacuously true
        # print("entering at most k")
        # print(f"len vars = {len(variables)}, k = {k}")
        self.add_clauses(cardinality.CAtMost(k, variables, self).to_clauses())
        # print("exiting at most k")

    def at_least_k(self, variables, k) -> None:
        """
        Adds an at-least-k constraint to the modeler.
        
        This constraint ensures that at least k of the given variables are true.
        The implementation uses the duality between at-least-k and at-most-k constraints:
        at-least-k(vars) is equivalent to at-most-(n-k)(-vars).
        
        Args:
            variables (list): A list of variables (can be names or numbers).
            k (int): The minimum number of variables that must be true.
            
        Returns:
            None
            
        Note:
            For k=1, a more efficient encoding might be available.
        """
        if k == 1:
            print("warning: inefficiency in the encoding! at_least_k with k=1 is better encoded as a single clause")

        # sum_{v in variables} v >= k
        # sum_{v in variables} -v <= |variables| - k
        num_variables = utils.to_numerical(variables, self)
        neg_variables = [-var for var in num_variables]
        self.at_most_k(neg_variables, len(variables) - k)

    def lex_less_equal(self, seq1, seq2, max_comparisons=None) -> None:
        """
            Ensure that seq1 is lexicographically smaller or equal than seq2
            Assumes the sequences are of the same length.
        
        """
        assert len(seq1) == len(seq2)

        seqVars1 = utils.to_numerical(seq1, self)
        seqVars2 = utils.to_numerical(seq2, self)

        v_name = f"_lex_{self.n_vars()+1}"
        self.add_var(v_name)
        all_previous_equal = self.v(v_name)
        self.add_clause([all_previous_equal])
        cnt_supp = 0
        cnt_skip = 0
        if max_comparisons is None:
            max_comparisons = len(seqVars1) 
        for i in range(len(seqVars1)):
            if cnt_supp >= max_comparisons:
                break
                # pass
            if seqVars1[i] == seqVars2[i]:
                cnt_skip += 1
                continue
            self.add_clause([-all_previous_equal, -seqVars1[i], +seqVars2[i]]) # all previous equal implies seq1[i] <= seq2[i]
            cnt_supp += 1
            vname_new = f"_lex_{self.n_vars()+1}"
            self.add_var(vname_new)
            all_previous_equal_new = self.v(vname_new)
            self.add_clause([-all_previous_equal, -seqVars1[i], +all_previous_equal_new])
            self.add_clause([-all_previous_equal, +seqVars2[i], +all_previous_equal_new])
            all_previous_equal = all_previous_equal_new

    def serialize(self, basename) -> None:
        """
        Serializes the modeler to a file.
        
        This is a convenience method that calls serialize_encoding with the given basename.
        
        Args:
            basename (str): The base filename to use for serialization.
            
        Returns:
            None
        """
        self.serialize_encoding(basename)
        
    def serialize_debug(self, filename) -> None:
        """
        Serializes the modeler to a file in DIMACS CNF format for debugging purposes.
        
        Args:
            filename (str): The filename to write to.
            
        Returns:
            None
            
        Note:
            This method is only supported for CNF formulas (not MaxSAT or QBF).
        """
        # only supported for cnf right now
        max_var = self.max_var_number()
        clauses = self._clauses
        with open(filename, "w", encoding="utf-8") as file:
            file.write(f"p cnf {max_var} {len(clauses)}\n")
            for clause in clauses:
                file.write(" ".join(map(str, clause)) + " 0\n")
            

    def serialize_encoding(self, filename, clauses=None, use_all_vars=True) -> None:
        """
        Serializes the encoding part of the modeler to a file in the appropriate format.
        
        The format depends on the type of formula:
        - CNF: Standard DIMACS CNF format
        - MaxSAT: DIMACS WCNF format (> 2022 format)
        - With k-constraints: KNF format
        - QBF: QDIMACS format
        
        Args:
            filename (str): The filename to write to.
            clauses (list, optional): The clauses to serialize. If None, uses all clauses in the modeler.
            
        Returns:
            None
        """
        if clauses is None:
            clauses = self._clauses
        knf_constraints = self._gconstraints + self._kconstraints
        
       
        max_var = self.max_var_number()
        if use_all_vars:
            max_var = max(max_var, len(self._varmap))

        with open(filename, "w", encoding="utf-8") as file:
            if self._max_sat:
                top = len(clauses) + 1  # not entirely sure about this yet.
                file.write(f"c p wcnf {max_var} {len(clauses)} {top}\n")
                for clause in clauses:
                    clause_weight = (
                        'h' if self._clause_weights[tuple(clause)] == "HARD" else self._clause_weights[tuple(clause)]
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
                clause_lines = (f"{' '.join(map(str, cl))} 0\n" for cl in clauses)
                file.writelines(clause_lines)

    def max_var_number(self) -> int:
        """
        Returns the maximum variable number used in any clause.
        
        This is used for serialization to determine the number of variables to declare
        in the formula header.
        
        Returns:
            int: The maximum variable number used in any clause, or 0 if there are no clauses.
        """
        mx = 0
        for clause in self._clauses:
            if len(clause):
                mx = max(mx, *[abs(lit) for lit in clause])
        return mx
    
    def unit_propagate(self) -> None:
        """
        Performs unit propagation on the modeler.
        
        """
        while True:
            unit_clauses = [clause for clause in self._clauses if len(clause) == 1]
            if not unit_clauses:
                break
            units = [clause[0] for clause in unit_clauses]
            new_clauses = []
            for clause in self._clauses:
                stays = True
                for unit in units:
                    if -unit in clause:
                        clause.remove(-unit)
                    if unit in clause:
                        stays = False
                if stays:
                    new_clauses.append(clause)
            self._clauses = new_clauses

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

    def solve_and_decode(self, output_builder, solver="kissat", multiplicity=1) -> tuple[str, int]:
        lit_valuation = {}
        self.serialize(constants.TMP_FILENAME)
        output, return_code = utils.system_call([solver, constants.TMP_FILENAME])
        if return_code != 10:
            print(
                f"return code = {return_code}, UNSAT formula does not allow decoding."
            )
            return output, return_code
        
        print(f"Got a solution! {multiplicity-1} remaining... ")
            
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
        neg_clause = []
        for lit_name, (lit, _) in self._varmap.items():
            sem_valuation[lit_name] = lit_valuation[lit]
            neg_clause.append(-lit if lit_valuation[lit] else lit)
            
        if multiplicity > 1:
            print(f"Adding negated clause {neg_clause} to the modeler")
            self.add_clause(neg_clause)
            self.solve_and_decode(output_builder, solver, multiplicity - 1)
            

        # for sem_name, sem_var in self._semvars.items():
        #     sem_valuation[sem_name] = OrderIntervalValuation(sem_var, lit_valuation)
        result = output_builder(sem_valuation)
        return output, return_code, result
        
    def solve(self, solver="kissat", timeout=None) -> SolverOutput:
        """
        Solves the current formula using an external SAT solver.
        
        This method serializes the current formula to a temporary file,
        calls an external SAT solver, and returns a SolverOutput object
        containing the result and variable assignments if the formula is satisfiable.
        
        Args:
            solver (str, optional): The SAT solver to use. Defaults to "kissat".
            timeout (int, optional): Maximum time in seconds to run the solver. Defaults to None (no timeout).
            
        Returns:
            SolverOutput: An object containing the result (SAT/UNSAT/UNKNOWN) and
                         variable assignments if the formula is satisfiable.
        """
        lit_valuation = {}
        self.serialize(constants.TMP_FILENAME)
        output, return_code = utils.system_call([solver, constants.TMP_FILENAME], timeout=timeout)
        if return_code == 20:
            return SolverOutput(solver, "UNSAT", None)
           
        if return_code != 10:
            return SolverOutput(solver, f"UNKNOWN with return code {return_code}, output = {output}", None)
            
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
            
        return SolverOutput(solver, "SAT", sem_valuation)

    def solve_with_proof(self, timeout=None):
        """
        Solves the formula with proof generation and returns the proof.
        
        This method calls the kissat SAT solver with proof generation enabled,
        and returns the proof in DRAT format along with the elapsed time.
        
        Args:
            timeout (int, optional): Maximum time in seconds to run the solver. Defaults to None (no timeout).
            
        Returns:
            tuple: A tuple containing:
                - list: The proof as a list of clause additions/deletions
                - float: The elapsed time in seconds
        """
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
                    lit_map[abs(int(token))] = (int(token) > 0)

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

            # raise NotImplementedError("Debugging UNSAT formulas is not implemented yet")
            # minimize unsat core naively.
            # let's try to remove clauses one by one and see if the formula is still unsat.
            clauses = self._clauses
            while True:
                for i in range(len(clauses)):
                    t_clauses = clauses[:i] + clauses[i + 1:]
                    self.serialize_encoding("tmp.cnf", t_clauses)
                    output, return_code = utils.system_call(["kissat", "tmp.cnf"])
                    if return_code == 20:
                        print(f"Removed clause {i}, {len(clauses)} remaining ")
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
            
    def evaluate(self, model):
        """
        Evaluates the modeler with a given model.
        
        This method checks if the model satisfies all clauses in the modeler.
        
        Args:
            model (dict): A dictionary mapping variable names to their boolean values.
            
        Returns:
            bool: True if the model satisfies all clauses, and the first falsified clause otherwise.
        """
        def lit_satisfied(lit):
            if lit > 0:
                return model[self.lit_to_str(lit)]
            else:
                return not model[self.lit_to_str(-lit)]
        for clause in self._clauses:
            if not any(lit_satisfied(lit) for lit in clause):
                return False, clause
        return True, None
        

    def print_clause(self, clause):
        print([self.lit_to_str(lit) for lit in clause])

    def clause_as_str(self, clause):
        numerical_clause = utils.to_numerical(clause, self)
        return str([self.lit_to_str(lit) for lit in numerical_clause])

    def print_clauses(self, clauses=None) -> None:
        if clauses is None:
            clauses = self._clauses
        for clause in clauses:
            self.print_clause(clause)
