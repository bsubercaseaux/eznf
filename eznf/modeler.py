class Modeler:
    def __init__(self) -> None:
        self._varmap = {}
        self._clauses = []
        self._semvars = {}
        
    def add_var(self, name, description="no description") -> None:
        self._varmap[name] = (len(self._varmap) + 1, description)
        
    def add_svar(self, name, description, semantic_type, **kwargs) -> None:
        if semantic_type == "ORDER_INTERVAL":
            assert "interval" in kwargs
            self._semvars[name] = OrderInterval(self, name, description, kwargs["interval"], kwargs["active_length"])
        
    def add_sclause(self, sclause) -> None:
        self.add_clauses(sclause.to_clauses())
        
    def v(self, name) -> int:
        return self._varmap[name][0]
        
    def interval_contains(self, name, value) -> int:
        order_interval = self._semvars[name]
        return order_interval.contains(value)
            
        
    def add_clause(self, clause) -> None:
        self._clauses.append(clause)
        
    def add_clauses(self, clauses) -> None:
        for clause in clauses:
            self._clauses.append(clause)
        
    def serialize(self, basename) -> None:
        self.serialize_encoding(basename + ".cnf")
        self.serialize_decoder(basename + ".dec")
        
    def serialize_encoding(self, filename) -> None:
        with open(filename, 'w') as file:
            file.write("p cnf {} {}\n".format(len(self._varmap), len(self._clauses)))
            for clause in self._clauses:
                file.write(" ".join(map(str, clause)) + " 0\n")
    
    def serialize_decoder(self, filename) -> None:
        pass
        
    def decode(self, sol_filename, output_builder) -> str:
        lit_valuation = {}
        with open(sol_filename, 'r') as sol:
            for line in sol:
                if line[0] == 'v':
                    tokens = line[:-1].split(' ') # skip newline
                    relevant_tokens = tokens[1:]
                    for token in relevant_tokens:
                        int_token = int(token)
                        if int_token == 0:
                            continue
                        lit_valuation[abs(int_token)] = int_token > 0
        sem_valuation = {}
        for lit_name, (lit, _) in self._varmap.items():
            sem_valuation[lit_name] = lit_valuation[lit]
            
        for sem_name, sem_var in self._semvars.items():
            sem_valuation[sem_name] = OrderIntervalValuation(sem_var, lit_valuation)
        return output_builder(sem_valuation)
                    
        
        
class OrderInterval:
    def __init__(self, modeler, name, description, interval, active_length) -> None:
        self._name = name
        self._description = description
        self._interval = interval
        self.max_vars = []
        self.min_vars = []
        
        for i in range(interval[0], interval[1]):
            modeler.add_var(f"__max_interval:{name}_{i}", f"{i}-th variable of the max-order-interval encoding for {name}")
            modeler.add_var(f"__min_interval:{name}_{i}", f"{i}-th variable of the min-order-interval encoding for {name}")
            
            self.max_vars.append(modeler.v(f"__max_interval:{name}_{i}"))
            self.min_vars.append(modeler.v(f"__min_interval:{name}_{i}"))
            
        for i in range(interval[0], interval[1]):
            
            if i > interval[0]:
                # max: 1 at pos i implies 1 at pos i-1
                modeler.add_clause([-self.max_vars[i], self.max_vars[i-1]])
            if i+1 < interval[1]:
                # min: 1 at pos i implies 1 at pos i+1
                modeler.add_clause([-self.min_vars[i], self.min_vars[i+1]])
                
        # given j >= active_length-1
        # max must be true until active_length - 1
        # given i + active_length < interval[1]
        # min must be activel at interval[1] - active_length
        if isinstance(active_length, int):
            modeler.add_clause([self.max_vars[active_length-1]])
            modeler.add_clause([self.min_vars[interval[1]-active_length]])
        else:
            # active_length is a functional variable. 
            # active_length = (var, if_true, if_false)
            variable, if_true, if_false = active_length
            modeler.add_clause([-modeler.v(variable), self.max_vars[if_true-1]])
            modeler.add_clause([modeler.v(variable), self.max_vars[if_false-1]])
            modeler.add_clause([-modeler.v(variable), self.min_vars[interval[1]-if_true]])
            modeler.add_clause([modeler.v(variable), self.min_vars[interval[1]-if_false]])
        
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
                    modeler.add_clause([-self.min_vars[i], -self.max_vars[i + active_length]])
                    modeler.add_clause([self.min_vars[i], self.max_vars[i + active_length]])
        else:
            variable, if_true, if_false = active_length
            for i in range(interval[0], interval[1]):
                if i + if_true < interval[1]:
                    modeler.add_clause([-modeler.v(variable), -self.min_vars[i], -self.max_vars[i + if_true]])
                    modeler.add_clause([-modeler.v(variable), self.min_vars[i], self.max_vars[i + if_true]])
                if i + if_false < interval[1]:
                    modeler.add_clause([modeler.v(variable), -self.min_vars[i], -self.max_vars[i + if_false]])
                    modeler.add_clause([modeler.v(variable), self.min_vars[i], self.max_vars[i + if_false]])
                    
                                        
    def contains(self, index) -> [int]:
        return SemCNF([SemClause([self.min_vars[index]]), 
                        SemClause([self.max_vars[index]])])
        
    
class OrderIntervalValuation:
    def __init__(self, order_interval, lit_valuation) -> None:
        self._order_interval = order_interval
        self._lit_valuation = lit_valuation
        self.active_range = []
        for index in range(order_interval._interval[0], order_interval._interval[1]):
            if self._lit_valuation[order_interval.min_vars[index]] and self._lit_valuation[order_interval.max_vars[index]]:
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
            raise TypeError("SemCNF can only be initialized with a SemClause, a list of SemClauses, a SemCNF or an int")
        
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
