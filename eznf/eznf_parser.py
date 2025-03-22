# Import Lark library for parsing
from lark import Lark, Transformer

# Lark grammar definition
GRAMMAR = r"""
?expression: literal
           | "not" expression  -> not_
           | expression ("<=>" | "<->") expression  -> iff
           | expression ("and" | "&" | "&&" | "^") expression  -> and_
           | expression ("or" | "|" | "||" | "v") expression  -> or_
           | expression ("->" | "=>") expression  -> implies
           | "(" expression ")"

variable: VARNAME "(" arg_list? ")"  -> var_with_args
        | VARNAME

arg_list: /[0-9]+/ ("," /[0-9]+/) *

literal: "-" variable  -> neg_var
       | variable

VARNAME: /[a-zA-Z_][a-zA-Z0-9_]*(?:_[a-zA-Z0-9_]+)?/

%import common.WS
%ignore WS
"""


# Parsing classes from your provided code
class Variable:
    def __init__(self, parse_results):
        self.var = parse_results
        self.head = self.var[0]
        self.tail = []
        if len(self.var) > 1:
            self.tail = self.var[1]

    def __repr__(self) -> str:
        if self.tail:
            return f"{self.head}({', '.join(self.tail)})"
        return str(self.head)

    def to_cls(self):
        return [[str(self)]]


class Literal:
    def __init__(self, args):
        self.negated = False
        self.var = args[0]
        if args[0] == "-":
            self.var = args[1]
            self.negated = True

    def __repr__(self):
        if self.negated:
            return f"-{self.var}"
        return str(self.var)

    def negation(self):
        if self.negated:
            return Literal([self.var])
        else:
            return Literal(["-", self.var])

    def to_cls(self):
        return [[str(self)]]


class Not:
    def __init__(self, child):
        self.child = child

    def __repr__(self):
        return f"(Not {str(self.child)})"

    def to_cls(self):
        if isinstance(self.child, Literal):
            return self.child.negation().to_cls()

        if isinstance(self.child, Iff):
            l1 = self.child.left
            r1 = self.child.right
            if isinstance(l1, Literal) and isinstance(r1, Literal):
                return [[str(l1), str(r1)], [str(l1.negation()), str(r1.negation())]]
        raise NotImplementedError(
            f"Tseint transformation not yet implemented for {self.child}"
        )


class And:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __repr__(self):
        return f"(And {str(self.left)} {str(self.right)})"

    def to_cls(self):
        # print("And to cls")
        # print(f"self.left = {self.left}, type = {type(self.left)}")
        # print(f"self.right = {self.right}, type = {type(self.right)}")
        # left_cls = self.left.to_cls()
        # # print("left cls", left_cls)
        # right_cls = self.right.to_cls()
        # print("right_cls", right_cls)
        return self.left.to_cls() + self.right.to_cls()


class Or:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __repr__(self):
        return f"(Or {str(self.left)} {str(self.right)})"

    def to_cls(self):
        # print("Or to cls")
        left_cls = self.left.to_cls()
        right_cls = self.right.to_cls()
        ans = []
        def negated(literal):
            if literal[0] == "-" or literal[0] == "~":
                return literal[1:]
            else: return f'-{literal}'
            
        for l_cls in left_cls:
            for r_cls in right_cls:
                # check if complementary literals
                tautological = any(negated(lit) in r_cls for lit in l_cls)
                if not tautological:
                    ans.append(l_cls + r_cls)
                    
        return ans


class Implies:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __repr__(self):
        return f"(Implies {str(self.left)} {str(self.right)})"

    def to_cls(self):
        right_cls = self.right.to_cls()
        if isinstance(self.left, Literal):
            negated_left = self.left.negation()
            return [[str(negated_left)] + right_clause for right_clause in right_cls]
        elif isinstance(self.left, Or):
            l1 = Implies(self.left.left, self.right)
            l2 = Implies(self.left.right, self.right)
            return l1.to_cls() + l2.to_cls()
        elif isinstance(self.left, And):
            return Or(
                Or(Not(self.left.left), Not(self.left.right)), self.right
            ).to_cls()

        elif isinstance(self.left, Implies):
            # (a->b) -> c
            obj = Or(And(self.left.left, Not(self.left.right)), self.right)
            print(type(obj), obj)
            return Or(And(self.left.left, Not(self.left.right)), self.right).to_cls()

        elif isinstance(self.left, Iff):
            # (A <-> B) -> C
            # = (A ^ -B) v (-A ^ B) v C
            # print("self.left", self.left)
            # print("self.right", self.right)
            # print("self.left.left", self.left.left)
            # print("self.left.right", self.left.right.to_cls())
            # print("And(self.left.left, Not(self.left.right)))", And(self.left.right, Not(self.left.left)).to_cls())
            # print("And(self.left.right, Not(self.left.left))", And(self.left.right, Not(self.left.left)).to_cls())
            # print("Or(And(self.left.left, Not(self.left.right)), And(self.left.right, Not(self.left.left)))", Or(And(self.left.left, Not(self.left.right)), And(self.left.right, Not(self.left.left))).to_cls())
            return Or(Or(And(self.left.left, Not(self.left.right)), And(self.left.right, Not(self.left.left))), self.right).to_cls()
            
            # return And(
            #     Or(And(self.left.left, Not(self.left.right)), self.right),
            #     Or(And(self.left.right, Not(self.left.left)), self.right),
            # ).to_cls()
            # (a <-> b) -> c
            # a ^ {-b} -> c
            #
        else:
            raise NotImplementedError(
                f"Implies not implemented for this case: {self.left}, {self.right}"
            )


class Iff:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __repr__(self):
        return f"(Iff {str(self.left)} {str(self.right)})"

    def to_cls(self):
        forward = Implies(self.left, self.right)
        backward = Implies(self.right, self.left)
        return forward.to_cls() + backward.to_cls()


# Transformer class for Lark
class MyTransformer(Transformer):
    def var_with_args(self, items):
        var_name = items[0].value  # Get the variable name as a string
        args = items[1] if len(items) > 1 else []  # Use the argument list directly
        return Variable([var_name, args])

    def arg_list(self, items):
        return [str(item) for item in items]

    def variable(self, items):
        return Variable([items[0]])

    def neg_var(self, items):
        return Literal(["-", items[0]])

    def literal(self, items):
        return Literal(items)

    def not_(self, items):
        return Not(items[0])

    def and_(self, items):
        return And(items[0], items[1])

    def or_(self, items):
        return Or(items[0], items[1])

    def implies(self, items):
        return Implies(items[0], items[1])

    def iff(self, items):
        return Iff(items[0], items[1])


# Lark parser instance
parser = Lark(GRAMMAR, start="expression", parser="lalr")


# Function to convert string to clauses using Lark
def str_to_clauses(str_constraint):
    try:
        tree = parser.parse(str_constraint)
        transformed = MyTransformer().transform(tree)
        # print(transformed)
        clauses = transformed.to_cls()
        return clauses
    except Exception as err:
        print(f" Parsing error! {err}")


# Example usage
REPL_DEBUG_LOOP = False

while REPL_DEBUG_LOOP:
    high_query = input("(query) > ")
    if high_query in ["q", "quit", "exit"]:
        print("bye!")
        break
    clauses = str_to_clauses(high_query)
    for clause in clauses:
        print("clause: ", clause)
