from eznf import modeler
import time


def test_variable_addition():
    enc = modeler.Modeler()
    enc.add_var("x", "x")
    assert enc.v("x") == 1


def test_qbf_basic_encoding():
    enc = modeler.Modeler()
    enc.add_existential_var("x")
    enc.add_universal_var("y")
    assert enc.v("y") == 2


def test_parser():
    enc = modeler.Modeler()
    enc.add_var("x")
    enc.add_var("y")

    ti = time.perf_counter_ns()
    for _ in range(1000):
        enc.constraint("x <-> (y <-> x)")
    tf = time.perf_counter_ns()
    elapsed = (tf - ti)/1e9
    print(f"elapsed time = {elapsed} seconds")
    assert enc.n_vars() == 2
    
def test_basics():
    enc = modeler.Modeler()
    enc.add_var("x")
    enc.add_clause(["x"])
    output = enc.solve()
    assert output.is_SAT()
    enc.add_clause(["-x"])
    output2 = enc.solve()
    assert output2.is_UNSAT()
    enc.remove_clause(["-x"])
    output3 = enc.solve()
    assert output3.is_SAT()
    sol = output3.get_solution()
    assert sol["x"]


def test_cardinality():
    enc = modeler.Modeler()
    enc.add_var("x")
    enc.add_var("y")
    enc.add_var("z")
    enc.add_var("w")
    enc.exactly_k(["x", "y", "z", "w"], 2)
    output = enc.solve()
    assert output.is_SAT()
    sol = output.get_solution()
    assert sol["x"] + sol["y"] + sol["z"] + sol["w"] == 2
    
    
def test_cardinality_contra():
    enc = modeler.Modeler()
    enc.add_var("x")
    enc.add_var("y")
    enc.add_var("z")
    enc.add_var("w")
    enc.at_most_k(["x", "y", "z", "w"], 2)
    enc.at_least_k(["x", "y", "z", "w"], 3)
    output = enc.solve()
    assert not output.is_SAT()
    
def test_cardinality_more():
    enc = modeler.Modeler()
    for i in range(200):
        enc.add_var(f"x{i}")
    enc.exactly_k([f"x{i}" for i in range(200)], 100)
    output = enc.solve()
    assert output.is_SAT()
    sol = output.get_solution()
    assert sum([sol[f"x{i}"] for i in range(200)]) == 100


def test_lex_less_equal1():
    enc = modeler.Modeler()
    enc.add_var("x")
    enc.add_var("y")
    enc.add_clause(["-x"])
    enc.add_clause(["y"])
    enc.lex_less_equal(["x"], ["y"])
    output = enc.solve()
    assert output.is_SAT()

def test_lex_less_equal2():
    enc = modeler.Modeler()
    enc.add_var("x")
    enc.add_var("y")
    enc.add_clause(["-x"])
    enc.add_clause(["y"])
    enc.lex_less_equal(["y"], ["x"])
    output = enc.solve()
    assert output.is_UNSAT(), "This should be UNSAT, but got solution: " + str(output.get_solution())

def test_lex_less_equal3():
    enc = modeler.Modeler()
    enc.add_var("x")
    enc.add_var("y")
    enc.add_clause(["x"])
    enc.add_clause(["y"])
    enc.lex_less_equal(["x"], ["y"])
    output = enc.solve()
    assert output.is_SAT()


def test_lex_less_equal4():
    enc = modeler.Modeler()
    enc.add_var("x")
    enc.add_var("y")
    enc.add_clause(["-x"])
    enc.add_clause(["-y"])
    enc.lex_less_equal(["x"], ["y"])
    output = enc.solve()
    assert output.is_SAT()

def test_lex_less_equal5():
    enc = modeler.Modeler()
    for i in range(10):
        enc.add_var(f"x{i}")
        enc.add_var(f"y{i}")
    enc.lex_less_equal([f"x{i}" for i in range(10)], [f"y{i}" for i in range(10)])
    output = enc.solve()
    assert output.is_SAT()
    sol = output.get_solution()

    for i in range(10):
        assert sol[f"x{i}"] <= sol[f"y{i}"], "Lexicographic order violated"
        if sol[f"x{i}"] < sol[f"y{i}"]:
            break
      
        