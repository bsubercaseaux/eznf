from eznf import modeler
import time


def test_variable_addition():
    Z = modeler.Modeler()
    Z.add_var("x", "x")
    assert Z.v("x") == 1


def test_qbf_basic_encoding():
    Z = modeler.Modeler()
    Z.add_existential_var("x")
    Z.add_universal_var("y")
    assert Z.v("y") == 2


def test_parser():
    Z = modeler.Modeler()
    Z.add_var("x")
    Z.add_var("y")

    ti = time.perf_counter_ns()
    for _ in range(1000):
        Z.constraint("x <-> (y <-> x)")
    tf = time.perf_counter_ns()
    elapsed = (tf - ti)/1e9
    print(f"elapsed time = {elapsed} seconds")
    assert Z.n_vars() == 2
    
def test_basics():
    Z = modeler.Modeler()
    Z.add_var("x")
    Z.add_clause(["x"])
    output = Z.solve()
    assert output.is_SAT()
    Z.add_clause(["-x"])
    output2 = Z.solve()
    assert output2.is_UNSAT()
    Z.remove_clause(["-x"])
    output3 = Z.solve()
    assert output3.is_SAT()
    sol = output3.get_solution()
    assert sol["x"]


def test_cardinality():
    Z = modeler.Modeler()
    Z.add_var("x")
    Z.add_var("y")
    Z.add_var("z")
    Z.add_var("w")
    Z.exactly_k(["x", "y", "z", "w"], 2)
    output = Z.solve()
    assert output.is_SAT()
    sol = output.get_solution()
    assert sol["x"] + sol["y"] + sol["z"] + sol["w"] == 2
    
    
def test_cardinality_contra():
    Z = modeler.Modeler()
    Z.add_var("x")
    Z.add_var("y")
    Z.add_var("z")
    Z.add_var("w")
    Z.at_most_k(["x", "y", "z", "w"], 2)
    Z.at_least_k(["x", "y", "z", "w"], 3)
    output = Z.solve()
    assert not output.is_SAT()
    
def test_cardinality_more():
    Z = modeler.Modeler()
    for i in range(200):
        Z.add_var(f"x{i}")
    Z.exactly_k([f"x{i}" for i in range(200)], 100)
    output = Z.solve()
    assert output.is_SAT()
    sol = output.get_solution()
    assert sum([sol[f"x{i}"] for i in range(200)]) == 100