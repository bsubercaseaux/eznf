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
