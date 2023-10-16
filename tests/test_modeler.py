from eznf import modeler

def test_variable_addition():
    Z = modeler.Modeler() 
    Z.add_var("x", "x")
    assert Z.v("x") == 1