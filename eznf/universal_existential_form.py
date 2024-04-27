import modeler

def forall_exists_encodings(universal_encoding, existential_encoding):
    """
    Merge the universal and existential encodings into a single encoding
    """
    Z = modeler.Modeler()
    for var in universal_encoding.get_vars():
        vname, _, vdesc = var
        Z.add_universal_var(vname, vdesc)

    for clause in universal_encoding.get_clauses():
        Z.add_existential_var(f"__f_{clause}")
        Z.add_clause([-Z.v(f"__f_{clause}")] + clause)
        for var in clause:
            Z.add_clause([Z.v(f"__f_{clause}"), -var])

    for var in existential_encoding.get_vars():
        vname, _, vdesc = var
        if not Z.has_var(vname):
            Z.add_existential_var(vname, vdesc)

    for clause in existential_encoding.get_clauses():
        converted_clause = [existential_encoding.lit_to_str(lit) for lit in clause]
        fclause = converted_clause + [-Z.v(f"__f_{c}") for c in universal_encoding.get_clauses()]
        Z.add_clause(fclause)

    return Z
