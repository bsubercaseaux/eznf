from eznf import modeler

def forall_exists_encodings(universal_encoding, existential_encoding):
    """
    Merge the universal and existential encodings into a single encoding
    """
    Z = modeler.Modeler()
    for var in universal_encoding.get_vars():
        vname, _, vdesc = var
        Z.add_universal_var(vname, vdesc)

    universal_clauses = universal_encoding.get_clauses(no_dups=True)
    existential_clauses = existential_encoding.get_clauses(no_dups=True)   
    
    def f_var(clause):
        return f"__f_{clause}"
    
    for clause in universal_clauses:
        Z.add_existential_var(f_var(clause))
        Z.add_clause([-Z.v(f_var(clause))] + clause)
        for var in clause:
            Z.add_clause([Z.v(f_var(clause)), -var])

    for var in existential_encoding.get_vars():
        vname, _, vdesc = var
        if not Z.has_var(vname):
            Z.add_existential_var(vname, vdesc)

    negative_universal_vars = [-Z.v(f_var(c)) for c in universal_clauses]
    for i, clause in enumerate(existential_clauses):
        print(f"existential clause {i}", end="\r")
        converted_clause = [existential_encoding.lit_to_str(lit) for lit in clause]
        fclause = converted_clause + negative_universal_vars
        Z.add_clause(fclause)
    print('\n')

    return Z
