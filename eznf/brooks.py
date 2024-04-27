from eznf import modeler
import itertools
from eznf import universal_existential_form
import sys

N = int(sys.argv[1])


def brooks(N):
    U = modeler.Modeler()
    E = modeler.Modeler()
    node_vars = {}
    for u in range(N):
        node_vars[u] = []

    for u in range(N):
        for v in range(u+1, N):
            U.add_var(f"e_{u, v}")
            node_vars[u].append(U.v(f"e_{u, v}"))
            node_vars[v].append(U.v(f"e_{u, v}"))

    # connectedness
    for u in range(1, N):
        U.add_clause([f"e_{v, u}" for v in range(u)])

    # for u in range(N):
    #     U.exactly_k(node_vars[u], 3)
    # at most 3
    for u in range(N):
        for quadruple in itertools.combinations(node_vars[u], 4):
            U.add_clause([-q for q in quadruple])

    # at least 3
    for u in range(N):
        for cset in itertools.combinations(node_vars[u], len(node_vars[u])-2):
            U.add_clause([c for c in cset])

    colors = ['r', 'g', 'b']
    for u in range(N):
        for c in colors:
            E.add_var(f"{c}_{u}")
        E.add_clause([f"{c}_{u}" for c in colors])
        for v in range(u+1, N):
            E.add_var(f"e_{u, v}")

    for u in range(N):
        for v in range(u+1, N):
            for c in colors:
                E.add_clause([f"-e_{u, v}", f"-{c}_{u}", f"-{c}_{v}"])

    final_enc = universal_existential_form.forall_exists_encodings(U, E)
    return final_enc


enc = brooks(N)
enc.serialize(f"brooks-{N}.cnf")
