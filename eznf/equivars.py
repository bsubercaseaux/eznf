import itertools


class EquivalenceVarPool:
    def __init__(self):
        self.ranks = {}
        self.parents = {}
        self.signs = {}  # signs[var] = sign from var to its parent

    def is_empty(self):
        return len(self.parents) == 0

    def find(self, var):
        # Handle negative input
        input_sign = 1
        if isinstance(var, str) and var.startswith('-'):
            input_sign = -1
            var = var[1:]  # Remove the '-' prefix
        
        if var not in self.parents:
            self.parents[var] = var
            self.ranks[var] = 0
            self.signs[var] = 1
            return var, input_sign
        
        # Path compression with sign accumulation
        if self.parents[var] == var:
            return var, input_sign
        
        # Recursively find root and accumulate signs
        root, parent_sign = self.find(self.parents[var])
        # Update parent and sign for path compression
        self.parents[var] = root
        self.signs[var] = self.signs[var] * parent_sign
        
        return root, self.signs[var] * input_sign

    def add_equivalence(self, var1, var2):
        """
        Add equivalence between var1 and var2.
        Supports negative variables: add_equivalence('x', '-y') means x = -y
        """
        # Parse signs from variable names
        relation_sign = 1
        
        if isinstance(var1, str) and var1.startswith('-'):
            relation_sign *= -1
            var1 = var1[1:]
        
        if isinstance(var2, str) and var2.startswith('-'):
            relation_sign *= -1
            var2 = var2[1:]
        
        v1root, sign1 = self.find(var1)
        v2root, sign2 = self.find(var2)
        
        # print(f"Adding equivalence: {var1} ({v1root}, {sign1}) <-> {var2} ({v2root}, {sign2}) with relation sign {relation_sign}")

        if v1root == v2root:
            return
        
        # Calculate the sign relationship between roots
        # We have: var1 = sign1 * v1root and var2 = sign2 * v2root
        # We want: var1 = relation_sign * var2
        # So: sign1 * v1root = relation_sign * sign2 * v2root
        # Thus: v1root = (relation_sign * sign2 / sign1) * v2root
        root_sign = relation_sign * sign2 * sign1  # sign1 is 1 or -1
        # print(f"Root sign for union: {root_sign}")


        # Use ranks to decide which becomes the parent
        if self.ranks[v1root] < self.ranks[v2root]:
            self.parents[v1root] = v2root
            self.signs[v1root] = root_sign
        elif self.ranks[v1root] > self.ranks[v2root]:
            self.parents[v2root] = v1root
            self.signs[v2root] = root_sign  # Inverse sign
        else:
            self.parents[v2root] = v1root
            self.signs[v2root] = root_sign  # Inverse sign
            self.ranks[v1root] += 1

    def get_representative(self, var):
        root, sign = self.find(var)
        return root if sign == 1 else f"-{root}"
    
    def contains_var(self, var):
        # Handle negative input
        if isinstance(var, str) and var.startswith('-'):
            var = var[1:]
        return var in self.parents


# # Example usage:
# pool = EquivalenceVarPool()

# # Now you can use negative variables directly!
# pool.add_equivalence('x', '-y')  # x = -y
# pool.add_equivalence('y', 'z')    # y = z

# print(f"get_representative('x') = {pool.get_representative('x')}")    # x
# print(f"get_representative('y') = {pool.get_representative('y')}")    # -x
# print(f"get_representative('z') = {pool.get_representative('z')}")    # -x
# print(f"get_representative('-z') = {pool.get_representative('-z')}")  # x

# # More complex example
# pool2 = EquivalenceVarPool()
# pool2.add_equivalence('-a', 'b')   # -a = b, so a = -b
# pool2.add_equivalence('b', '-c')   # b = -c
# print(f"\nget_representative('a') = {pool2.get_representative('a')}")    # a (or equivalent)
# print(f"get_representative('b') = {pool2.get_representative('b')}")      # -a (or equivalent)  
# print(f"get_representative('c') = {pool2.get_representative('c')}")      # a (or equivalent)
# print(f"get_representative('-a') = {pool2.get_representative('-a')}")    # -a (or equivalent)
# print(f"get_representative('-b') = {pool2.get_representative('-b')}")      # a (or equivalent)  
# print(f"get_representative('-c') = {pool2.get_representative('-c')}")      # -a (or equivalent)

# pool2.add_equivalence('d', 'e')  
# pool2.add_equivalence('f', 'e')  
# pool2.add_equivalence('f', 'g')  
# pool2.add_equivalence('g', 'h')  
# pool2.add_equivalence('h', '-a')  

# print(f"\nget_representative('d') = {pool2.get_representative('d')}")    # d (or equivalent)  
# print(f"get_representative('a') = {pool2.get_representative('a')}")    # -d (or equivalent)