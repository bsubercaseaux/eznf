class SolverOutput:
    def __init__(self, solver, status, solution):
        self.solver = solver
        self.status = status
        self.solution = solution

    def __str__(self):
        return f'{self.solver} {self.status} {self.solution}'
        
    def is_SAT(self):
        return self.status == "SAT"
        
    def is_UNSAT(self):
        return self.status == "UNSAT"
         
    def get_solution(self):
        if self.is_SAT():
            return self.solution
        else:
            raise Exception("No solution available for instances that are not SAT")