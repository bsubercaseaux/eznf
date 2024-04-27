from typing import List
from eznf import sem_cnf


class OrderInterval:
    def __init__(self, modeler, name, description, interval, active_length) -> None:
        self._name = name
        self._description = description
        self._interval = interval
        self.max_vars = []
        self.min_vars = []

        for i in range(interval[0], interval[1]):
            modeler.add_var(
                f"__max_interval:{name}_{i}",
                f"{i}-th variable of the max-order-interval encoding for {name}",
            )
            modeler.add_var(
                f"__min_interval:{name}_{i}",
                f"{i}-th variable of the min-order-interval encoding for {name}",
            )

            self.max_vars.append(modeler.v(f"__max_interval:{name}_{i}"))
            self.min_vars.append(modeler.v(f"__min_interval:{name}_{i}"))

        for i in range(interval[0], interval[1]):

            if i > interval[0]:
                # max: 1 at pos i implies 1 at pos i-1
                modeler.add_clause([-self.max_vars[i], self.max_vars[i - 1]])
            if i + 1 < interval[1]:
                # min: 1 at pos i implies 1 at pos i+1
                modeler.add_clause([-self.min_vars[i], self.min_vars[i + 1]])

        # given j >= active_length-1
        # max must be true until active_length - 1
        # given i + active_length < interval[1]
        # min must be activel at interval[1] - active_length
        if isinstance(active_length, int):
            modeler.add_clause([self.max_vars[active_length - 1]])
            modeler.add_clause([self.min_vars[interval[1] - active_length]])
        else:
            # active_length is a functional variable.
            # active_length = (var, if_true, if_false)
            variable, if_true, if_false = active_length
            modeler.add_clause([-modeler.v(variable), self.max_vars[if_true - 1]])
            modeler.add_clause([modeler.v(variable), self.max_vars[if_false - 1]])
            modeler.add_clause(
                [-modeler.v(variable), self.min_vars[interval[1] - if_true]]
            )
            modeler.add_clause(
                [modeler.v(variable), self.min_vars[interval[1] - if_false]]
            )

        # active range restrictions
        # range [i, j] <-> min is true from i, max is true until j
        # min[i] -> range starts at most at i
        #        -> range ends at most at i+active_length-1
        #        -> max[i+active_length] is false
        # ~min[i] -> range starts at least at i+1
        #         -> range ends at least at i+active_length
        #        -> max[i+active_length] is true
        if isinstance(active_length, int):
            for i in range(interval[0], interval[1]):
                if i + active_length < interval[1]:
                    modeler.add_clause(
                        [-self.min_vars[i], -self.max_vars[i + active_length]]
                    )
                    modeler.add_clause(
                        [self.min_vars[i], self.max_vars[i + active_length]]
                    )
        else:
            variable, if_true, if_false = active_length
            for i in range(interval[0], interval[1]):
                if i + if_true < interval[1]:
                    modeler.add_clause(
                        [
                            -modeler.v(variable),
                            -self.min_vars[i],
                            -self.max_vars[i + if_true],
                        ]
                    )
                    modeler.add_clause(
                        [
                            -modeler.v(variable),
                            self.min_vars[i],
                            self.max_vars[i + if_true],
                        ]
                    )
                if i + if_false < interval[1]:
                    modeler.add_clause(
                        [
                            modeler.v(variable),
                            -self.min_vars[i],
                            -self.max_vars[i + if_false],
                        ]
                    )
                    modeler.add_clause(
                        [
                            modeler.v(variable),
                            self.min_vars[i],
                            self.max_vars[i + if_false],
                        ]
                    )

    def contains(self, index) -> List[int]:
        return sem_cnf.SemCNF(
            [
                sem_cnf.SemClause([self.min_vars[index]]),
                sem_cnf.SemClause([self.max_vars[index]]),
            ]
        )


class OrderIntervalValuation:
    def __init__(self, order_interval, lit_valuation) -> None:
        self._order_interval = order_interval
        self._lit_valuation = lit_valuation
        self.active_range = []
        for index in range(order_interval._interval[0], order_interval._interval[1]):
            if (
                self._lit_valuation[order_interval.min_vars[index]]
                and self._lit_valuation[order_interval.max_vars[index]]
            ):
                self.active_range.append(index)
