from typing import List
import time
from subprocess import TimeoutExpired, check_output, CalledProcessError, STDOUT

def to_numerical(clause, modeler, introduce_if_absent=False) -> List[int]:
    numerical_clause = []
    for slit in clause:
        if isinstance(slit, str):
            if slit[0] == "~" or slit[0] == "-":
                numerical_clause.append(-modeler.v(slit[1:], introduce_if_absent=introduce_if_absent))
            else:
                numerical_clause.append(modeler.v(slit, introduce_if_absent=introduce_if_absent))
        elif isinstance(slit, int):
            numerical_clause.append(slit)
        else:
            raise TypeError("Unknown type in clause", type(slit), "value", slit)
    return numerical_clause


def clause_filter(clause: List[int]) -> List[int]:
    literal_set = set(clause)
    for lit in clause:
        if -lit in literal_set:
            return "SKIP"
    # duplicates have been removed.
    # now we want to return the clause in the order of the literals
    initial_order = {}
    for i, lit in enumerate(clause):
        initial_order[lit] = i
    list_literal_set = list(literal_set)
    return sorted(list_literal_set, key=lambda x: initial_order[x])


def system_call(command, timeout=None):
    """
    params:
        command: list of strings, ex. ["ls", "-l"]
        timeout: number of seconds to wait for the command to complete.
    returns: output, return_code
    """
    try:
        output = check_output(command, stderr=STDOUT, timeout=timeout).decode()
        return_code = 0
    except CalledProcessError as e:
        output = e.output.decode()
        return_code = e.returncode
    except TimeoutExpired:
        output = f"Command timed out after {timeout} seconds"
        return_code = (
            -1
        )  # You can use any number that is not a valid return code for a success or normal failure
    return output, return_code


def timed_run_shell(commands, timeout=None):
    """
    params:
        command: list of strings, ex. ["ls", "-l"]
        timeout: number of seconds to wait for the command to complete.
    returns: output, return_code
    """
    start_time = time.perf_counter_ns()
    output, return_code = system_call(commands, timeout=timeout)
    elapsed_time = time.perf_counter_ns() - start_time
    return output, return_code, elapsed_time
