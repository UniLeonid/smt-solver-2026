from z3 import *
from common import check_formulas, Solver_test_files


def array_to_euf(formulas):
    """
    Реализуйте: по списку формул над EUF и массивами без равенств массивов верните эквивыполнимый
    список формул в EUF — без термов сорта массив (в частности, без `select` и `store`).

    Полезное из API z3: `is_select(t)`, `is_store(t)`, `t.arg(i)`, `Select(A, y)`, `If(c, a, b)`,
    `Function(name, *sorts)`, `A.domain()`, `A.range()`
    """
    functions = {}
    cache = {}

    def unwrap(A, index):
        key = (A.get_id(), index.get_id())

        out = cache.get(key, None)
        if out is None:
            if is_store(A):
                array, store_index, value = A.arg(0), A.arg(1), A.arg(2)

                out = If(store_index == index, value, unwrap(array, index))
            else:
                if A.get_id() not in functions:
                    functions[A.get_id()] = Function(f"array_{A}", A.domain(), A.range())

                out = functions[A.get_id()](index)

            cache[key] = out

        return out

    def replace(term):
        if is_select(term):
            return unwrap(term.arg(0), term.arg(1))
        return term

    result = []
    for formula in formulas:
        result.append(rewrite(formula, replace))
    return result


def rewrite(e, f):
    """Применяет `f` ко всем подтермам `e` снизу вверх: сначала к аргументам, затем к терму с уже переписанными аргументами"""
    memo = {}

    def go(t):
        if t.get_id() not in memo:
            if is_app(t) and t.num_args() > 0:
                memo[t.get_id()] = f(t.decl()(*[go(c) for c in t.children()]))
            else:
                memo[t.get_id()] = f(t)
        return memo[t.get_id()]

    return go(e)


def subterms(formulas):
    seen, result = set(), []

    def go(t):
        if t.get_id() not in seen:
            seen.add(t.get_id())
            result.append(t)
            for c in t.children():
                go(c)

    for f in formulas:
        go(f)
    return result


class ArrayToEufSolver:
    def __init__(self):
        self.formulas = []

    def add(self, *formulas):
        self.formulas += formulas

    def check(self):
        result = list(array_to_euf(self.formulas))
        arrays = [t for t in subterms(result) if is_array(t)]
        assert not arrays, f"В результате остались массивы: {arrays[0]}"
        solver = Solver()
        solver.add(result)
        return solver.check()


def array_to_euf_test_lecture():
    S = DeclareSort('S')
    A = Array('A', S, S)
    x, y, z, v, w, x1, x2, v1, v2 = Consts('x y z v w x1 x2 v1 v2', S)
    check_formulas(ArrayToEufSolver, [x == y, x != z, Select(Store(Store(A, x, v), z, w), y) != v], unsat)
    check_formulas(ArrayToEufSolver, [Select(A, x) == Select(A, y), x != y], sat)
    check_formulas(ArrayToEufSolver, [A[A[A[x]]] == x, A[A[A[A[A[x]]]]] == x, A[x] != x], unsat)
    check_formulas(ArrayToEufSolver, [x1 == y, x1 != x2, Select(A, y) == v1,
                                      Select(Store(Store(A, x1, v1), x2, v2), y) != Select(A, y)], unsat)


def array_to_euf_test_bool():
    S = DeclareSort('S')
    A = Array('A', S, S)
    x, y, v, w = Consts('x y v w', S)
    check_formulas(ArrayToEufSolver, [Implies(Select(Store(A, x, v), y) == v, x == y), Select(A, y) == v, x != y], unsat)
    check_formulas(ArrayToEufSolver, [Or(Select(Store(A, x, v), y) != v, x != y), x == y], unsat)
    check_formulas(ArrayToEufSolver, [Or(Select(Store(A, x, w), y) == v, x == y), Select(A, y) == v], sat)


def array_to_euf_tests():
    array_to_euf_test_lecture()
    array_to_euf_test_bool()
    Solver_test_files(ArrayToEufSolver, list, "QF_AX")


if __name__ == "__main__":
    array_to_euf_tests()
    print("OK")
