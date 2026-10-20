from collections.abc import Callable, Iterable

from z3 import *

from common import Solver_test_files, check_formulas


def array_to_euf(formulas: list[ExprRef]) -> Iterable[ExprRef]:
    """
    Реализуйте: по списку формул над EUF и массивами без равенств массивов верните эквивыполнимый
    список формул в EUF — без термов сорта массив (в частности, без `select` и `store`).

    Полезное из API z3: `is_select(t)`, `is_store(t)`, `t.arg(i)`, `Select(A, y)`, `If(c, a, b)`,
    `Function(name, *sorts)`, `A.domain()`, `A.range()`
    """
    raise NotImplementedError()


def rewrite(e: ExprRef, f: Callable[[ExprRef], ExprRef]) -> ExprRef:
    """Применяет `f` ко всем подтермам `e` снизу вверх: сначала к аргументам, затем к терму с уже переписанными аргументами"""
    memo: dict[int, ExprRef] = {}

    def go(t: ExprRef) -> ExprRef:
        if t.get_id() not in memo:
            if is_app(t) and t.num_args() > 0:
                memo[t.get_id()] = f(t.decl()(*[go(c) for c in t.children()]))
            else:
                memo[t.get_id()] = f(t)
        return memo[t.get_id()]

    return go(e)


def subterms(formulas: Iterable[ExprRef]) -> list[ExprRef]:
    seen: set[int] = set()
    result: list[ExprRef] = []

    def go(t: ExprRef) -> None:
        if t.get_id() not in seen:
            seen.add(t.get_id())
            result.append(t)
            for c in t.children():
                go(c)

    for f in formulas:
        go(f)
    return result


class ArrayToEufSolver:
    def __init__(self) -> None:
        self.formulas: list[ExprRef] = []

    def add(self, *formulas: ExprRef) -> None:
        self.formulas += formulas

    def check(self) -> CheckSatResult:
        result = list(array_to_euf(self.formulas))
        arrays = [t for t in subterms(result) if is_array(t)]
        assert not arrays, f"В результате остались массивы: {arrays[0]}"
        solver = Solver()
        solver.add(result)
        return solver.check()


def array_to_euf_test_lecture() -> None:
    S = DeclareSort("S")
    A = Array("A", S, S)
    x, y, z, v, w, x1, x2, v1, v2 = Consts("x y z v w x1 x2 v1 v2", S)
    check_formulas(ArrayToEufSolver, [x == y, x != z, Select(Store(Store(A, x, v), z, w), y) != v], unsat)
    check_formulas(ArrayToEufSolver, [Select(A, x) == Select(A, y), x != y], sat)
    check_formulas(ArrayToEufSolver, [A[A[A[x]]] == x, A[A[A[A[A[x]]]]] == x, A[x] != x], unsat)
    check_formulas(
        ArrayToEufSolver, [x1 == y, x1 != x2, Select(A, y) == v1, Select(Store(Store(A, x1, v1), x2, v2), y) != Select(A, y)], unsat
    )


def array_to_euf_test_bool() -> None:
    S = DeclareSort("S")
    A = Array("A", S, S)
    x, y, v, w = Consts("x y v w", S)
    check_formulas(ArrayToEufSolver, [Implies(Select(Store(A, x, v), y) == v, x == y), Select(A, y) == v, x != y], unsat)
    check_formulas(ArrayToEufSolver, [Or(Select(Store(A, x, v), y) != v, x != y), x == y], unsat)
    check_formulas(ArrayToEufSolver, [Or(Select(Store(A, x, w), y) == v, x == y), Select(A, y) == v], sat)


def array_to_euf_tests() -> None:
    array_to_euf_test_lecture()
    array_to_euf_test_bool()
    Solver_test_files(ArrayToEufSolver, list, "QF_AX")


if __name__ == "__main__":
    array_to_euf_tests()
    print("OK")
