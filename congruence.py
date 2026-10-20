from z3 import *

from common import EqTheorySolver, Solver_test_files, check_formulas, linearize


class CongruenceSolver(EqTheorySolver):
    """
    Решатель для бескванторного фрагмента теории неинтерпретированных функций (QF_UF).

    Union-find и сбор подтермов уже написаны, осталось реализовать `check`.

    Полезное из API z3:
    - `t.children()` — аргументы терма (у констант — пустой список)
    - `t.decl()` — функциональный символ терма, `t.decl().get_id()` — его уникальный номер
    - `t.get_id()` — уникальный номер терма
    """

    def __init__(self) -> None:
        self.terms: dict[int, ExprRef] = {}  # номер терма -> терм; все подтермы добавленных литералов
        self.parent: dict[int, int] = {}  # union-find: номер терма -> номер родителя
        self.equalities: list[tuple[ExprRef, ExprRef]] = []  # пары термов (s, t) для литералов s = t
        self.disequalities: list[tuple[ExprRef, ExprRef]] = []  # пары термов (s, t) для литералов s != t

    def register(self, t: ExprRef) -> None:
        """Добавляет терм `t` и все его подтермы в `self.terms`"""
        if t.get_id() not in self.terms:
            self.terms[t.get_id()] = t
            self.parent[t.get_id()] = t.get_id()
            for c in t.children():
                self.register(c)

    def find(self, t: ExprRef) -> int:
        """Номер представителя класса эквивалентности терма `t`"""
        i = t.get_id()
        while self.parent[i] != i:
            i = self.parent[i]

        return i

    def union(self, s: ExprRef, t: ExprRef) -> None:
        """Сливает классы эквивалентности термов `s` и `t`"""
        self.parent[self.find(s)] = self.find(t)

    def add_equal(self, a: ExprRef, b: ExprRef) -> None:
        self.register(a)
        self.register(b)
        self.equalities.append((a, b))

    def add_distinct(self, a: ExprRef, b: ExprRef) -> None:
        self.register(a)
        self.register(b)
        self.disequalities.append((a, b))

    def merge(self) -> None:
        merged = True
        while merged:
            merged = False
            for i, f in self.terms.items():
                if not f.children():
                    continue

                for j, g in self.terms.items():
                    if i == j or not g.children() or self.find(f) == self.find(g):
                        continue

                    if f.decl() != g.decl() or len(f.children()) != len(g.children()):
                        continue

                    if all(self.find(s) == self.find(t) for s, t in zip(f.children(), g.children())):
                        self.union(f, g)
                        merged = True

    def check(self) -> CheckSatResult:
        for i in self.terms:
            self.parent[i] = i

        for s, t in self.equalities:
            self.union(s, t)

        self.merge()

        for s, t in self.disequalities:
            if self.find(s) == self.find(t):
                return unsat

        return sat


def CongruenceSolver_test1() -> None:
    S = DeclareSort("S")
    f = Function("f", S, S)
    x = Const("x", S)
    solver = CongruenceSolver()
    solver.add(f(f(x)) == x, f(f(f(x))) == x)
    assert solver.check() == sat
    solver.add(f(x) != x)
    assert solver.check() == unsat


def CongruenceSolver_test2() -> None:
    S = DeclareSort("S")
    a, b, c, d, e, s, t = Consts("a b c d e s t", S)
    f = Function("f", S, S, S)
    g = Function("g", S, S)
    check_formulas(
        CongruenceSolver,
        [a == b, b == c, d == e, b == s, d == t, f(a, g(d)) != f(g(e), b)],
        sat,
    )


def CongruenceSolver_test_lecture() -> None:
    S = DeclareSort("S")
    a, b, c, x = Consts("a b c x", S)
    f = Function("f", S, S)
    g = Function("g", S, S)
    h = Function("h", S, S, S)
    check_formulas(CongruenceSolver, [a == b, b == c, f(a) != f(c)], unsat)
    check_formulas(CongruenceSolver, [a == b, f(f(a)) != f(f(c))], sat)
    check_formulas(CongruenceSolver, [h(a, b) == a, h(h(a, b), b) != a], unsat)
    check_formulas(CongruenceSolver, [f(a) == f(b), a != b], sat)
    check_formulas(CongruenceSolver, [g(g(g(x))) == x, g(g(g(g(g(x))))) == x, g(x) != x], unsat)


def CongruenceSolver_test_sat() -> None:
    S = DeclareSort("S")
    a, b, c = Consts("a b c", S)
    f = Function("f", S, S)
    g = Function("g", S, S)
    h = Function("h", S, S, S)
    check_formulas(CongruenceSolver, [a == c, f(a) != f(b)], sat)
    check_formulas(CongruenceSolver, [f(a) != g(a)], sat)
    check_formulas(CongruenceSolver, [h(a, b) != h(b, a)], sat)
    check_formulas(CongruenceSolver, [a == b, h(a, c) != h(b, a)], sat)


def CongruenceSolver_tests() -> None:
    CongruenceSolver_test1()
    CongruenceSolver_test2()
    CongruenceSolver_test_lecture()
    CongruenceSolver_test_sat()
    Solver_test_files(CongruenceSolver, linearize, "QF_UF")


if __name__ == "__main__":
    CongruenceSolver_tests()
    print("OK")
