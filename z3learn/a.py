from z3 import *


def s1():
    s = Solver()
    f = Function('f', IntSort(), IntSort(), IntSort())
    a = Int('a')
    b = Int('b')
    x = Int('x')
    s.add(ForAll(x, f(x, x) >= x + a))
    s.add(f(a, b) < a)
    s.add(a > 0)
    if s.check() == sat:
        print(s.model())
        for l in s.model():
            print(s.model()[l])


def s2():
    s = Solver()
    x = Int('x')
    y = Int('y')
    a1 = Array('a1', IntSort(), IntSort())
    s.add(Select(a1, x) == x)
    s.add(Store(a1, x, y) == a1)
    s.add(is_not(x == y))
    if s.check() == sat:
        print(s.model())
    else:
        print("unsat")


if __name__ == '__main__':
    s1()
