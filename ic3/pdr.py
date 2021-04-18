from z3 import *


# conjunction of literals.
class tCube:
    # make a tcube object assosciated with frame t.
    def __init__(self, model, lMap, t=None):
        self.t = t
        no_primes = [l for l in model if '\'' not in str(l)]
        no_input = [l for l in no_primes if 'i' not in str(l)]
        self.cubeLiterals = [lMap[str(l)] == model[l] for l in no_input]

    def cube(self):
        return And(self.cubeLiterals)

    def __repr__(self):
        return str(self.t) + ": " + str(sorted(self.cubeLiterals, key=str))


class PDR:
    def __init__(self, primary_inputs, literals, primes, init, trans, post):
        self.primary_inputs = primary_inputs
        self.init = init
        self.trans = trans
        self.literals = literals
        self.lMap = {str(l): l for l in self.literals}
        self.post = post
        self.R = []
        self.primeMap = zip(literals, primes)

    def run(self):
        self.R = list()
        self.R.append(self.init)

        while True:
            c = self.getBadCube()
            if c is not None:
                trace = self.recBlockCube(c)
                if trace is not None:
                    print("Found trace ending in bad state:")
                    for f in trace:
                        print(f)
                    return False
            else:
                inv = self.checkForInduction()
                if inv is not None:
                    print("Fond inductive invariant:" + str(simplify(inv)))
                    return True
                print("Did not find invariant, adding frame" + str(len(self.R)))
                self.R.append(True)
                for index, fi in enumerate(self.R):
                    for c in fi:
                        s = Solver()
                        s.add(fi)
                        s.add(c)
                        s.add(self.trans)
                        s.add(Not(substitute(c, *self.primeMap)))
                        if s.check() == unsat:
                            self.R[index + 1].append(c)

    def checkForInduction(self):
        for frame in self.R:
            s = Solver()
            s.add(self.trans)
            s.add(frame)
            s.add(Not(substitute(frame, *self.primeMap)))
            if s.check() == unsat:
                return frame
        return None

    def recBlockCube(self, s0):
        Q = [s0]
        while len(Q) > 0:
            s = Q[-1]
            if s.t == 0:
                return Q
            z = self.solveRelative(s)
            if z is None:
                Q.pop()
                for i in range(1, s.t + 1):
                    self.R[i] = And(self.R[i], Not(s.cube()))
            else:
                Q.append(z)
        return None

    # tcube is bad state
    def solveRelative(self, tcube):
        cubePrime = substitute(tcube.cube(), *self.primeMap)
        s = Solver()
        s.add(self.R[tcube.t - 1])
        s.add(self.trans)
        s.add(cubePrime)
        if s.check() == sat:
            model = s.model()
            return tCube(model, self.lMap, tcube.t - 1)
        return None

    def getBadCube(self):
        model = And(Not(self.post), self.R[-1])
        s = Solver()
        s.add(model)
        if s.check() == sat:
            return tCube(s.model(), self.lMap, len(self.R) - 1)
        else:
            return None

