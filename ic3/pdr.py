from z3 import *

from ic3.model import tCube


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
                print("get bad cube!")
                trace = self.recBlockCube(c)
                if trace is not None:
                    print("Found trace ending in bad state:")
                    for f in trace:
                        print(f)
                    return False
            else:
                # inv = self.checkForInduction()
                # if inv is not None:
                #     print("Fond inductive invariant:" + str(inv))
                #     return True
                print("Did not find invariant, adding frame" + str(len(self.R)))
                self.R.append(tCube(len(self.R)))
                for index, fi in enumerate(self.R):
                    if index == len(self.R) - 1:
                        break
                    for c in fi.cubeLiterals:
                        s = Solver()
                        s.add(fi.cube())
                        s.add(c)
                        s.add(self.trans.cube())
                        s.add(Not(substitute(c, *self.primeMap)))
                        if s.check() == unsat:
                            self.R[index + 1].add(c)
                    if self.checkForInduction(fi):
                        print("Fond inductive invariant:" + str(fi))
                        return True

    def checkForInduction(self, frame):
        print("check for Induction now...")
        s = Solver()
        s.add(self.trans.cube())
        s.add(frame.cube())
        s.add(Not(substitute(frame.cube(), *self.primeMap)))
        if s.check() == unsat:
            return True
        return False

    def recBlockCube(self, s0):
        print("recBlockCube now...")
        Q = [s0]
        while len(Q) > 0:
            s = Q[-1]
            if s.t == 0:
                return Q
            z = self.solveRelative(s)
            if z is None:
                Q.pop()
                for i in range(1, s.t + 1):
                    self.R[i].add(Not(s.cube()))
            else:
                Q.append(z)
        return None

    def generalize_CTG(self, c: tCube):
        pass

    # tcube is bad state
    def solveRelative(self, tcube):
        cubePrime = substitute(tcube.cube(), *self.primeMap)
        s = Solver()
        s.add(self.R[tcube.t - 1].cube())
        s.add(self.trans.cube())
        s.add(cubePrime)
        if s.check() == sat:
            model = s.model()
            c = tCube(tcube.t - 1)
            c.addModel(model, self.lMap)
            return c
        return None

    def getBadCube(self):
        print("seek for bad cube...")
        model = And(Not(self.post.cube()), self.R[-1].cube())
        s = Solver()
        s.add(model)
        if s.check() == sat:
            res = tCube(len(self.R) - 1)
            res.addModel(self.lMap, s.model())
            return res
        else:
            return None

