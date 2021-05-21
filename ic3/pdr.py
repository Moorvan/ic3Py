from z3 import *


# conjunction of literals.
class tCube:
    # make a tcube object assosciated with frame t.
    def __init__(self, t=0):
        self.t = t
        self.cubeLiterals = list()

    def addModel(self, lMap, model):
        no_primes = [l for l in model if str(l)[-1] != '\'']
        no_input = [l for l in no_primes if str(l)[0] != 'i']
        self.cubeLiterals.extend([lMap[str(l)] == model[l] for l in no_input])

    def addAnds(self, ms):
        self.cubeLiterals.extend(ms)

    def add(self, m):
        g = Goal()
        g.add(m)
        t = Tactic('tseitin-cnf')
        for c in t(g)[0]:
            self.cubeLiterals.append(c)
        if len(t(g)[0]) == 0:
            self.cubeLiterals.append(True)

    def delete(self, i: int):
        res = tCube(self.t)
        for it in range(len(self.cubeLiterals)):
            if it == i:
                res.add(True)
                continue
            res.add(self.cubeLiterals[it])
        return res

    def cube(self):
        return simplify(And(self.cubeLiterals))

    def __repr__(self):
        return str(self.t) + ": " + str(sorted(self.cubeLiterals, key=str))


class tClause:
    def __init__(self, t=0):
        self.t = t
        self.clauseLiterals = []

    def defFromNotCube(self, c: tCube):
        for cube in c.cubeLiterals:
            self.clauseLiterals.append(Not(cube))

    def clause(self):
        return simplify(Or(self.clauseLiterals))

    def add(self, m):
        self.clauseLiterals.append(m)

    def delete(self, i: int):
        res = tClause(self.t)
        for it in range(len(self.clauseLiterals)):
            if it == i:
                continue
            res.add(self.clauseLiterals[it])
        return res

    def __repr__(self):
        return str(self.t) + ": " + str(sorted(self.clauseLiterals, key=str))


class PDR:
    def __init__(self, primary_inputs, literals, primes, init, trans, post):
        self.primary_inputs = primary_inputs
        self.init = init
        self.trans = trans
        self.literals = literals
        self.items = self.primary_inputs + self.literals
        self.lMap = {str(l): l for l in self.items}
        self.post = post
        self.R = list()
        self.primeMap = [(literals[i], primes[i]) for i in range(len(literals))]

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
                print("Adding frame " + str(len(self.R)) + "...")
                self.R.append(tCube(len(self.R)))
                for index, fi in enumerate(self.R):
                    if index == len(self.R) - 1:
                        break
                    for c in fi.cubeLiterals:
                        s = Solver()
                        s.add(fi.cube())
                        s.add(self.trans.cube())
                        s.add(Not(substitute(c, self.primeMap)))
                        if s.check() == unsat:
                            self.R[index + 1].add(c)
                    if self.checkForInduction(fi):
                        print("Fond inductive invariant:\n" + str(fi.cube()))
                        return True

    def checkForInduction(self, frame):
        print("check for Induction now...")
        s = Solver()
        s.add(self.trans.cube())
        s.add(frame.cube())
        s.add(Not(substitute(frame.cube(), self.primeMap)))
        if s.check() == unsat:
            return True
        return False

    def recBlockCube(self, s0: tCube):
        print("recBlockCube now...")
        Q = [s0]
        while len(Q) > 0:
            s = Q[-1]
            if s.t == 0:
                return Q
            z = self.solveRelative(s)
            if z is None:
                Q.pop()
                s = self.MIC(s)
                for i in range(1, s.t + 1):
                    self.R[i].add(Not(s.cube()))
            else:
                Q.append(z)
        return None

    def MIC(self, q: tCube):
        i = 0
        while True:
            if i < len(q.cubeLiterals) - 1:
                i = i + 1
            else:
                break
            q1 = q.delete(i)
            if self.down(q1):
                q = q1
        return q

    def down(self, q: tCube):
        while True:
            s = Solver()
            s.push()
            s.add(And(self.R[0].cube(), Not(q.cube())))
            if unsat == s.check():
                return False
            s.pop()
            s.push()
            s.add(And(self.R[q.t].cube(), Not(q.cube()), self.trans.cube(),
                      substitute(q.cube(), self.primeMap)))  # Fi and not(q) and T and q'
            if unsat == s.check():
                return True
            # q.addModel(self.lMap, s.model())
            # s.pop()
            return False

    def generalize_iter(self, c: tClause):
        done = False
        for i in range(1, 10):
            if done:
                break
            done = True
            for j in range(len(c.clauseLiterals)):
                g = c.delete(j)
                s = Solver()
                s.push()
                s.add(self.R[0].cube())
                s.add(Not(g.clause()))
                if s.check() == sat:
                    s.pop()
                    continue
                s.pop()
                s.push()
                s.add(And(self.R[c.t].cube(), self.trans.cube(), g.clause()), substitute(g.clause(), self.primeMap))
                if s.check() == sat:
                    cc = tClause(c.t)
                    while s.check() == sat:
                        c0 = tCube()
                        c0.addModel(self.lMap, s.model())
                        cc.add(c0.cube())
                        s.add(Not(c0.cube()))
                    s.pop()
                    s.push()
                    s.add(And(cc.clause(), self.R[0].cube()))
                    print(1)
                    s0 = Solver()
                    s0.add(Or(cc.clause(), g.clause()))
                    s0.add(self.R[0].cube())
                    if unsat == s0.check():
                        print("Yyyyys")
                        exit(1)
                    else:
                        print("Nooo")
                        exit(1)

                    while s.check() == sat:
                        print(2)
                        s1 = Solver()
                        s1.push()
                        for l in g.clauseLiterals:
                            s1.add(cc.clause())
                            s1.add(l)
                            if unsat == s1:
                                cc.add(l)
                                break
                        s.pop()
                        s.push()
                        s.add(And(cc.clause(), self.R[0].cube()))
                    c = cc
                    done = False
                    break
                else:
                    s.pop()

    def generalize_CTG(self, c: tClause, rec_lvl=1):
        required = []
        fail = 0
        for l in c.clauseLiterals:
            cand = c.delete(l)
            if self.down_CTG(cand, rec_lvl, required):
                c = cand
                fail = 0
            else:
                if ++fail > 5:
                    break
                required.append(l)

    def down_CTG(self, c: tClause, rec_lvl, required: []):
        ctgs = 0
        s = Solver()
        while True:
            s.push()
            s.add(And(self.R[0].cube(), Not(c.clause())))
            if s.check() == sat:
                return False
            s.pop()
            s.push()
            s.add(And(self.R[c.t].cube(), self.trans.cube(), c.clause()), substitute(c.clause(), *self.primeMap))
            if s.check() == sat:
                cc = tClause(c.t)
                while s.check() == sat:
                    c0 = tCube()
                    c0.addModel(self.lMap, s.model())
                    cc.add(c0)
                    s.add(Not(s.model()))
                s.pop()
                s.push()
                s.add(And(cc.clause(), self.R[0].cube()))
                while s.check() == sat:
                    s1 = Solver()
                    s1.push()
                    for l in c.clauseLiterals:
                        s1.add(cc.clause())
                        s1.add(l)
                        if unsat == s1:
                            cc.add(l)
                            break
                    s.pop()
                    s.push()
                    s.add(And(cc.clause(), self.R[0].cube()))
                c = cc
                return True
            elif rec_lvl > 4:
                return False
            else:
                pass
                # s = self.get_predecessor(c.t, Not(substitute(c, *self.primeMap))

    def get_predecessor(self, c: tCube) -> tCube:
        s = Solver()
        s.add(And(self.R[c.t - 1].cube(), self.trans.cube(), Not(c.cube()), substitute(c.cube(), self.primeMap)))
        assert sat == s.check()
        model = s.model()
        c0 = tCube(c.t - 1)
        inputs = [self.lMap[str(l)] == model[l] for l in model if str(l)[0] == 'i']
        p = [self.lMap[str(l)] == model[l] for l in model if str(l)[0] == 'v']
        c0.addAnds(p)
        return c0
        # for iter in range(0, max_iter):
        #     s0 = Solver()
        #     s0.add(And(self.trans.cube(), inputs, substitute(c, self.primeMap), p))
        #     ms = tCube()
        #     while sat == s0.check():
        #         m = s0.model()

    # tcube is bad state
    def solveRelative(self, tcube):
        cubePrime = substitute(tcube.cube(), self.primeMap)
        s = Solver()
        s.add(self.R[tcube.t - 1].cube())
        s.add(self.trans.cube())
        s.add(Not(tcube.cube()))
        s.add(cubePrime)
        if s.check() == sat:
            model = s.model()
            c = tCube(tcube.t - 1)
            c.addModel(self.lMap, model)
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


if __name__ == '__main__':
    pass
