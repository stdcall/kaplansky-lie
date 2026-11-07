"""Exact checks of Chapter II, §§ 4-6 (printed pp. 102-113) of I. Kaplansky,
"Алгебры Ли и локально компактные группы" (Москва: Мир, 1974): the functions
Delta, theta, phi, psi and the bound on i/n_i.

Run from the project root: sage -python checks/sage/chapter-2b.py
(plain asserts; do not use -O).  The last line is "ok chapter-2b: N checks".
Pages are the printed pages; labels are those of content/02-*.typ.  Expected
values are the book's; a printed reading that is wrong is kept as a refuted
check (`refuted`) beside the corrected one.  All arithmetic is in QQ.

What is checked, by section:

finite_groups (§§ 4-5, a finite group is a discrete metrizable locally compact
  group, every subset is compact, the Haar measure is the counting measure):
  for S_3, Q_8, D_4, Z/12 and A_4 exhaustively over all pairs Q subset U of
  symmetric subsets containing 1 with <Q> not in U, for S_4 over 200 random
  pairs: n as in step:integer-n; Delta by the printed table
  (step:function-delta); lem:delta-properties (a)-(e); phi of eq:phi-definition
  for a proper theta (step:function-theta) with lem:phi-properties (a), (b),
  (c); psi with lem:psi-support; eq:difference-quotient-integral (with the
  shift in eq:difference-quotient-shifted); the bound and the support U^5 of
  lem:difference-quotients-bounded; lem:phi-right-equicontinuous in the sharp
  form |phi(x a) - phi(x)| <= sup |theta(x a) - theta(x)|; lem:psi-proper:
  psi(u) < psi(1) for u != 1, with eq:cauchy-psi; eq:product-estimate for all
  products of n elements of Q.  lem:yamabe-proper, the step n' <= n, Delta' >=
  Delta for U' subset U (S_3, Q_8, D_4, exhaustively).  The printed
  «theta, как и Delta, имела строгий максимум» refuted: Delta has a strict
  minimum at 1, 1 - Delta a strict maximum.

line (§§ 4-6 on G = R, U = [-1, 1], which is canonical by the definition of
  p. 93): Q_i = [-1/i, 1/i], Q_i^j = [-j/i, j/i], n_i = i + 1 (for all i <= 200):
  the printed «n_i <= i» on p. 112 and the module 1 of <a_i, n_i> are refuted,
  the corrected n_(p(i)) <= p(i) holds whenever p(i)/n_(p(i)) > 1 and the
  sequence <a_i, i> has module 1.  Delta_i in closed form, phi_i in closed form,
  verified against a brute-force sup on a grid; the limit phi(x) = (1 - |x|/2)^2
  on [-2, 2] (the closed form, as a sup of (1 - |y|)(1 - |x - y|)), the rate
  |phi_i - phi| <= 2/i; psi = lim psi_i as an explicit piecewise polynomial of
  degree 5 (exact integrals), C^1, proper, vanishing outside U^4; psi_i exact for
  small i (exact integration of piecewise polynomials) with
  lem:psi-subsequence-converges and lem:difference-quotients-bounded;
  th:standard-sequence-differentiable: i (a_i psi - psi) tends to -c psi' for
  a_i = c/i at the rate C/i.
  lem:difference-quotients-bounded, the step «можно ограничиться только теми u
  и z, которые лежат в U^5»: for Q = U = [-1, 1], n = 2, the pair u = 49/10,
  z = 51/10 has values n (q psi - psi)(u) != 0 = n (q psi - psi)(z), and the
  integrand of eq:integral-phi-difference does not vanish at y = 141/20 outside
  U^7 (refuted), while U^8 suffices (corrected reading).
  lem:q-sets-fundamental: n_i -> infinity, Q_i inside (-eps, eps).

circle, torus, Heisenberg (th:ratio-bounded, p. 111): circle with U = {|x| <= 1/5}
  and torus T^2 with the box: Q_i = {|x| <= 1/(5 i)} by a direct test of multiples
  on a grid, n_i = i + 1.  On the circle also: Delta_i, phi_i, the limit phi and psi
  (with the wrap-around): lem:delta-properties, lem:phi-properties on a grid with a
  brute-force sup, |phi_i - phi| <= 2/i, psi = (psi_R(5 |u|) + psi_R(5 - 5 |u|))/5
  against an exact integral, lem:psi-proper.  Heisenberg group with U = {|a|, |b|, |c| <= 1}: i/2 < n_i <= i + 1 for
  i <= 200, by the bound Q_i subset {|a|, |b| <= 1/i, |c| <= 3/(2 i)} and an
  explicit element; the theorem in a non-abelian group.  In the discrete group Z
  (U = [-3, 3]) Q_i = {0} for i > 3 and no n_i exists (th:ratio-bounded needs a
  nondiscrete G; the corrected reading).  In a non-NSS group, Z/p^K x R, phi_i is
  proper for each i while phi is not: the set S of lem:phi-one-subgroup is the
  subgroup Z/p^K x {0} (this is what p. 109 warns about; p = 2, 3, K = 3).

What this does NOT establish: any theorem in general.  The inequalities are
verified on stated finite grids of a family with a closed form; the exhaustive
parts are exhaustive for the listed finite groups only.
"""
from sage.all import (QQ, ZZ, PolynomialRing, SymmetricGroup, DihedralGroup,
                      AlternatingGroup, QuaternionGroup,
                      CyclicPermutationGroup, ceil, floor, matrix)
import itertools
import random

SCOPE = 'chapter-2b'
COUNT = [0]


def check(cond, what):
    assert bool(cond), what
    COUNT[0] += 1


def refuted(cond, what):
    assert not bool(cond), 'not refuted: ' + what
    COUNT[0] += 1


# ------------------------------------------------------- finite groups
class FG:
    """A finite group as a multiplication table on 0, ..., N-1; 0 is 1."""

    def __init__(self, G):
        L = G.list()
        one = G.identity()
        L.remove(one)
        L = [one] + L
        idx = {g: i for i, g in enumerate(L)}
        self.N = len(L)
        self.mul = [[idx[a * b] for b in L] for a in L]
        self.inv = [idx[a.inverse()] for a in L]

    def prod(self, A, B):
        return frozenset(self.mul[a][b] for a in A for b in B)

    def classes(self):
        seen, out = set(), []
        for x in range(1, self.N):
            if x not in seen:
                c = frozenset((x, self.inv[x]))
                seen |= c
                out.append(c)
        return out

    def generated(self, Q):
        S = frozenset(Q) | frozenset((0,))
        while True:
            T = S | self.prod(S, S)
            if T == S:
                return S
            S = T


def powers_until_exit(G, Q, U):
    """Q^0, Q^1, ... up to the first power not in U; returns (n, powers)."""
    P = [frozenset((0,))]
    while P[-1] <= U:
        nxt = G.prod(P[-1], Q)
        P.append(nxt)
        if len(P) > G.N + 2:
            return None, None
    return len(P) - 1, P


def run_case(G, U, Q):
    """All the claims of §§ 4-5 for one triple (G, U, Q)."""
    N, mul, inv = G.N, G.mul, G.inv
    n, P = powers_until_exit(G, Q, U)
    check(n is not None and n >= 2, 'n exists and n >= 2, as Q is inside U')
    # step (ii): the printed table
    lev = [None] * N
    for x in range(N):
        for j in range(n):
            if x in P[j]:
                lev[x] = j
                break
        if lev[x] is None:
            lev[x] = n
    Delta = [QQ(l) / n for l in lev]
    # Lemma 3
    for x in range(N):
        if x not in U:
            check(Delta[x] == 1, 'lemma 3 (a)')
        check(0 <= Delta[x] <= 1, 'lemma 3 (b)')
        check(Delta[x] == Delta[inv[x]], 'lemma 3 (c)')
        for y in range(N):
            check(Delta[mul[x][y]] <= Delta[x] + Delta[y], 'lemma 3 (d)')
        for q in Q:
            check(abs(Delta[mul[q][x]] - Delta[x]) <= QQ(1) / n, 'lemma 3 (e)')
    check(Delta[0] == 0 and all(Delta[x] >= QQ(1) / n for x in range(1, N)),
          'Delta has a strict minimum at 1')
    if N > 1:
        refuted(all(Delta[x] < Delta[0] for x in range(1, N)),
                'p. 103, the printed «как и Delta»: Delta has a strict maximum')
    # step (iii): a proper theta vanishing outside U, values rational
    theta = [QQ(0)] * N
    theta[0] = QQ(1)
    for x in U:
        if x != 0:
            theta[x] = QQ(x % 5 + 1) / 7
    # step (iv)
    phi = [max((1 - Delta[y]) * theta[mul[inv[y]][x]] for y in range(N))
           for x in range(N)]
    U2 = G.prod(U, U)
    U4 = G.prod(U2, U2)
    U5 = G.prod(U4, U)
    # Lemma 4
    for x in range(N):
        if x not in U2:
            check(phi[x] == 0, 'lemma 4 (a)')
        check(0 <= phi[x] <= 1, 'lemma 4 (b)')
        if x != 0:
            check(phi[x] < 1, 'lemma 4 (b): strict maximum')
        for q in Q:
            check(abs(phi[mul[q][x]] - phi[x]) <= QQ(1) / n, 'lemma 4 (c)')
    check(phi[0] == 1, 'lemma 4 (b)')
    # Lemma 6, sharp form
    for a in range(N):
        d = max(abs(theta[mul[x][a]] - theta[x]) for x in range(N))
        check(all(abs(phi[mul[x][a]] - phi[x]) <= d for x in range(N)),
              'lemma 6')
    # step (v): psi(u) = sum phi(u x) phi(x)
    psi = [sum(phi[mul[u][x]] * phi[x] for x in range(N)) for u in range(N)]
    for u in range(N):
        if u not in U4:
            check(psi[u] == 0, 'lemma 5')
    # Lemma 10: (9), (10), the bound m(U^2), the support U^5
    mU2 = len(U2)
    for q in Q:
        qi = inv[q]
        for u in range(N):
            val = n * (psi[mul[qi][u]] - psi[u])     # (q psi)(u) = psi(q^-1 u)
            i9 = n * sum((phi[mul[qi][mul[u][y]]] - phi[mul[u][y]]) * phi[y]
                         for y in range(N))
            ui = inv[u]
            i10 = n * sum((phi[mul[qi][y]] - phi[y]) * phi[mul[ui][y]]
                          for y in range(N))
            check(val == i9 == i10, 'formulas (9), (10)')
            check(abs(val) <= mU2, 'lemma 10: bound m(U^2)')
            if u not in U5:
                check(val == 0, 'lemma 10: support U^5')
    # Lemma 14: psi is proper, and the Cauchy inequality (16)
    s11 = sum(p ** 2 for p in phi)
    check(psi[0] == s11, 'psi(1) is the integral of phi^2')
    for u in range(1, N):
        check(psi[u] < psi[0], 'lemma 14')
        check(psi[u] ** 2 <= sum(phi[mul[u][y]] ** 2 for y in range(N)) * s11,
              'formula (16)')
    # (17): c a product of n elements of Q: ||c psi - psi|| <= n max ||a psi - psi||
    def snorm(a):
        ai = inv[a]
        return max(abs(psi[mul[ai][x]] - psi[x]) for x in range(N))
    mx = max(snorm(a) for a in Q)
    for c in P[n]:
        check(snorm(c) <= n * mx, 'formula (17)')
    return n, Delta


def enumerate_pairs(G):
    cl = G.classes()
    for choice in itertools.product((0, 1, 2), repeat=len(cl)):
        U, Q = {0}, {0}
        for c, t in zip(cl, choice):
            if t >= 1:
                U |= c
            if t == 2:
                Q |= c
        U, Q = frozenset(U), frozenset(Q)
        if not G.generated(Q) <= U:
            yield U, Q


def finite_groups():
    random.seed(20261107)
    for name, H in (('S3', SymmetricGroup(3)), ('Q8', QuaternionGroup()),
                    ('D4', DihedralGroup(4)),
                    ('Z12', CyclicPermutationGroup(12)),
                    ('A4', AlternatingGroup(4))):
        G = FG(H)
        cases = 0
        for U, Q in enumerate_pairs(G):
            run_case(G, U, Q)
            cases += 1
        check(cases > 0, 'there are cases in ' + name)
    # S_4: 200 random pairs
    G = FG(SymmetricGroup(4))
    cl = G.classes()
    cases = 0
    while cases < 200:
        choice = [random.randint(0, 2) for _ in cl]
        U, Q = {0}, {0}
        for c, t in zip(cl, choice):
            if t >= 1:
                U |= c
            if t == 2:
                Q |= c
        U, Q = frozenset(U), frozenset(Q)
        if not G.generated(Q) <= U:
            run_case(G, U, Q)
            cases += 1
    # Lemma 43, the step n' <= n, Delta' >= Delta for U' subset U.
    for H in (SymmetricGroup(3), QuaternionGroup(), DihedralGroup(4)):
        G = FG(H)
        cl = G.classes()
        for choice in itertools.product((0, 1, 2, 3), repeat=len(cl)):
            U, Up, Q = {0}, {0}, {0}
            for c, t in zip(cl, choice):
                if t >= 1:
                    U |= c
                if t >= 2:
                    Up |= c
                if t == 3:
                    Q |= c
            U, Up, Q = frozenset(U), frozenset(Up), frozenset(Q)
            if G.generated(Q) <= U:
                continue
            n, P = powers_until_exit(G, Q, U)
            np_, Pp = powers_until_exit(G, Q, Up)
            check(np_ <= n, "lemma 43: n' <= n")
            for x in range(G.N):
                def d(nn, PP):
                    for j in range(nn):
                        if x in PP[j]:
                            return QQ(j) / nn
                    return QQ(1)
                check(d(np_, Pp) >= d(n, P), "lemma 43: Delta' >= Delta")


# ---------------------------------------------------------------- the line
def theta_line(x):
    return max(QQ(0), 1 - abs(x))


def delta_line(i, x):
    n = i + 1
    return min(ZZ(ceil(i * abs(x))), n) / QQ(n)


def phi_line(i, x):
    """The closed form of sup (1 - Delta_i(y)) theta(x - y), for x of any sign."""
    x = abs(QQ(x))
    n = i + 1
    best = theta_line(x)                                      # y = 0
    for j in range(1, i + 1):
        f = 1 - QQ(j) / n
        lo, hi = QQ(j - 1) / i, QQ(j) / i
        if lo < x <= hi:
            v = f
        elif x > hi:
            v = f * theta_line(x - hi)
        else:
            v = f * theta_line(lo - x)
        best = max(best, v)
    return best


def phi_limit(x):
    x = abs(QQ(x))
    return (1 - x / 2) ** 2 if x <= 2 else QQ(0)


def piecewise_breaks(i):
    """All abscissae where phi_i can change slope, x >= 0, exact."""
    n = i + 1
    lines = [(QQ(0), QQ(1), QQ(-1))]                  # (start, value at 0, slope)
    pts = {QQ(0), QQ(1)}
    fs = [QQ(1)] + [1 - QQ(j) / n for j in range(1, i + 1)]
    # constants f_j on the steps and the lines f_j (1 - x + j/i)
    for j in range(0, i + 1):
        h = QQ(j) / i
        pts |= {h, h + 1}
    for j in range(0, i + 1):
        for l in range(0, i + 1):
            hj, hl = QQ(j) / i, QQ(l) / i
            # line j meets line l
            aj, bj = fs[j] * (1 + hj), -fs[j]
            al, bl = fs[l] * (1 + hl), -fs[l]
            if bj != bl:
                pts.add((al - aj) / (bj - bl))
            # line j meets constant l
            if bj != 0:
                pts.add((fs[l] - aj) / bj)
    return sorted(p for p in pts if 0 <= p <= 3)


def poly_int(piece_pts, F):
    """Integral over breakpoints of a function that is a polynomial of degree
    <= d on each piece, with d <= 4: exact Simpson-type (Boole) rule."""
    total = QQ(0)
    for a, b in zip(piece_pts, piece_pts[1:]):
        h = (b - a) / 4
        v = [F(a + t * h) for t in range(5)]
        total += (b - a) / 90 * (7 * v[0] + 32 * v[1] + 12 * v[2] + 32 * v[3]
                                 + 7 * v[4])
    return total


def psi_i_at(i, u, br):
    """psi_i(u) = int phi_i(u + x) phi_i(x) dx, exact: on each piece the integrand
    is a polynomial of degree <= 2, and the rule above is exact."""
    u = QQ(u)
    pts = set()
    for b in br:
        for s in (b, -b):
            pts.add(s)
            pts.add(s - u)
    pts = sorted(p for p in pts if -3 - abs(u) <= p <= 3 + abs(u))
    return poly_int(pts, lambda x: phi_line(i, u + x) * phi_line(i, x))


def psi_limit_polys():
    """psi on [0, 2] and on [2, 4] as polynomials in u, exact integrals."""
    R = PolynomialRing(QQ, 'u,x')
    u, x = R.gens()
    S = PolynomialRing(QQ, 'u')
    uu = S.gen()

    def integ(f, a, b):
        # f in QQ[u, x], a, b in QQ[u]
        Fx = f.integral(x)
        return S((Fx.subs({x: b}) - Fx.subs({x: a})))
    neg, pos = lambda t: (1 + t / 2) ** 2, lambda t: (1 - t / 2) ** 2
    # 0 <= u <= 2: x in [-2, -u], [-u, 0], [0, 2 - u]
    p1 = (integ(neg(x + u) * neg(x), R(-2), -u)
          + integ(pos(x + u) * neg(x), -u, R(0))
          + integ(pos(x + u) * pos(x), R(0), 2 - u))
    # 2 <= u <= 4: x in [-2, 2 - u]
    p2 = integ(pos(x + u) * neg(x), R(-2), 2 - u)
    return S, uu, p1, p2


def psi_limit(S_p1_p2, u):
    S, uu, p1, p2 = S_p1_p2
    u = abs(QQ(u))
    if u <= 2:
        return p1(u)
    if u <= 4:
        return p2(u)
    return QQ(0)


def line():
    # U = [-1, 1] is canonical.  Q_i, its powers, n_i.
    gridx = sorted(set(QQ(a) / b for b in range(1, 13) for a in range(-3 * b, 3 * b + 1)))
    for i in range(1, 201):
        Qi = lambda x: all(abs(k * x) <= 1 for k in range(1, i + 1))
        check(Qi(QQ(1) / i) and not Qi(QQ(1) / i + QQ(1) / (1000 * i)),
              'Q_i = [-1/i, 1/i]')
        n = i + 1
        check(all(QQ(j) / i <= 1 for j in range(1, i + 1)) and QQ(n) / i > 1,
              'n_i = i + 1, as Q_i^j = [-j/i, j/i]')
        refuted(n <= i, 'p. 112, the printed n_i <= i')
        # the printed module 1 of <a_i, n_i> with a_i = 1/i
        refuted(abs(n * (QQ(1) / i)) <= 1, 'p. 112, module 1 of <a_i, n_i>')
        check(i * (QQ(1) / i) <= 1, 'module 1 of <a_i, i>')
        check(QQ(i) / n < 1, 'theorem 13: i/n_i is bounded on the line')
    # the corrected reading: if p/n_p > 1 then n_p <= p, and the module 1 holds
    # for <a_p, n_p>; p(i)/n_p(i) -> oo is the assumption of the proof by
    # contradiction, which fails on the line (consistently with theorem 13).
    for p in range(1, 100):
        for np_ in range(1, 100):
            if QQ(p) / np_ > 1:
                check(np_ <= p, 'p/n_p > 1 gives n_p <= p')
                check(abs(np_ * (QQ(1) / p)) <= 1, 'then module 1 of <a_p, n_p>')
    # Lemma 3 for Delta_i on a grid.
    for i in (1, 2, 3, 5, 8):
        n = i + 1
        for x in gridx:
            if abs(x) > 1:
                check(delta_line(i, x) == 1, 'lemma 3 (a) on the line')
            check(delta_line(i, x) == delta_line(i, -x), 'lemma 3 (c) on the line')
            check(delta_line(i, 0) == 0, 'Delta_i(0) = 0')
        for x in gridx[::3]:
            for y in gridx[::5]:
                check(delta_line(i, x + y) <= delta_line(i, x) + delta_line(i, y),
                      'lemma 3 (d) on the line')
            for q in (QQ(1) / i, QQ(-1) / i, QQ(1) / (2 * i)):
                check(abs(delta_line(i, q + x) - delta_line(i, x)) <= QQ(1) / n,
                      'lemma 3 (e) on the line')
    # phi_i: the closed form against a brute-force sup on a grid of y, Lemma 4.
    ys = [QQ(a) / 240 for a in range(-720, 721)]
    for i in (1, 2, 3, 4, 6):
        for x in [QQ(a) / 24 for a in range(-60, 61, 3)]:
            brute = max((1 - delta_line(i, y)) * theta_line(x - y) for y in ys)
            c = phi_line(i, x)
            check(brute <= c, 'the closed form of phi_i is an upper bound')
            # attained up to the mesh of the grid, as theta is 1-Lipschitz
            check(c - brute <= QQ(1) / 120, 'and it is attained up to the mesh')
        n = i + 1
        for x in gridx:
            if abs(x) > 2:
                check(phi_line(i, x) == 0, 'lemma 4 (a) on the line')
            if x != 0:
                check(0 <= phi_line(i, x) < 1, 'lemma 4 (b) on the line')
            for q in (QQ(1) / i, QQ(-1) / i, QQ(1) / (3 * i)):
                check(abs(phi_line(i, q + x) - phi_line(i, x)) <= QQ(1) / n,
                      'lemma 4 (c) on the line')
        check(phi_line(i, 0) == 1, 'phi_i(1) = 1')
    # phi = lim phi_i.  phi(x) = sup_y (1 - |y|)(1 - |x - y|) = (1 - |x|/2)^2.
    A = PolynomialRing(QQ, 'x,y')
    xx, yy = A.gens()
    fxy = (1 - yy) * (1 - xx + yy)
    check(fxy.derivative(yy) == xx - 2 * yy, 'critical point y = x/2')
    check(fxy.subs({yy: xx / 2}) == (1 - xx / 2) ** 2, 'phi(x) = (1 - x/2)^2')
    for x in [QQ(a) / 10 for a in range(0, 21)]:
        for y in [QQ(a) / 40 for a in range(-80, 81)]:
            check(max(QQ(0), 1 - abs(y)) * theta_line(x - y) <= phi_limit(x),
                  'the limit phi is the sup')
    for i in (1, 2, 4, 8, 16, 32, 64):
        for x in [QQ(a) / 16 for a in range(-40, 41)]:
            check(abs(phi_line(i, x) - phi_limit(x)) <= QQ(2) / i,
                  '|phi_i - phi| <= 2/i on the grid')
    check(all(phi_limit(x) < 1 for x in gridx if x != 0) and phi_limit(0) == 1,
          'phi is proper, S = {0}: lemma 13 with U without subgroups')
    # psi = lim psi_i, the closed form.
    data = psi_limit_polys()
    S, uu, p1, p2 = data
    check(p1(2) == p2(2), 'psi is continuous at u = 2')
    check(p1.derivative()(2) == p2.derivative()(2), 'psi is C^1 at u = 2')
    check(p1.derivative()(0) == 0, "psi'(0) = 0: psi is C^1 at 0 (even function)")
    check(p2(4) == 0 and p2.derivative()(4) == 0, 'psi is C^1 at u = 4')
    for u in [QQ(a) / 25 for a in range(1, 101)]:
        check(psi_limit(data, u) < psi_limit(data, 0), 'lemma 14: psi proper')
    for u in (QQ(41) / 10, QQ(5), QQ(-9)):
        check(psi_limit(data, u) == 0, 'lemma 5: psi vanishes outside U^4')
    # psi by numerical-free exact integration agrees with the polynomials
    brk = {QQ(-2), QQ(0), QQ(2)}
    for u in (QQ(1) / 2, QQ(3) / 2, QQ(5) / 2, QQ(7) / 2):
        pts = sorted(brk | {b - u for b in brk})
        val = poly_int(pts, lambda x: phi_limit(x + u) * phi_limit(x))
        check(val == psi_limit(data, u), 'psi: Boole rule = closed form')
    # th:standard-sequence-differentiable: i (a_i psi - psi) -> -c psi', a_i = c/i.
    dp1, dp2 = p1.derivative(), p2.derivative()
    ddp = max(abs(dp1.derivative()(QQ(a) / 8)) for a in range(0, 17))

    def dpsi(u):
        s = 1 if u >= 0 else -1
        u = abs(QQ(u))
        return s * (dp1(u) if u <= 2 else dp2(u) if u <= 4 else QQ(0))
    for c in (QQ(1), QQ(-2), QQ(1) / 2):
        for i in (10, 100, 1000):
            for u in [QQ(a) / 8 for a in range(-40, 41)]:
                diff = i * (psi_limit(data, u - c / i) - psi_limit(data, u))
                check(abs(diff + c * dpsi(u)) <= 8 * c ** 2 / i,
                      'th. 12 on the line: rate 8 c^2/i')
    check(ddp <= 8, 'the second derivative of psi is below 8 at the sample')
    # psi_i exact, for small i: lemma 11, lemma 10.
    for i in (1, 2, 3, 4):
        br = piecewise_breaks(i)
        n = i + 1
        memo = {}

        def pi(u):
            u = abs(QQ(u))
            if u not in memo:
                memo[u] = psi_i_at(i, u, br) if u <= 4 else QQ(0)
            return memo[u]
        us = [QQ(a) / 4 for a in range(-18, 19)]
        for u in us:
            check(abs(pi(u) - psi_limit(data, u)) <= QQ(16) / i,
                  'lemma 11 (bound 2 m(U^2) sup|phi_i - phi|)')
            for q in (QQ(1) / i, QQ(-1) / i):
                check(abs(n * (pi(u - q) - pi(u))) <= 4,
                      'lemma 10: bound m(U^2) = 4 on the line')
                check(abs(i * (pi(u - q) - pi(u))) <= 4,
                      'lemma 16, with i in place of n_i')
        check(pi(0) > 0 and all(pi(u) < pi(0) for u in us if u != 0),
              'psi_i has a strict maximum at 1')
    # The step of the proof of lemma 10: Q = U = [-1, 1], i = 1, n = 2, q = 1.
    br = piecewise_breaks(1)

    def p1f(u):
        return psi_i_at(1, abs(QQ(u)), br) if abs(QQ(u)) <= 4 else QQ(0)
    u0, z0 = QQ(49) / 10, QQ(51) / 10
    check(2 * (p1f(u0 - 1) - p1f(u0)) != 0, 'the value at u = 49/10 is not zero')
    check(2 * (p1f(z0 - 1) - p1f(z0)) == 0, 'the value at z = 51/10 is zero')
    y0 = QQ(141) / 20
    check(y0 > 7, 'y = 141/20 lies outside U^7 = [-7, 7]')
    refuted(phi_line(1, y0 - z0) == phi_line(1, y0 - u0),
            'p. 108: the integrand of (11) vanishes outside U^7 for this pair')
    # with V inside U and at least one point in U^5, both lie in U^6, y in U^8
    for u in [QQ(a) / 2 for a in range(-10, 11)]:
        for v in (QQ(-1), QQ(-1) / 2, QQ(1) / 2, QQ(1)):
            z = u + v
            if abs(u) <= 5:
                check(abs(z) <= 6, 'corrected: z in U^6')
                for t in (QQ(-2), QQ(2)):
                    check(abs(z + t) <= 8 and abs(u + t) <= 8,
                          'corrected: the integrand lives on U^8')
    # Lemma 15 on the line.
    for b in range(1, 100):
        eps = QQ(1) / b
        i = b + 1
        check(QQ(1) / i < eps, 'Q_i lies inside (-eps, eps)')
        check(i + 1 >= b, 'n_i tends to infinity')


# ------------------------------------------- the circle, the torus, Heisenberg
def circ(x):
    x = QQ(x)
    return x - floor(x + QQ(1) / 2)


def others():
    # Circle, U = {|x| <= 1/5}.
    c5 = QQ(1) / 5
    for i in range(1, 41):
        def inQ(x):
            return all(abs(circ(k * x)) <= c5 for k in range(1, i + 1))
        edge = QQ(1) / (5 * i)
        check(inQ(edge) and inQ(-edge), 'Q_i contains +-1/(5 i)')
        check(not inQ(edge + QQ(1) / (1000 * i)), 'and nothing beyond')
        for a in range(-100, 101):
            x = circ(QQ(a) / (5 * i * 20))
            if abs(x) <= c5:
                check(inQ(x) == (abs(x) <= edge), 'Q_i on the grid')
        # Q_i^j = {|x| <= j/(5 i)} without wrap-around for j <= 2 i, n_i = i + 1
        check(QQ(i) / (5 * i) <= c5 < QQ(i + 1) / (5 * i) < QQ(1) / 2,
              'n_i = i + 1 on the circle')
        check(QQ(i) / (i + 1) < 1, 'theorem 13 on the circle')
    # Delta, theta, phi, psi on the circle.  Lemma 3 with the wrap-around in x + y;
    # theta(x) = max(0, 1 - 5 |x|); phi_i(x) = phi_line(i, 5 |x|), since a term
    # with |x - y| > 1/2 has theta = 0 (|y| <= 1/5 in the sup, by lemma 3 (a)).
    gridc = sorted(set(circ(QQ(a) / b) for b in range(1, 41) for a in range(b)))

    def theta_c(x):
        return max(QQ(0), 1 - 5 * abs(circ(x)))

    def delta_c(i, x):
        n = i + 1
        return min(ZZ(ceil(5 * i * abs(circ(x)))), n) / QQ(n)

    def phi_c(i, x):
        return phi_line(i, 5 * abs(circ(x)))
    for i in (1, 2, 3, 5):
        n = i + 1
        for x in gridc:
            if abs(x) > c5:
                check(delta_c(i, x) == 1, 'lemma 3 (a) on the circle')
            check(delta_c(i, x) == delta_c(i, -x), 'lemma 3 (c) on the circle')
            for q in (QQ(1) / (5 * i), QQ(-1) / (5 * i), QQ(1) / (10 * i)):
                check(abs(delta_c(i, q + x) - delta_c(i, x)) <= QQ(1) / n,
                      'lemma 3 (e) on the circle')
                check(abs(phi_c(i, q + x) - phi_c(i, x)) <= QQ(1) / n,
                      'lemma 4 (c) on the circle')
            if abs(x) > 2 * c5:
                check(phi_c(i, x) == 0, 'lemma 4 (a) on the circle')
            if x != 0:
                check(0 <= phi_c(i, x) < 1, 'lemma 4 (b) on the circle')
        for x in gridc[::6]:
            for y in gridc[::4]:
                check(delta_c(i, x + y) <= delta_c(i, x) + delta_c(i, y),
                      'lemma 3 (d) on the circle')
        check(phi_c(i, 0) == 1 and delta_c(i, 0) == 0, 'at the identity')
        # the closed form of phi_i against a brute-force sup, on the circle
        ys = [circ(QQ(a) / 240) for a in range(240)]
        for x in [circ(QQ(a) / 48) for a in range(48)]:
            brute = max((1 - delta_c(i, y)) * theta_c(x - y) for y in ys)
            check(brute <= phi_c(i, x) and phi_c(i, x) - brute <= QQ(1) / 24,
                  'phi_i on the circle: the sup, up to the mesh')
    # phi = lim phi_i = (1 - 5 |x|/2)^2, psi = (psi_R(5 |u|) + psi_R(5 - 5 |u|))/5.
    data = psi_limit_polys()

    def phi_lim_c(x):
        return phi_limit(5 * abs(circ(x)))

    def psi_c(u):
        s = 5 * abs(circ(u))
        return (psi_limit(data, s) + psi_limit(data, 5 - s)) / 5
    for i in (1, 2, 4, 8, 16):
        for x in gridc[::3]:
            check(abs(phi_c(i, x) - phi_lim_c(x)) <= QQ(2) / i,
                  '|phi_i - phi| <= 2/i on the circle')
    for u in gridc:
        if u != 0:
            check(psi_c(u) < psi_c(0), 'lemma 14: psi is proper on the circle')
    for u in (QQ(1) / 10, QQ(3) / 10, QQ(1) / 2, QQ(-2) / 5):
        brk = {QQ(-1) / 2, QQ(1) / 2}
        for b in (QQ(-2) / 5, QQ(0), QQ(2) / 5):
            for t in (b, b - u, b - u + 1, b - u - 1):
                if abs(t) <= QQ(1) / 2:
                    brk.add(t)
        val = poly_int(sorted(brk), lambda x: phi_lim_c(x + u) * phi_lim_c(x))
        check(val == psi_c(u), 'psi on the circle: exact integral = closed form')
    # Torus: the box.  Q_i is the box of side 1/(5 i), n_i = i + 1, since a
    # product stays in U iff it does in each coordinate.
    for i in range(1, 41):
        e = QQ(1) / (5 * i)
        p = (i * e, i * e)
        check(all(abs(t) <= c5 for t in p), 'Q_i^i lies in U')
        check(max((i + 1) * e, 0) > c5, 'Q_i^(i+1) does not')
    # Heisenberg group (a, b, c)(a', b', c') = (a + a', b + b', c + c' + a b'),
    # U = {|a|, |b|, |c| <= 1}.
    def hmul(p, q):
        return (p[0] + q[0], p[1] + q[1], p[2] + q[2] + p[0] * q[1])

    def hpow(p, k):
        # p^k = (k a, k b, k c + binomial(k, 2) a b)
        return (k * p[0], k * p[1], k * p[2] + QQ(k * (k - 1)) / 2 * p[0] * p[1])

    def inU(p):
        return all(abs(t) <= 1 for t in p)
    for i in range(1, 201):
        # Q_i lies in the box |a|, |b| <= 1/i, |c| <= 3/(2 i): from k = i:
        # |i c + binomial(i, 2) a b| <= 1 and |a b| <= 1/i^2.
        bound = (1 + QQ(i * (i - 1)) / 2 / i ** 2) / i
        check(bound <= QQ(3) / (2 * i), 'the bound for c on Q_i')
        # a product of n elements of the box: |a| <= n/i, |b| <= n/i,
        # |c| <= 3 n/(2 i) + binomial(n, 2)/i^2.  For n <= i/2 it stays in U.
        n = i // 2
        if n >= 1:
            cmax = QQ(3 * n) / (2 * i) + QQ(n * (n - 1)) / 2 / i ** 2
            check(QQ(n) / i <= 1 and cmax <= 1, 'Q_i^n lies in U for n <= i/2')
        # the element (1/i, 0, 0) lies in Q_i, its (i + 1)-st power leaves U.
        el = (QQ(1) / i, QQ(0), QQ(0))
        check(all(inU(hpow(el, k)) for k in range(1, i + 1)), '(1/i, 0, 0) in Q_i')
        check(not inU(hpow(el, i + 1)), 'n_i <= i + 1')
        # hence i/(i + 1) <= i/n_i < 2 (and i/n_i = 1/... for i = 1 trivially)
        if i >= 2:
            check(QQ(i) / (n + 1) <= 2, 'theorem 13 on the Heisenberg group')
    # the power formula against repeated multiplication
    p = (QQ(1) / 7, QQ(-2) / 5, QQ(3) / 11)
    q = (QQ(0), QQ(0), QQ(0))
    for k in range(1, 30):
        q = hmul(q, p)
        check(q == hpow(p, k), 'the power formula in the Heisenberg group')
    # Theorem 13 needs a nondiscrete G: Z, U = [-3, 3], Q_i = {0} for i > 3.
    for i in range(4, 50):
        Q = [x for x in range(-3, 4) if all(abs(k * x) <= 3 for k in range(1, i + 1))]
        check(Q == [0], 'in Z, Q_i = {0}, every Q_i^n lies in U: no n_i exists')
    # In a nondiscrete group each Q_i contains x != 1, whose powers leave U.
    # On the line: x = 1/i.  See the function line().
    # A non-NSS group: Z/p^K x R, U = Z/p^K x [-1, 1].  Q_i = Z/p^K x [-1/i, 1/i].
    # Delta_i(z, t) = max(1, ceil(i |t|))/(i + 1) off the identity.  With
    # theta(z, t) = (1 if z = 0 else 1/2) * max(0, 1 - |t|).
    for p_, K in ((2, 3), (3, 3)):
        M = p_ ** K

        def delta2(i, z, t):
            if z % M == 0 and t == 0:
                return QQ(0)
            return min(max(1, ZZ(ceil(i * abs(t)))), i + 1) / QQ(i + 1)

        def theta2(z, t):
            return (QQ(1) if z % M == 0 else QQ(1) / 2) * max(QQ(0), 1 - abs(t))

        def phi2(i, z, t, ts):
            return max((1 - delta2(i, w, s)) * theta2(z - w, t - s)
                       for w in range(M) for s in ts)
        ts = [QQ(a) / 4 for a in range(-8, 9)]
        for i in (1, 2, 4, 8, 16):
            for z in range(M):
                v = phi2(i, z, QQ(0), ts)
                if z != 0:
                    check(v < 1, 'phi_i is proper for each i')
                    # the sup is attained at y = (z, 0): 1 - 1/(i + 1)
                    check(v == 1 - QQ(1) / (i + 1), 'phi_i(z, 0) = 1 - 1/n_i -> 1')
            check(phi2(i, 0, QQ(0), ts) == 1, 'phi_i(1) = 1')
        # S = {(z, 0)} is a subgroup contained in U: closed under addition.
        S = [(z, 0) for z in range(M)]
        check(all(((a[0] + b[0]) % M, 0) in S for a in S for b in S),
              'lemma 13: S is a subgroup inside U')
        check(len(S) > 1, 'so the limit phi is not proper')


def main():
    finite_groups()
    line()
    others()
    print('ok %s: %d checks' % (SCOPE, COUNT[0]))


if __name__ == '__main__':
    main()
