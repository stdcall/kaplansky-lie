"""Exact checks of Chapter II, §§ 1-3 (printed pp. 88-102) of I. Kaplansky,
"Алгебры Ли и локально компактные группы" (Москва: Мир, 1974).

Run from the project root: sage -python checks/sage/chapter-2a.py
(plain asserts; do not use -O).  The last line is "ok chapter-2a: N checks".
Pages are the printed pages; labels are those of content/02-*.typ.  Expected
values are the book's statements; a printed reading that is wrong, or a
hypothesis that cannot be dropped, is kept as a refuted check (`refuted`).
All arithmetic is exact, in QQ, QQ(i) and polynomial rings over QQ; no floats.

The chapter is about topological groups, where a computation can test a claim
on concrete groups (the line, the circle, the Heisenberg group, GL_n) and can
verify identities and inequalities on the full range of a parameter grid, but
cannot prove a topological statement.  The logical steps of §§ 1-2 are in the
Lean files (NssGroups, CompactBasis, SquaringNss, FloorSteps).

What is checked, by section:

section_1 (pp. 88-90).  exm:nss-real-line, exm:nss-circle: every nonzero x in a
  rational grid has a multiple outside U = [-1, 1], resp. outside the arc
  |x| <= 1/4.  exc:nss-bounded-order: Q/Z in the circle is a nondiscrete group
  of finite orders without small subgroups, while the N-torsion is finite (the
  uniform bound on the orders cannot be dropped).  exm:nss-general-linear: the
  sketch: (I + N)^k = sum binomial(k, j) N^j for nilpotent N, n <= 4; a nonzero
  N and an eigenvalue != 1 (real or a rational rotation) push a power out of
  the unit ball.  exm:nss-topological-field: the part of the generalisation
  that reduces to the additive group: the second difference of k a +
  binomial(k, 2) b with step m is m^2 b, and d-th differences give d! c m^d;
  four squares give all integers (n <= 2000).  This does not settle the
  semisimple part of that example: for a field topology that does not come from
  an absolute value it stays as printed, neither proved nor refuted here.
  exm:nss-banach-units: in M_2(QQ) a unipotent x != 1 has unbounded powers (the
  content of Gelfand's proposition for matrices, not the proposition itself).
  exc:nss-infinite-product on the truncations (Z/2)^n: a basic neighbourhood
  fixing the coordinates in F is a subgroup with more than one element for all
  proper F, n <= 6.  The closing question of § 1 on quotients: the example
  G = l^2, H = {x : x_n in (1/n) Z} shows that local compactness cannot be
  dropped (membership and the norm of the small element of order 2 are exact;
  the closedness of H is by hand).
section_2 (pp. 90-98).  Lemmas on a concrete group: lem:compact-conjugation-
  neighbourhood on K = {[[1, t], [0, 1]] : |t| <= T} in GL_2(QQ);
  lem:decreasing-compact-basis on [-1/i, 1/i], with a non-compact family
  refuting it without compactness.  th:square-injective: the identity
  y^(-1) a y = a^(-1) for x^2 = y^2, a = x y^(-1) (all pairs in S_4, in the
  dihedral group of order 16, and for matrices far from 1); the map C -> x C + C y
  behind injectivity of squaring in GL_n near 1 (constant term 2^(n^2) of its
  determinant, n <= 3); doubling on the circle: injective on |x| <= 1/5, not on
  |x| <= 1/4 (the pair +-1/4); the theorem refuted without NSS on (Z/2)^n.
  The floor steps: th:canonical-one-parameter (first paragraph),
  th:canonical-sequence-bound, th:standard-sequence-neighbourhood,
  th:standard-sequence-convergence, on a grid of rationals.
  th:canonical-sequence-bound on the line with r_0 = eps.
  th:canonical-one-parameter on the line, the circle and the Heisenberg group
  (the rate O(1/i) in exact arithmetic, for a_i = exp(A/i) and for the Trotter
  product), and refuted without a_i -> 1 (a_i = 1, m_i = 1 on the line).
  th:canonical-set-compact: a_i -> 1 follows from th:canonical-sequence-bound.
section_3 (pp. 98-102).  The left shift is a left action preserving the norm
  (S_3, all functions with values in a small set).  D_X f, the derivative at
  r = 0 of X(r) f: on the line, for the C^1 bump f = (1 - x^2)^2 on [-1, 1], the
  difference quotient of X(r) f, X(r) = c r, tends to -c f' with the exact
  remainder bound 4 c^2 |h| (both signs of h) on a grid; the derivative at r
  is X(r) D_X f, as stated on p. 99; D_(lambda X) = lambda D_X.
  eq:shift-sum-identity, as a polynomial identity in a, for d <= 15, in the free
  module on f, g over QQ[m][a].  m/[h m] -> 1/h with an exact bound (p. 102).
  The estimate at the head of the proof of th:translation-continuous.  The case
  analysis behind |f(a^(-1) x) - f(x)| < eps on p. 100, on the line.

What this does NOT establish: any theorem of §§ 1-3 in general; the
identification of our text with the printed one.
"""
from sage.all import (QQ, ZZ, PolynomialRing, matrix, identity_matrix, binomial,
                      factorial, SymmetricGroup, DihedralGroup, Subsets,
                      four_squares, ceil, floor)
import itertools

SCOPE = 'chapter-2a'
COUNT = [0]


def check(cond, what):
    assert bool(cond), what
    COUNT[0] += 1


def refuted(cond, what):
    """The printed reading (or the statement without a hypothesis) is false."""
    assert not bool(cond), 'not refuted: ' + what
    COUNT[0] += 1


def grid(den, top):
    """Rationals a/b with b <= den and |a/b| <= top."""
    s = set()
    for b in range(1, den + 1):
        for a in range(-top * b, top * b + 1):
            s.add(QQ(a) / b)
    return sorted(s)


def circ(x):
    """Representative of x mod 1 in [-1/2, 1/2)."""
    x = QQ(x)
    return x - floor(x + QQ(1) / 2)


def norm_inf(M):
    """Maximum row sum norm, exact."""
    return max(sum(abs(e) for e in row) for row in M.rows())


# --------------------------------------------------------------------- § 1
def section_1():
    # Example 2: the line, U = [-1, 1].
    for x in grid(30, 2):
        if x != 0:
            k = floor(1 / abs(x)) + 1
            check(abs(k * x) > 1, 'multiple of x leaves U')
    # Example 3: the circle, the arc |x| <= 1/4 contains no subgroup.
    q = QQ(1) / 4
    for x in grid(40, 1):
        y = circ(x)
        if y != 0:
            check(any(abs(circ(k * y)) > q for k in range(1, 400)),
                  'multiple of x leaves the arc')
    # Exercise 1: Q/Z is nondiscrete, of finite orders, without small
    # subgroups; a uniform bound N on the orders leaves finitely many points.
    for N in range(2, 40):
        pts = sorted(set(circ(QQ(a) / d) for d in range(1, N + 1)
                         for a in range(d)))
        gaps = [abs(pts[j + 1] - pts[j]) for j in range(len(pts) - 1)]
        check(min(gaps) >= QQ(1) / (N * (N - 1)),
              'the elements of order <= N are isolated')
        x = QQ(1) / N
        check(circ(N * x) == 0 and all(circ(j * x) != 0 for j in range(1, N)),
              '1/N has order N')
    # Example 4, the sketch: unipotent powers.
    for n in (2, 3, 4):
        N = matrix(QQ, n, n, lambda i, j: QQ(i + 2 * j + 1) / 7 if i < j else 0)
        I = identity_matrix(QQ, n)
        for k in range(0, 13):
            s = sum((binomial(k, j) * N ** j for j in range(n)),
                    matrix(QQ, n, n))
            check((I + N) ** k == s, '(I + N)^k expansion')
        # a small nonzero N has a power far from I
        for den in (10, 100, 1000):
            M = N / den
            P, k = I + M, 1
            while norm_inf(P - I) <= 1:
                P, k = P * (I + M), k + 1
            check(norm_inf(P - I) > 1 and k >= 1, 'unipotent power escapes')
    # real eigenvalue != 1 and the rational rotations
    for b in (3, 10, 50, 200):
        for lam in (1 + QQ(1) / b, 1 - QQ(1) / b):
            k = 1
            while abs(lam ** k - 1) < QQ(1) / 2:
                k += 1
            check(k <= 2 * b and abs(lam ** k - 1) >= QQ(1) / 2,
                  'eigenvalue power escapes')
    for b in (2, 5, 17, 40):
        u = QQ(1) / b
        c, s = (1 - u ** 2) / (1 + u ** 2), 2 * u / (1 + u ** 2)
        R = matrix(QQ, [[c, -s], [s, c]])
        I = identity_matrix(QQ, 2)
        P, k = R, 1
        while norm_inf(P - I) < QQ(1) / 2:
            P, k = P * R, k + 1
        check(R != I and k <= 3 * b, 'rational rotation has a far power')
    # Example 5, the additive part.  In a topological field whose additive
    # group is NSS a unipotent matrix cannot have all powers near I.
    A = PolynomialRing(QQ, 'k,m,a,b')
    k, m, a, b = A.gens()

    def xk(t):
        return t * a + t * (t - 1) / 2 * b
    check(xk(k + m) - 2 * xk(k) + xk(k - m) == m ** 2 * b,
          'second difference with step m')
    R1 = PolynomialRing(QQ, 'k,m')
    k1, m1 = R1.gens()
    for d in range(1, 7):
        # d-th difference with step m of k^d is d! m^d
        p = k1 ** d
        for _ in range(d):
            p = p.subs({k1: k1 + m1}) - p
        check(p == factorial(d) * m1 ** d, 'd-th difference of k^d')
    for n in range(0, 2001):
        s = four_squares(n)
        check(sum(t ** 2 for t in s) == n, 'four squares')
    # Example 6, for matrices: x unipotent, x != 1, has unbounded powers.
    x = matrix(QQ, [[1, QQ(1) / 3], [0, 1]])
    check((x ** 300)[0, 1] == 100, 'powers of a unipotent grow')
    # Exercise 4 on truncations: a basic neighbourhood contains a subgroup.
    for n in range(1, 7):
        for F in Subsets(range(n)):
            if len(F) == n:
                continue
            V = [v for v in itertools.product((0, 1), repeat=n)
                 if all(v[i] == 0 for i in F)]
            check(len(V) > 1 and all(
                tuple((p + q2) % 2 for p, q2 in zip(v, w)) in V
                for v in V for w in V), 'the coordinate box is a subgroup')
    # The closing question of § 1: local compactness cannot be dropped.
    # G = l^2 is NSS (a normed space), H = {x : x_n in (1/n) Z} is closed, and
    # the class of e_n/(2n) has order 2 and norm at most 1/(2n).
    for n in range(1, 200):
        v = QQ(1) / (2 * n)
        check((v * n) not in ZZ, 'e_n/(2n) is not in H')
        check((2 * v * n) in ZZ, '2 e_n/(2n) is in H')
        check(v ** 2 == QQ(1) / (4 * n ** 2), 'its squared norm tends to 0')


# --------------------------------------------------------------------- § 2
def section_2():
    # Lemma 1 on GL_2(QQ): conjugation by a compact family.
    for T in (1, 2, 5):
        delta = QQ(1) / (2 * (1 + T) ** 2)
        for t in (QQ(j) / 2 for j in range(-2 * T, 2 * T + 1)):
            x = matrix(QQ, [[1, t], [0, 1]])
            for E in ([[1, 0], [0, 0]], [[0, 1], [0, 0]], [[0, 0], [1, 0]],
                      [[1, 1], [1, -1]], [[-1, 1], [-1, 1]]):
                E = matrix(QQ, E)
                g = identity_matrix(QQ, 2) + delta * E / norm_inf(E)
                c = x.inverse() * g * x
                check(norm_inf(c - identity_matrix(QQ, 2)) <= QQ(1) / 2,
                      'x^(-1) V x lies in U')
    # Lemma 2 on the line and without compactness.
    for b in range(1, 200):
        eps = QQ(1) / b
        i = floor(1 / eps) + 1
        check(QQ(1) / i < eps, '[-1/i, 1/i] lies in (-eps, eps)')
    # U_i = [-1/i, 1/i] union [i, oo) is closed, decreasing, with intersection
    # {0}; no member lies in (-1, 1), since i is in U_i.
    refuted(any(abs(QQ(i)) < 1 for i in range(1, 200)),
            'Lemma 2 without compactness: some U_i lies in (-1, 1)')
    # Theorem 3, the identity.
    for G in (SymmetricGroup(4), DihedralGroup(8)):
        L = G.list()
        one = G.identity()
        squares = {}
        for x in L:
            squares.setdefault(x * x, []).append(x)
        pairs = 0
        for s, xs in squares.items():
            for x in xs:
                for y in xs:
                    if x != y:
                        a = x * y.inverse()
                        check(y.inverse() * a * y == a.inverse() and a != one,
                              'y^(-1) a y = a^(-1), a != 1')
                        for k in range(1, 6):
                            check(y.inverse() * a ** k * y == a ** (-k),
                                  'y^(-1) a^k y = a^(-k)')
                        pairs += 1
        check(pairs > 0, 'there are such pairs in the group')
    x = matrix(QQ, [[1, 0], [0, -1]])
    y = matrix(QQ, [[1, 2], [0, -1]])
    a = x * y.inverse()
    check(x ** 2 == y ** 2 and x != y, 'a pair in GL_2(QQ), far from 1')
    check(y.inverse() * a * y == a.inverse(), 'the identity for the pair')
    # Squaring near 1 in GL_n: x^2 - y^2 = x (x - y) + (x - y) y, and the map
    # C -> x C + C y has determinant with constant term 2^(n^2) at x = y = I.
    for n in (1, 2, 3):
        names = ['a%d' % i for i in range(n * n)] + ['b%d' % i for i in range(n * n)]
        P = PolynomialRing(QQ, names)
        gs = P.gens()
        Am = matrix(P, n, n, gs[:n * n])
        Bm = matrix(P, n, n, gs[n * n:])
        Imat = identity_matrix(P, n)
        Xm, Ym = Imat + Am, Imat + Bm
        check(Xm ** 2 - Ym ** 2 == Xm * (Xm - Ym) + (Xm - Ym) * Ym,
              'x^2 - y^2 = x (x - y) + (x - y) y')
        rows = []
        for i in range(n):
            for j in range(n):
                E = matrix(P, n, n)
                E[i, j] = 1
                im = Xm * E + E * Ym
                rows.append([im[p, q] for p in range(n) for q in range(n)])
        sub = {g: 0 for g in gs}
        M0 = matrix(QQ, [[e.subs(sub) for e in r] for r in rows])
        check(M0.det() == 2 ** (n * n), 'det at (I, I)')
    # Doubling on the circle: U = {|x| <= 1/5} is canonical, |x| <= 1/4 is not.
    g = grid(60, 1)
    arc5 = sorted(set(circ(x) for x in g if abs(circ(x)) <= QQ(1) / 5))
    seen = {}
    for x in arc5:
        d = circ(2 * x)
        check(d not in seen, 'doubling injective on |x| <= 1/5')
        seen[d] = x
    refuted(circ(2 * QQ(1) / 4) != circ(2 * QQ(-1) / 4),
            'doubling injective on |x| <= 1/4: the pair +-1/4')
    check(QQ(1) / 4 != circ(QQ(-1) / 4), 'the pair consists of two points')
    # The hypothesis NSS in theorem 3 cannot be dropped: in the product of
    # copies of Z/2 every box contains an element x != 1, x^2 = 1 = 1^2.
    for n in range(1, 7):
        for F in Subsets(range(n)):
            if len(F) == n:
                continue
            free = [i for i in range(n) if i not in F][0]
            v = tuple(1 if i == free else 0 for i in range(n))
            refuted(tuple(2 * t % 2 for t in v) != tuple(0 for _ in v),
                    'squaring injective on a box of (Z/2)^n')
    # Floor steps on a grid.
    Rs = [QQ(a) / b for b in range(1, 12) for a in range(0, 3 * b + 1)]
    Rs = sorted(set(Rs))
    ks = [QQ(1) / 2, QQ(1), QQ(3) / 2, QQ(2), QQ(1) / 3, QQ(7) / 5]
    for m in list(range(1, 25)) + [37, 100, 101]:
        for r in Rs:
            for s in Rs[::4]:
                d = floor((r + s) * m) - floor(r * m) - floor(s * m)
                check(d in (0, 1), 'th. 5: floors differ by at most one')
            # th. 4: p [r m] <= p r m <= m when p r <= 1
            for p in (1, 2, 3, 7):
                if p * r <= 1:
                    check(p * floor(r * m) <= p * r * m <= m, 'th. 4 chain')
        for k in ks:
            pm = floor(k * m)
            if k * m >= 2:
                check(k * m / 2 <= k * m - 1 <= pm, 'th. 8: k m/2 <= [k m]')
                for s in (QQ(1) / 3, QQ(1) / 2, QQ(1)):
                    for r in Rs:
                        if r < k * s / 2:
                            check(floor(r * m) <= floor(s * pm), 'th. 8: floors')
            # th. 9: [r m] and [(r/k) [k m]] differ by a bounded amount
            for r in Rs:
                check(abs(floor(r * m) - floor(r / k * pm)) <= r / k + 1,
                      'th. 9: bounded difference of the exponents')
    # Theorem 4 on the line: |a| <= 1/m, r_0 = eps.
    for m in (1, 2, 5, 17, 100):
        for a in (QQ(1) / m, QQ(-1) / m, QQ(1) / (3 * m)):
            check(all(abs(k * a) <= 1 for k in range(1, m + 1)),
                  'a, ..., a^m lie in U')
            for eps in (QQ(1) / 2, QQ(1) / 10, QQ(1) / 100):
                for r in (eps / 2, eps * QQ(9) / 10):
                    check(abs(floor(r * m) * a) < eps, 'th. 4 with r_0 = eps')
    # Theorem 5 on the line and on the circle, a_i = c/i, m_i = i.
    for c in (QQ(1), QQ(1) / 2, QQ(-3) / 4):
        for i in (5, 50, 500, 5000):
            for r in (QQ(1) / 2, QQ(1) / 3, QQ(2) / 3, QQ(1), QQ(5) / 4, QQ(3)):
                a = c / i
                check(abs(floor(r * i) * a - c * r) <= abs(c) / i,
                      'a^[r i] tends to c r at the rate |c|/i')
                check(abs(circ(floor(r * i) * a - c * r)) <= abs(c) / i,
                      'the same on the circle')
    # ... and on the Heisenberg group, for a_i = exp(A/i) and for the Trotter
    # product a_i = exp(A/i) exp(B/i), whose limit is exp(r (A + B)).
    E12 = matrix(QQ, [[0, 1, 0], [0, 0, 0], [0, 0, 0]])
    E23 = matrix(QQ, [[0, 0, 0], [0, 0, 1], [0, 0, 0]])
    I3 = identity_matrix(QQ, 3)

    def exp3(M):
        return I3 + M + M ** 2 / 2
    for i in (10, 100, 1000, 10000):
        for r in (QQ(1) / 2, QQ(1) / 3, QQ(1), QQ(2)):
            n = floor(r * i)
            a1 = exp3(E12 / i)
            X = exp3(r * E12)
            check(norm_inf(X.inverse() * a1 ** n - I3) <= QQ(2) / i,
                  'Heisenberg: one-parameter sequence')
            a2 = exp3(E12 / i) * exp3(E23 / i)
            Z = exp3(r * (E12 + E23))
            check(norm_inf(Z.inverse() * a2 ** n - I3) <= QQ(8) / i,
                  'Heisenberg: the Trotter product converges at the rate 1/i')
    # Theorem 5 needs a_i -> 1: a_i = 1, m_i = 1 on the line gives a step
    # function, which is no one-parameter subgroup.
    vals = {r: floor(r * 1) * QQ(1) for r in (QQ(1) / 2, QQ(1), QQ(3) / 2)}
    refuted(vals[QQ(1) / 2] + vals[QQ(1)] == vals[QQ(3) / 2] and
            vals[QQ(1) / 2] + vals[QQ(1) / 2] == vals[QQ(1)],
            'theorem 5 without a_i -> 1')
    # Theorem 7: a_i = X_i(1/i) tends to 1 by theorem 4; on the line |c_i| <= 1
    # (X_i(t) in U for |t| <= 1) gives |a_i| <= 1/i.
    for i in range(1, 100):
        for c in (QQ(1), QQ(-1), QQ(1) / 3):
            check(abs(c / i) <= QQ(1) / i, 'a_i tends to 1')
    # Theorem 6 on the line: a_i = 3/(2 i) has m_i = floor(2 i/3), a^m_i -> 1.
    for i in range(3, 200):
        a = QQ(3) / (2 * i)
        mi = floor(1 / a)
        check(abs(mi * a) <= 1 < abs((mi + 1) * a), 'm_i is the largest')
        check(abs(mi * a - 1) <= a, 'a^m_i tends to b = 1 != 0')


# --------------------------------------------------------------------- § 3
def bump(x):
    """(1 - x^2)^2 on [-1, 1], 0 outside: a C^1 function with compact support."""
    return (1 - x ** 2) ** 2 if abs(x) <= 1 else QQ(0)


def dbump(x):
    return -4 * x * (1 - x ** 2) if abs(x) <= 1 else QQ(0)


def section_3():
    # The left shift is a left action preserving the norm.
    G = SymmetricGroup(3)
    L = G.list()
    for vals in itertools.product((0, 1, -2), repeat=3):
        f = {g: QQ(vals[i % 3]) * (i + 1) for i, g in enumerate(L)}

        def shift(a, h):
            return {x: h[a.inverse() * x] for x in L}
        for a in L:
            check(max(abs(v) for v in shift(a, f).values())
                  == max(abs(v) for v in f.values()), '||a f|| = ||f||')
            for b in L[:3]:
                check(shift(a * b, f) == shift(a, shift(b, f)),
                      '(a b) f = a (b f)')
                # the estimate of the proof of theorem 13, in the same setting
                nab = max(abs(shift(a * b, f)[x] - f[x]) for x in L)
                na = max(abs(shift(a, f)[x] - f[x]) for x in L)
                nb = max(abs(shift(b, f)[x] - f[x]) for x in L)
                check(nab <= na + nb, '||a b f - f|| <= ||a f - f|| + ||b f - f||')
    # D_X f on the line: X(r) = c r, (X(r) f)(x) = f(x - c r).  The difference
    # quotient, for h of both signs, tends to -c f' with remainder <= 4 c^2 |h|
    # (|f''| <= 8 on [-1, 1]).
    xs = [QQ(a) / 16 for a in range(-24, 25)]
    for c in (QQ(1), QQ(-1), QQ(3) / 2, QQ(1) / 3):
        for h in (QQ(1) / 2, QQ(-1) / 2, QQ(1) / 10, QQ(-1) / 10, QQ(1) / 100,
                  QQ(-1) / 1000):
            for x in xs:
                q = (bump(x - c * h) - bump(x)) / h
                check(abs(q - (-c * dbump(x))) <= 4 * c ** 2 * abs(h),
                      'difference quotient at 0 tends to -c f\'')
                # p. 99: the derivative at r is X(r) D_X f = (x -> -c f'(x - c r)).
                for r in (QQ(1) / 3, QQ(-5) / 7):
                    q2 = (bump(x - c * (r + h)) - bump(x - c * r)) / h
                    check(abs(q2 - (-c * dbump(x - c * r)))
                          <= 4 * c ** 2 * abs(h),
                          'the derivative of X(r) f at r is X(r) D_X f')
                # D_(lambda X) = lambda D_X: the same formula with lambda c.
                lam = QQ(2)
                q3 = (bump(x - lam * c * h) - bump(x)) / h
                check(abs(q3 - lam * (-c * dbump(x)))
                      <= 4 * (lam * c) ** 2 * abs(h),
                      'D_(lambda X) f = lambda D_X f')
    # Formula (2), as a polynomial identity: the free module on f, g over
    # QQ[m][a].  Coefficient of f and of g are compared separately.
    P = PolynomialRing(QQ, 'a,m')
    a, m = P.gens()
    for d in range(1, 16):
        # m (a^d f - f) - d g = sum a^t [m (a f - f) - g] + sum (a^t g - g)
        lhs_f, lhs_g = m * (a ** d - 1), P(-d)
        rhs_f = sum(a ** t * m * (a - 1) for t in range(d))
        rhs_g = sum(-a ** t for t in range(d)) + sum(a ** t - 1 for t in range(d))
        check(lhs_f == rhs_f and lhs_g == rhs_g, 'eq:shift-sum-identity')
    # p. 102: m/[h m] -> 1/h, with |m/[h m] - 1/h| <= 2/(h^2 m) once h m >= 2.
    for h in (QQ(1) / 3, QQ(1) / 2, QQ(1), QQ(7) / 5):
        for mm in (10, 100, 1000, 12345):
            if h * mm >= 2:
                d = floor(h * mm)
                check(abs(QQ(mm) / d - 1 / h) <= 2 / (h ** 2 * mm),
                      'm/[h m] tends to 1/h')
    # Theorem 11: ||a g - f|| <= ||g - f|| + ||a f - f||, as functions on a grid.
    def g_(y):
        return bump(y) + (y ** 2 / 100 if abs(y) <= 1 else QQ(0))
    for a0 in (QQ(1) / 4, QQ(-1) / 3):
        n1 = max(abs(g_(x - a0) - bump(x)) for x in xs)
        ng = max(abs(g_(y) - bump(y)) for y in xs + [x - a0 for x in xs])
        naf = max(abs(bump(x - a0) - bump(x)) for x in xs)
        check(n1 <= ng + naf, 'the estimate of the proof of theorem 11')
    # P. 100: T = [-1, 1], W = [-1, 1], V inside W.  If a^(-1) x leaves W T then
    # x is outside T, so f vanishes at both points: the printed V subset W is
    # what makes uniform continuity on W T sufficient.
    for a0 in (QQ(1) / 2, QQ(-1), QQ(3) / 4, QQ(1)):
        for x in xs + [QQ(a) / 8 for a in range(-32, 33)]:
            if abs(x - a0) > 2:
                check(abs(x) > 1, 'a^(-1) x outside W T implies x outside T')


def main():
    section_1()
    section_2()
    section_3()
    print('ok %s: %d checks' % (SCOPE, COUNT[0]))


if __name__ == '__main__':
    main()
