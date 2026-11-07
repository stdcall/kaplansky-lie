"""Exact checks of Chapter II, §§ 7-9 (printed pp. 113-132) of I. Kaplansky,
"Алгебры Ли и локально компактные группы" (Москва: Мир, 1974): standard
sequences, the vector space of one-parameter subgroups, the integral formula,
K is a neighbourhood of 1.

Run from the project root: sage -python checks/sage/chapter-2c.py
(plain asserts; do not use -O).  The last line is "ok chapter-2c: N checks".
Pages are the printed pages; labels are those of content/02-*.typ.  Expected
values are the book's; a printed reading that is wrong is kept as a refuted
check (`refuted`) beside the corrected one.  All arithmetic is exact (QQ,
polynomial rings over QQ, QQ(t, e)[a, b], power series over QQ).

The models.  G is the group of unitriangular 3 x 3 or 4 x 4 rational matrices
(exp is a polynomial), a one-parameter subgroup is X(r) = exp(r A), X + Y is
exp(r (A + B)) (the Trotter limit, whose rate is checked), a "function on G" f
is a polynomial in the matrix entries (not of compact support: the formulas
below are formal consequences of (g f)(h) = f(g^(-1) h) and
D_X f(h) = d/dr f(X(-r) h) at r = 0, and do not see the support).

What is checked:

identities: eq:telescoping-identity for m <= 10, in the free module on f and the
  symbols D_r over the group ring of the free group on x = X(1/m), y = Y(1/m),
  with the exact expansion in reduced words; the identity of lem:product-standard
  and eq:shifted-product-difference in the same ring; eq:difference-quotient-sum
  for n <= 12 as a polynomial identity; the identity for q_i in
  lem:k-neighbourhood.
integral: lem:integral-formula as an exact polynomial identity in t and the
  entries of h, for two pairs (A, B) of 4 x 4 matrices; the printed A_0 and g with
  Y(1/m) in place of Y(r/m) (p. 128) refuted (their limit is a different integral);
  the convergence of the corrected A_0 with an exact rate; (Y(1/m) X(1/m))^m ->
  Z(1) with a rate; lem:sum-zero-inverse: X(r) Y(s) = Y(s) X_1(r), the chain of
  partial derivatives on p. 118, F = function of r - s when B = -A, not otherwise;
  D_X linear in X (lem:product-standard, lem:vector-space-embedding) as the
  coefficient of 1/m of f(exp(-A/m) h).
lemma_39: eq:difference-as-integral as an exact polynomial identity in e = 1/N.
  lem:standard-difference: the printed statement without Y_i -> 0 refuted, twice:
  on the unitriangular group by p = exp(-y B) exp(y B + e A) = I + e A + (y e/2) E_13,
  whose powers tend to I + r A + (r y/2) E_13 != X(r) (over QQ with symbolic y, e);
  on GL_2(R) with Y = diag(t, -t), X = E_12: the closed form of the matrix
  exponential [[a, e (a - b)/(2 t)], [0, b]], a = exp(t), b = exp(-t), verified as
  the solution of E' = M E over QQ(t, e)[a, b], against the power series of exp M to
  order 30, and the limit c X with c = (1 - exp(-2 t))/(2 t), c != 1, with
  rational enclosures for t in a list.  The corrected statement: for y_i -> 0
  (t_i -> 0) the limit is X, with the exact rate.  The limit in general is
  Gamma(-Y) X, Gamma(X) = sum (ad X)^k/(k + 1)!: the first order in e of
  exp(-B) exp(B + e A) (4 x 4).
steps: the floors of lem:standard-uniform: [s m] + [(r - s) m] and [r m] differ by
  the factor 1 or a_j, both occur, a_j^2 never occurs on the grid (the printed
  reading refuted).  lem:product-standard: the printed a_i b_i in Q_(k m_i) refuted
  on the line; the printed step «(a_i b_i)^s in U if 2 s <= n» refuted on the line
  (h odd, a = b = 1/h, 2 s = h + 1) and the corrected chain with strict signs
  (A > i/n_i) checked on a grid; the sequence a_i b_i on GL_2(QQ) with its
  module.  p. 119, the printed X(1/m_i) against X_i(1/m_i).  p. 120: the printed
  M = image of K_1 is not a subspace, on the line.  p. 124: (i r) X = s X
  lies in K_1 on the line (lem:compact-small-time with the constants).
  lem:standard-to-zero, lem:standard-to-subgroup, lem:product-of-standard-sequences,
  lem:standard-uniform on the line and on the Heisenberg group with exact rates.
  Uniqueness of the subgroup with a given value at 1 (p. 119): on the circle with a
  canonical U, and refuted with the whole circle as U.  lem:image-fills-neighbourhood,
  lem:neighbourhood-of-zero on the line.  lem:adjoint-continuous: S_a linear, S_(a b)
  = S_a S_b, a exp(r A) a^(-1) = exp(r a A a^(-1)).  lem:k-neighbourhood,
  th:nss-locally-euclidean on the Heisenberg group: exp(t log g) stays in the unit
  box for |t| <= 1 when g is in the box of radius 1/2.  th:quotient-nss: Heisenberg
  -> R^2 and R -> circle, explicit lifts.

What this does NOT establish: any theorem in general; the analysis (uniformity of
limits) in the book's proofs, which is read by hand and partly formalised in Lean.
"""
from sage.all import (QQ, ZZ, PolynomialRing, PowerSeriesRing, matrix,
                      identity_matrix, floor, ceil, factorial)
import itertools

SCOPE = 'chapter-2c'
COUNT = [0]


def check(cond, what):
    assert bool(cond), what
    COUNT[0] += 1


def refuted(cond, what):
    assert not bool(cond), 'not refuted: ' + what
    COUNT[0] += 1


def norm_inf(M):
    return max(sum(abs(e) for e in row) for row in M.rows())


# ----------------------------------------------------------- the free group ring
def reduce_word(w):
    out = []
    for g in w:
        if out and out[-1] == -g:
            out.pop()
        else:
            out.append(g)
    return tuple(out)


def wmul(*ws):
    w = ()
    for u in ws:
        w = reduce_word(w + tuple(u))
    return w


def wpow(u, k):
    if k < 0:
        return wpow(tuple(-g for g in reversed(u)), -k)
    w = ()
    for _ in range(k):
        w = wmul(w, u)
    return w


class FM:
    """Formal sums of (word, symbol) with coefficients in QQ."""

    def __init__(self, d=None):
        self.d = dict(d or {})

    def __add__(self, o):
        r = dict(self.d)
        for k, v in o.d.items():
            r[k] = r.get(k, QQ(0)) + v
            if r[k] == 0:
                del r[k]
        return FM(r)

    def scale(self, c):
        return FM({k: c * v for k, v in self.d.items()} if c != 0 else {})

    def __sub__(self, o):
        return self + o.scale(QQ(-1))

    def act(self, w):
        return FM({(wmul(w, k[0]), k[1]): v for k, v in self.d.items()})

    def __eq__(self, o):
        return self.d == o.d


def sym(s):
    return FM({((), s): QQ(1)})


def identities():
    x, y = (1,), (2,)
    f = sym('f')
    # eq:telescoping-identity.  c = Y(1/m) X(1/m); X_(r/m)(1/m) = y^(-r) x y^r.
    for m in range(1, 11):
        c = wmul(y, x)
        left = f.act(wpow(c, m)) - f.act(wpow(y, m))
        A, B = FM(), FM()
        for r in range(m):
            pre = wmul(wpow(c, m - r), wpow(x, -1), wpow(y, r))
            Dr = sym('D%d' % r)
            A = A + Dr.act(pre).scale(QQ(1) / m)
            Xr = wmul(wpow(y, -r), x, wpow(y, r))
            inner = (f.act(Xr) - f).scale(QQ(m)) - Dr
            B = B + inner.act(pre).scale(QQ(1) / m)
        check(left == A + B, '(27) for m = %d' % m)
        check(all(k[1] == 'f' for k in (A + B).d), 'the symbols D_r cancel')
    # the identity m (a b f - f) = a {m (b f - f)} + m (a f - f); (19) is the same.
    a, b = (1,), (2,)
    for m in (1, 2, 3, 7):
        lhs = (f.act(wmul(a, b)) - f).scale(QQ(m))
        rhs = (f.act(b) - f).scale(QQ(m)).act(a) + (f.act(a) - f).scale(QQ(m))
        check(lhs == rhs, 'lemma 19, (19), lemma 29')
    # (21): in the module over QQ(s, n)[a] on f and D, a = X(s), X(k s) = a^k.
    P = PolynomialRing(QQ, 'a,s')
    a_, s_ = P.gens()
    F = P.fraction_field()
    for n in range(1, 13):
        lf = (a_ ** n - 1) / (n * s_)
        ld = F(-1)
        rd = sum((a_ ** k - 1) / F(n) for k in range(n))
        rf = sum(a_ ** k * (a_ - 1) / (n * s_) for k in range(n))
        rd2 = -sum(a_ ** k / F(n) for k in range(n))
        check(lf == rf and ld == rd + rd2, '(21) for n = %d' % n)
    # The identity for q_i in lemma 40, a group identity: with p = Y(-1) Z(1),
    # p^(-1) x = Z(-1) Y(1) Y(-1) a = Z(-1) a.  Words y = Y(1), z = Z(1), v = a.
    yy, zz, vv = (1,), (2,), (3,)
    p = wmul(wpow(yy, -1), zz)
    x_i = wmul(wpow(yy, -1), vv)
    check(wmul(wpow(p, -1), x_i) == wmul(wpow(zz, -1), vv), 'q_i = Z(-1) a')


# ------------------------------------------------------- the unitriangular model
ENT = ['g12', 'g13', 'g14', 'g23', 'g24', 'g34']


def ring4(extra=()):
    return PolynomialRing(QQ, list(extra) + ENT + ['e0'])


def gen_h(R):
    return matrix(R, [[1, R('g12'), R('g13'), R('g14')],
                      [0, 1, R('g23'), R('g24')],
                      [0, 0, 1, R('g34')],
                      [0, 0, 0, 1]])


def mexp(M):
    n = M.nrows()
    R = M.base_ring()
    out = identity_matrix(R, n)
    T = identity_matrix(R, n)
    for k in range(1, n):
        T = T * M / k
        out = out + T
    return out


def f4(M):
    """A polynomial function on the unitriangular group."""
    return (M[0, 1] * M[1, 2] + 2 * M[0, 2] * M[2, 3] + M[0, 3] ** 2
            + M[0, 1] ** 2 * M[2, 3] - 3 * M[1, 3] + M[1, 2] * M[1, 3])


def D_at(A, h):
    """D_X f at h: the derivative at r = 0 of f(exp(-r A) h), by (I - e0 A) h."""
    R = h.base_ring()
    e0 = R('e0')
    M = (identity_matrix(R, 4) - e0 * A) * h
    val = f4(M)
    return val.derivative(e0).subs({e0: R(0)})


def integral():
    pairs = [
        ([[0, 1, 2, 0], [0, 0, 1, 3], [0, 0, 0, 1], [0, 0, 0, 0]],
         [[0, 2, 0, 1], [0, 0, -1, 1], [0, 0, 0, 2], [0, 0, 0, 0]]),
        ([[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
         [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]),
    ]
    R = ring4(['t', 'r', 's'])
    t, r, s = R('t'), R('r'), R('s')
    h = gen_h(R)
    I4 = identity_matrix(R, 4)
    for Al, Bl in pairs:
        A, B = matrix(R, Al), matrix(R, Bl)
        C = A + B
        # Lemma 37: f(Z(-1) h) - f(Y(-1) h) = int_0^1 [Z(1-t) Y(t) D_(X_t) f](h) dt.
        left = f4(mexp(-C) * h) - f4(mexp(-B) * h)
        Yt, Ymt = mexp(t * B), mexp(-t * B)
        At = Ymt * A * Yt
        arg = Ymt * mexp((t - 1) * C) * h
        integrand = D_at(At, arg)
        F = integrand.integral(t)
        val = F.subs({t: R(1)}) - F.subs({t: R(0)})
        check(left == val, 'lemma 37: the integral formula')
        # The printed A_0 and g with Y(1/m), m -> oo: the term Y(t) is lost.  Its
        # limit is the integral of Z(1 - t) D_(X_t) f, a different function.
        arg_printed = mexp((t - 1) * C) * h
        F2 = D_at(At, arg_printed).integral(t)
        val2 = F2.subs({t: R(1)}) - F2.subs({t: R(0)})
        refuted(left == val2, 'p. 128: the printed Y(1/m) in A_0 and g')
        # Riemann sums of the corrected A_0: rate in m at a rational point h0.
        sub = {R('g12'): QQ(1), R('g13'): QQ(-2), R('g14'): QQ(1) / 3,
               R('g23'): QQ(2), R('g24'): QQ(1), R('g34'): QQ(-1)}
        exact = QQ(val.subs(sub))
        iu = PolynomialRing(QQ, 't')
        I0 = iu([QQ(c0) for c0 in integrand.subs(sub).polynomial(t).list()])
        for m in (10, 100, 1000):
            A0 = sum(I0(QQ(j) / m) for j in range(m)) / m
            bound = sum(abs(c) for c in I0.derivative().coefficients()) / m
            check(abs(A0 - exact) <= bound, 'A_0 tends to the integral')
        # (Y(1/m) X(1/m))^m -> Z(1), at a rate.
        Aq, Bq = matrix(QQ, Al), matrix(QQ, Bl)
        Cq = Aq + Bq
        Zinv = mexp(-Cq)
        rates = []
        for m in (10, 100, 1000):
            c = mexp(Bq / m) * mexp(Aq / m)
            rates.append(norm_inf(Zinv * c ** m - identity_matrix(QQ, 4)) * m)
        check(rates[2] <= rates[0] + 1 and rates[0] <= 60,
              'the Trotter limit: rate C/m with a bounded C')
        # p. 118: X(r) Y(s) = Y(s) X_1(r), and the chain of partial derivatives.
        Ys, Yms = mexp(s * B), mexp(-s * B)
        A1 = Yms * A * Ys
        Xr, Xmr = mexp(r * A), mexp(-r * A)
        check(Xr * Ys == Ys * mexp(r * A1), 'X(r) Y(s) = Y(s) X_1(r)')
        Frs = f4(Yms * Xmr * h)                     # (X(r) Y(s) f)(h)
        dF_dr = Frs.derivative(r)
        # Y(s) X_1(r) D_(X_1) f at h is (D_(X_1) f)(X_1(-r) Y(-s) h)
        rhs = D_at(A1, mexp(-r * A1) * Yms * h)
        check(dF_dr == rhs, 'dF/dr = Y(s) X_1(r) D_(X_1) f')
        dF_ds = Frs.derivative(s)
        rhs2 = D_at(B, Yms * Xmr * h)               # X(r) Y(s) D_Y f at h
        check(dF_ds == rhs2, 'dF/ds = X(r) Y(s) D_Y f')
        # when Y = -X the sum is 0 and F is a function of r - s; otherwise not
        Fminus = f4(mexp(s * A) * Xmr * h)
        check(Fminus.derivative(r) == -Fminus.derivative(s),
              'lemma 23: F_r = -F_s for Y = -X')
        refuted(dF_dr == -dF_ds, 'F_r = -F_s for a general pair')
        # D_X is linear in X: the coefficient of 1/m in f(exp(-A/m) h).
        R1 = ring4(['u', 'v', 'w'])
        u, v, w = R1('u'), R1('v'), R1('w')
        hh = gen_h(R1)
        AA, BB = matrix(R1, Al), matrix(R1, Bl)
        expd = f4(mexp(-w * (u * AA + v * BB)) * hh)
        first = expd.derivative(w).subs({w: R1(0)})
        check(first == u * D_at(AA, hh) + v * D_at(BB, hh),
              'D_(u X + v Y) f = u D_X f + v D_Y f')
    # Lemma 36: S_a, on the unitriangular group with symbolic r.
    Rq = PolynomialRing(QQ, 'r')
    rq = Rq.gen()
    aa = matrix(Rq, [[1, 2, 3, 0], [0, 1, 1, 1], [0, 0, 1, -1], [0, 0, 0, 1]])
    bb = matrix(Rq, [[1, 0, 1, 2], [0, 1, 3, 1], [0, 0, 1, 2], [0, 0, 0, 1]])
    A = matrix(Rq, pairs[0][0])
    B = matrix(Rq, pairs[0][1])
    S = lambda g, M: g * M * g.inverse()
    check(aa * mexp(rq * A) * aa.inverse() == mexp(rq * S(aa, A)),
          'a exp(r A) a^(-1) = exp(r S_a A)')
    check(S(aa * bb, A) == S(aa, S(bb, A)), 'S_(a b) = S_a S_b')
    check(S(aa, A + 2 * B) == S(aa, A) + 2 * S(aa, B), 'S_a is linear')
    check(S(identity_matrix(Rq, 4), A) == A, 'S_1 = I')


# --------------------------------------------------------------- lemma 39
def enclosure_exp(x, K=60):
    """Rational enclosure of exp(x) for |x| <= 3, by the alternating or positive
    Taylor remainder bound."""
    s, term = QQ(0), QQ(1)
    for k in range(K):
        s += term
        term = term * x / (k + 1)
    rem = abs(term) * 2
    return s - rem, s + rem


def lemma_39():
    # (29) as an identity in e = 1/N: f(Z(-1) Y(1) h) - f(h) =
    # e int_0^1 [Y(-1) Z(1 - t) Y(t) D_(X_t) f](h) dt, Z = Y + e X.
    R = ring4(['t', 'e'])
    t, e = R('t'), R('e')
    h = gen_h(R)
    for Al, Bl in [([[0, 1, 2, 0], [0, 0, 1, 3], [0, 0, 0, 1], [0, 0, 0, 0]],
                    [[0, 2, 0, 1], [0, 0, -1, 1], [0, 0, 0, 2], [0, 0, 0, 0]])]:
        A, B = matrix(R, Al), matrix(R, Bl)
        C = B + e * A
        left = f4(mexp(-C) * mexp(B) * h) - f4(h)
        Yt, Ymt = mexp(t * B), mexp(-t * B)
        At = Ymt * A * Yt
        arg = Ymt * mexp((t - 1) * C) * mexp(B) * h
        F = D_at(At, arg).integral(t)
        val = e * (F.subs({t: R(1)}) - F.subs({t: R(0)}))
        check(left == val, '(28) = (29): N cancels')
        # Gamma(-Y) X is the first order in e of exp(-B) exp(B + e A).
        P2 = mexp(-B) * mexp(C)
        first = P2.apply_map(lambda p: p.derivative(e).subs({e: R(0)}))
        ad = lambda M: B * M - M * B
        G = A - ad(A) / 2 + ad(ad(A)) / 6 - ad(ad(ad(A))) / 24
        check(first == G, 'the limit of lemma 39 in general is Gamma(-Y) X')
    # The refutation on the unitriangular 3 x 3 group, over QQ[y, e].
    P3 = PolynomialRing(QQ, 'y,e')
    y, e = P3.gens()
    E12 = matrix(P3, [[0, 1, 0], [0, 0, 0], [0, 0, 0]])
    E23 = matrix(P3, [[0, 0, 0], [0, 0, 1], [0, 0, 0]])
    E13 = matrix(P3, [[0, 0, 1], [0, 0, 0], [0, 0, 0]])
    I3 = identity_matrix(P3, 3)
    p = mexp(-y * E23) * mexp(y * E23 + e * E12)
    check(p == I3 + e * E12 + (y * e / 2) * E13, 'p = I + e A + (y e/2) E_13')
    for k in range(1, 15):
        check(p ** k == I3 + k * e * E12 + (k * y * e / 2) * E13, 'powers of p')
    for yv in (QQ(1), QQ(-2), QQ(1) / 3):
        # N -> oo, k = [r N]: the limit is I + r E12 + (r y/2) E13, X(r) = I + r E12.
        for r in (QQ(1) / 2, QQ(1), QQ(2)):
            for N in (10, 1000, 100000):
                k = floor(r * N)
                v12, v13 = QQ(k) / N, QQ(k) / N * yv / 2
                check(abs(v12 - r) <= QQ(1) / N, 'the (1, 2) entry tends to r')
                check(abs(v13 - r * yv / 2) <= abs(yv) / N,
                      'the (1, 3) entry tends to r y/2')
            refuted(r * yv / 2 == 0, 'p. 129, the printed lemma 39: limit is X')
    # The corrected statement: y_i -> 0, then the (1, 3) entry tends to 0.
    for i in (10, 100, 1000):
        yi, N, r = QQ(1) / i, i ** 2, QQ(3) / 2
        k = floor(r * N)
        check(abs(QQ(k) / N * yi / 2) <= r * yi, 'with Y_i -> 0 the limit is X')
    # GL_2(R): the closed form of exp [[t, e], [0, -t]] over QQ(t, e)[a, b].
    K = PolynomialRing(QQ, 't,e').fraction_field()
    tt, ee = K.gens()
    Rab = PolynomialRing(K, 'a,b')
    a, b = Rab.gens()

    def d(pol):        # d/ds with a = exp(s t), b = exp(-s t)
        return tt * a * pol.derivative(a) - tt * b * pol.derivative(b)
    E = matrix(Rab, [[a, ee * (a - b) / (2 * tt)], [0, b]])
    M = matrix(Rab, [[tt, ee], [0, -tt]])
    check(E.apply_map(d) == M * E, "E' = M E")
    check(E.apply_map(lambda p: p.subs({a: Rab(1), b: Rab(1)}))
          == identity_matrix(Rab, 2), 'E(0) = I')
    check(M ** 2 == tt ** 2 * identity_matrix(Rab, 2), 'M^2 = t^2 I')
    pp = matrix(Rab, [[b, 0], [0, a]]) * E     # Y(-1) Z_i(1)
    # reduce modulo a b = 1
    check((pp[0, 0] - (a * b)) == 0 and (pp[1, 1] - (a * b)) == 0
          and pp[1, 0] == 0, 'the diagonal is a b = 1')
    check(pp[0, 1] == ee * (a * b - b ** 2) / (2 * tt),
          'the corner is e (a b - b^2)/(2 t) = e (1 - b^2)/(2 t)')
    # The same by the power series of exp M, order 30, over QQ[e][[t]].
    Pe = PolynomialRing(QQ, 'e')
    ev = Pe.gen()
    Rs = PowerSeriesRing(Pe, 't', default_prec=31)
    ts = Rs.gen()
    Ms = matrix(Rs, [[ts, ev], [0, -ts]])
    Sum = identity_matrix(Rs, 2)
    T = identity_matrix(Rs, 2)
    for k in range(1, 40):
        T = (T * Ms) / k
        T = T.apply_map(lambda c: c.add_bigoh(31))
        Sum = Sum + T
    exp_t = sum(ts ** k / factorial(k) for k in range(31)).add_bigoh(31)
    exp_mt = sum((-ts) ** k / factorial(k) for k in range(31)).add_bigoh(31)
    check((Sum[0, 0] - exp_t).add_bigoh(30) == 0, 'series: entry (1, 1)')
    corner = (exp_t - exp_mt).add_bigoh(31)
    # (a - b)/(2 t) as a power series
    half = (corner.shift(-1) / 2)
    check((Sum[0, 1] - ev * half).add_bigoh(29) == 0, 'series: entry (1, 2)')
    c_series = (1 - exp_mt ** 2).add_bigoh(30).shift(-1) / 2
    check(c_series[0] == 1 and c_series[1] == -1 and c_series[2] == QQ(2) / 3,
          'c = 1 - t + (2/3) t^2 - ...')
    # c(t) != 1 for t != 0, with rational enclosures.
    for tv in (QQ(1), QQ(2), QQ(-1), QQ(1) / 2, QQ(-1) / 2, QQ(1) / 10):
        lo, hi = enclosure_exp(-2 * tv)
        c1, c2 = (1 - hi) / (2 * tv), (1 - lo) / (2 * tv)
        c_lo, c_hi = min(c1, c2), max(c1, c2)
        refuted(c_lo <= 1 <= c_hi, 'the printed lemma 39 on GL_2: c = 1')
        # and Y(-1) Z_N(1) = I + (c/N) E_12 has powers I + (c [r N]/N) E_12
    # With t_i -> 0: c(t_i) -> 1, the corrected statement on GL_2.
    for i in (10, 100, 1000):
        tv = QQ(1) / i
        lo, hi = enclosure_exp(-2 * tv)
        c1, c2 = (1 - hi) / (2 * tv), (1 - lo) / (2 * tv)
        check(abs(c1 - 1) <= 2 * tv and abs(c2 - 1) <= 2 * tv,
              'c(t_i) tends to 1')


# ----------------------------------------------------------- steps and examples
def bump(x):
    return (1 - x ** 2) ** 2 if abs(x) <= 1 else QQ(0)


def dbump(x):
    return -4 * x * (1 - x ** 2) if abs(x) <= 1 else QQ(0)


def circ(x):
    x = QQ(x)
    return x - floor(x + QQ(1) / 2)


def steps():
    # Lemma 35: the factor is 1 or a_j.
    seen = set()
    for m in list(range(1, 30)) + [97, 100]:
        for r in [QQ(a) / b for b in range(1, 9) for a in range(0, 3 * b + 1)]:
            for s in [QQ(a) / b for b in range(1, 7) for a in range(0, b + 1)]:
                if s <= r:
                    d = floor(r * m) - floor(s * m) - floor((r - s) * m)
                    check(d in (0, 1), 'lemma 35: exponents differ by 0 or 1')
                    seen.add(d)
    check(seen == {0, 1}, 'both 1 and a_j occur as the factor')
    refuted(2 in seen, 'p. 126: the printed factor a_j^2 occurs')
    # Lemma 19 on the line, U = [-1, 1], Q_h = [-1/h, 1/h], n_h = h + 1, A = 1.
    for h in range(1, 60):
        a = b = QQ(1) / h
        refuted(abs(a + b) <= QQ(1) / h, 'p. 115: the printed a b in Q (no square)')
        check(abs(a + b) <= QQ(2) / h, 'a b lies in Q^2')
        n = h + 1
        if h % 2 == 1:
            s = n // 2
            check(2 * s == n, 'the case 2 s = n')
            refuted(abs(s * (a + b)) <= 1,
                    'p. 115: the printed step (a b)^s in U if 2 s <= n')
        # 2 s < n implies Q^(2 s) in U
        for s in range(0, h):
            if 2 * s < n:
                check(QQ(2 * s) / h <= 1, 'corrected: 2 s < n gives (a b)^s in U')
    # The corrected chain, with A > i/n_i: n > [k m]/A, 2 [k m/2 A] <= [k m]/A.
    for k in (QQ(1) / 2, QQ(1), QQ(3) / 2, QQ(2)):
        for m in range(1, 80):
            h = floor(k * m)
            if h == 0:
                continue
            for n in range(1, 2 * h + 2):
                # all A > h/n
                A = floor(QQ(h) / n) + 1
                check(QQ(n) / h > QQ(1) / A, 'n/i > 1/A')
                check(n > QQ(h) / A, '(18), strict')
                s = floor(k * m / (2 * A))
                check(s <= QQ(h) / (2 * A), 'the last display of p. 115')
                check(2 * A * s <= k * m and 2 * A * s <= h, 'p. 116')
                check(2 * s < n, 'hence 2 s < n: the module k/2 A stays')
    # GL_2(QQ), U = {||g - I|| <= 1/2}: a = I + E_12/(2 h), b = I + E_21/(2 h) lie
    # in Q_h, the powers of a b stay in U up to a fixed fraction of h.
    I2 = identity_matrix(QQ, 2)
    for h in (4, 8, 16, 32, 64, 128):
        a = I2 + matrix(QQ, [[0, 1], [0, 0]]) / (2 * h)
        b = I2 + matrix(QQ, [[0, 0], [1, 0]]) / (2 * h)
        check(norm_inf(a ** h - I2) <= QQ(1) / 2 and
              norm_inf(b ** h - I2) <= QQ(1) / 2, 'a, b lie in Q_h')
        c = a * b
        P, j = c, 1
        while norm_inf(P - I2) <= QQ(1) / 2:
            P, j = P * c, j + 1
        check(j - 1 >= QQ(h) / 3, 'lemma 19 on GL_2: module at least 1/3')
    # P. 119: the functions are m {X_i(1/m) f - f}; X(1/m) is another element.
    xs = [QQ(a) / 16 for a in range(-20, 21)]
    c, ci = QQ(1), QQ(1) + QQ(1) / 10
    m = 100
    refuted(all(bump(x - c / m) == bump(x - ci / m) for x in xs),
            'p. 119: X(1/m_i) and X_i(1/m_i) give the same functions')
    for j in (10, 100, 1000):
        ci = 1 + QQ(1) / j
        m = j ** 2
        for x in xs:
            lim = -c * dbump(x)
            val = m * (bump(x - ci / m) - bump(x))
            check(abs(val - lim) <= 4 * ci ** 2 / m + 16 * abs(ci - c),
                  'lemma 27 on the line: m {X_i(1/m) f - f} -> D_X f')
    # P. 120: the image of K_1 = {|c| <= 1} is no subspace; the image of L is.
    x0 = QQ(1) / 2
    v = -dbump(x0)
    check(v != 0, 'f is not constant')
    refuted(abs(QQ(2)) <= 1, 'p. 120: 2 D_X f is the image of an element of K_1')
    # P. 124, lemma 33 on the line, K_1 = [-1, 1].
    for T in (1, 2, 5):
        for b_ in (2, 10):
            eps = QQ(1) / b_
            i = b_ + 1
            s = QQ(1) / T
            r = s / i
            check(i * r == s, '(i r) X = s X')
            for c in (QQ(T), QQ(-T), QQ(T) / 2):
                check(abs(s * c) <= 1, 's X lies in K_1')
                for t in (r, -r, r / 3):
                    check(abs(c * t) <= QQ(1) / i < eps, 'X(t) lies in V')
                    check(all(abs(j * c * t) <= 1 for j in range(1, i + 1)),
                          'X(t), ..., X(t)^i lie in U')
    # Lemma 30, 31, 29, 35 on the line and on the Heisenberg group.
    for N in (10, 100, 1000, 10000):
        a = QQ(1) / N ** 2
        check(abs(N * a) <= QQ(1) / N, 'lemma 30: m (a f - f) -> 0 with a = 1/N^2')
        check(all(abs(j * a) <= 1 for j in (1, N)), 'lemma 30: standard, limit 0')
        for r in (QQ(1) / 2, QQ(2)):
            check(abs(floor(r * N) * a) <= r / N, 'lemma 30: converges to 0')
            for c in (QQ(1), QQ(-3)):
                a2 = c / N + QQ(1) / N ** 2
                check(abs(floor(r * N) * a2 - c * r) <= (abs(c) + r) / N,
                      'lemma 31: the sequence converges to X')
    E12 = matrix(QQ, [[0, 1, 0], [0, 0, 0], [0, 0, 0]])
    E23 = matrix(QQ, [[0, 0, 0], [0, 0, 1], [0, 0, 0]])
    E13 = matrix(QQ, [[0, 0, 1], [0, 0, 0], [0, 0, 0]])
    I3 = identity_matrix(QQ, 3)
    for N in (10, 100, 1000):
        a = mexp(E12 / N) * (I3 + E13 / N ** 2)
        b = mexp(E23 / N)
        for r in (QQ(1) / 2, QQ(1), QQ(2)):
            k = floor(r * N)
            Z = mexp(r * (E12 + E23))
            check(norm_inf(Z.inverse() * (a * b) ** k - I3) <= QQ(16) / N,
                  'lemma 29 on the Heisenberg group')
            X = mexp(r * E12)
            check(norm_inf(X.inverse() * a ** k - I3) <= QQ(8) / N,
                  'lemma 35 on the Heisenberg group, uniformly in r')
    # Uniqueness at p. 119.  The circle with U = {|x| <= 1/5}: K_1 = {|c| <= 1/5},
    # c -> c mod 1 is injective.  With U = the whole circle it is not: c = 0 and
    # c = 1 give the same value at 1.
    vals = {}
    for a_ in range(-20, 21):
        c = QQ(a_) / 100
        if abs(c) <= QQ(1) / 5:
            check(all(abs(circ(t * c)) <= QQ(1) / 5
                      for t in (QQ(-1), QQ(-1) / 2, QQ(1) / 2, QQ(1))), 'c in K_1')
            v1 = circ(c)
            check(v1 not in vals, 'X -> X(1) is injective on K_1')
            vals[v1] = c
    check(circ(QQ(1)) == circ(QQ(0)) and QQ(1) != QQ(0),
          'c = 0, c = 1 agree at 1')
    refuted(circ(QQ(1) / 2) == circ(QQ(0)),
            'but they differ at 1/2: no uniqueness without square roots')
    # Lemma 28 on the line: X(t) = c t, c > 1: lambda = 1/c < 1, X(lambda) on the
    # boundary, lambda X in K_1.
    for c in (QQ(3) / 2, QQ(2), QQ(100)):
        lam = 1 / c
        check(lam < 1 and c * lam == 1, 'X(lambda) lies on the boundary')
    # Lemma 38 on the line: W = r K_1, r = eps/2.
    for eps in (QQ(1) / 2, QQ(1) / 100):
        r = eps / 2
        for c in (r, -r, r / 2):
            for t in (QQ(1), QQ(-1), QQ(1) / 2):
                check(abs(c * t) < eps, 'lemma 38')
    # Lemma 40 on the Heisenberg group: every g in the box of radius 1/2 has the
    # form X(1), X in K_1, where (a, b, c) = exp(a E12 + b E23 + (c - a b/2) E13).
    grid = [QQ(j) / 8 for j in range(-4, 5)]
    for a in grid:
        for b in grid:
            for c in grid:
                g = I3 + a * E12 + b * E23 + c * E13
                L = a * E12 + b * E23 + (c - a * b / 2) * E13
                check(mexp(L) == g, 'g = exp(L)')
                for t in (QQ(-1), QQ(-1) / 2, QQ(1) / 4, QQ(1) / 2, QQ(3) / 4, QQ(1)):
                    h = mexp(t * L)
                    check(all(abs(h[i, j]) <= 1 for i in range(3)
                              for j in range(i + 1, 3)), 'X(t) lies in U')
    # Theorem 16: Heisenberg -> R^2, R -> circle: explicit lifts.
    for al, be in ((QQ(1), QQ(0)), (QQ(1) / 2, QQ(-3))):
        for t in (QQ(1) / 3, QQ(-2), QQ(5)):
            g = mexp(t * (al * E12 + be * E23))
            check((g[0, 1], g[1, 2]) == (t * al, t * be), 'the lift of (al t, be t)')
    for c in (QQ(1) / 7, QQ(-3) / 2):
        for t in (QQ(1) / 3, QQ(-2)):
            check(circ(c * t + 5) == circ(c * t), 'c t mod 1')


def main():
    identities()
    integral()
    lemma_39()
    steps()
    print('ok %s: %d checks' % (SCOPE, COUNT[0]))


if __name__ == '__main__':
    main()
