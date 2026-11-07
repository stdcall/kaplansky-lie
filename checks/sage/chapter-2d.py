"""Exact checks of Chapter II, §§ 10-11 (printed pp. 132-143) of I. Kaplansky,
"Алгебры Ли и локально компактные группы" (Москва: Мир, 1974): approximation by
NSS groups and the survey of the further development.

Run from the project root: sage -python checks/sage/chapter-2d.py
(plain asserts; do not use -O).  The last line is "ok chapter-2d: N checks".
Pages are the printed pages; labels are those of content/02-*.typ.  Expected
values are the book's; a printed reading that is wrong is kept as a refuted
check (`refuted`) beside the corrected one.  All arithmetic is exact: QQ,
QQ(sqrt 2), Z/p^K, polynomial rings and power series over QQ.

section_10 (pp. 132-139).
  eq:power-shift-expansion as a polynomial identity (free module on psi, tau over
  QQ[a]) for n <= 15.  The Schwarz step in the proof of th:yamabe-small-subgroup:
  on Z/4 and S_3, for all phi with values in {0, 1/2, 1}, phi(1) = 1: psi(c) =
  psi(1) implies phi(c) = 1 (it does not exclude c != 1: phi may be non-proper).
  lem:neighbourhood-sequence: on the line, U = [-1, 1], the printed statement (for
  N without 1) refuted, a ball from the printed list that gives an empty symmetric
  set exhibited, and the corrected list (unions containing 0, with closure in U)
  checked to contain W_j with N subset W_j subset closure subset V, for N, V in a
  list.  lem:yamabe-tight: a Yamabe system with Q not in U has q psi - psi nonzero
  outside U^5 (G = R, U = [-1, 1], Q = [-10, 10], n = 1), inside the compact set of
  the corrected reading.  Definition of a Yamabe system, Theorem 17 on Z/p^K x R:
  subgroups in V = p^a Z/p^K x (-1/2, 1/2) lie in the first factor; on Z/p^K all
  subgroups in p^a Z/p^K generate inside it.
  p-adic groups: the congruence subgroups Gamma_k of GL_2(Z/p^K) are subgroups, for
  (p, K) = (2, 3), (3, 2), all elements: GL_2(Q_p) and PSL_2(Q_p) have small
  subgroups (the example in the remark after th:approximation-nss; the simplicity
  of PSL_2 is from the literature).
  The solenoid S_p (th:approximation-nss, items 3, 5, 6 of § 11): on rational points
  at level K, the coherent sequences x_k = p^(K-k) x_K: N_k is a subgroup, its order
  p^(K-k), S_p/N_k = circle by the coordinate x_k, the lift t -> (t/p^k)_k of the
  one-parameter subgroup of S_p/N_0.  T^n, the quotients of T^oo: dimension
  unbounded (item 4).
section_11 (pp. 139-143).
  Item 3 (a), the group G/(N inter H): the kernel of G -> G/N x G/H is N inter H,
  for all pairs of normal subgroups of S_4, D_4, Q_8, Z/12 (from GAP, libgap).
  Items 9-12 on gl_n: S_(exp(t A)) = exp(t ad A) in QQ[[t]] mod t^12 for gl_2, gl_3
  and over QQ[t] on the strictly upper triangular matrices (4 x 4); Lambda(A) = ad A,
  [A, A] = 0, bilinear; item 10: the group commutator in the Heisenberg group: limit
  I + r E_13 = exp(r [A, B]) (sign checked, -E_13 refuted), the inner limit
  exp(r i (B' - B)) with a rate and the outer limit i (B' - B) -> [A, B] as an exact
  polynomial in 1/i (4 x 4), the second order term of the commutator on gl_2; item
  11: ad [A, B] = [ad A, ad B], tr [A, B] = 0; item 12: Jacobi, n = 2, 3 symbolic.
  Item 13: sl_n ideal in gl_n, det exp(t A) = exp(t tr A) in QQ[[t]]; the centre of
  the Heisenberg algebra.  Item 14: the line (t, t sqrt 2) in T^2: injective over
  QQ(sqrt 2) and not closed (Pell, exact |n - m sqrt 2| -> 0); the subalgebra.
  Item 15: on strictly upper triangular 4 x 4 and 5 x 5 matrices, W(t) = log(exp X
  exp(t Z)): formula eq:product-differential-equation, W' = Delta(-W) Z, exact over
  QQ[t], with Gamma(V) = sum (ad V)^k/(k + 1)! = int_0^1 S_(V(t)) dt; the readings
  Delta(W) Z and Delta((-X) x t Z) Z refuted, so that the printed -X x t Z is
  -(X x t Z); the derivative of (-X) x (X + t Y) at t = 0 is Gamma(-X) Y.

What this does NOT establish: the theorems of § 10 or any item of § 11 in general.
The items of § 11 are a survey: most are confirmed by the literature, by an exact
computation here or by a derivation by hand; item 15 only describes its proof, which
is not reconstructed.
"""
from sage.all import (QQ, ZZ, PolynomialRing, PowerSeriesRing, QuadraticField,
                      matrix, identity_matrix, zero_matrix, floor, factorial,
                      SymmetricGroup, DihedralGroup, QuaternionGroup,
                      CyclicPermutationGroup, libgap)
import itertools

SCOPE = 'chapter-2d'
COUNT = [0]


def check(cond, what):
    assert bool(cond), what
    COUNT[0] += 1


def refuted(cond, what):
    assert not bool(cond), 'not refuted: ' + what
    COUNT[0] += 1


def norm_inf(M):
    return max(sum(abs(e) for e in row) for row in M.rows())


def mexp(M):
    n = M.nrows()
    R = M.base_ring()
    out = identity_matrix(R, n)
    T = identity_matrix(R, n)
    for k in range(1, n):
        T = T * M / k
        out = out + T
    return out


def mlog(M):
    """log of a unitriangular matrix."""
    n = M.nrows()
    R = M.base_ring()
    N = M - identity_matrix(R, n)
    out = zero_matrix(R, n, n)
    T = identity_matrix(R, n)
    for k in range(1, n):
        T = T * N
        out = out + (T / k if k % 2 == 1 else -T / k)
    return out


# ---------------------------------------------------------------- § 10
def section_10():
    # (30): a^n psi - psi = (1/n) sum a^t (gamma - tau)
    #                        + (1/n) sum (a^t tau - tau) + tau,
    # gamma = n (a psi - psi); coefficient of psi and of tau, over QQ[a].
    P = PolynomialRing(QQ, 'a')
    a = P.gen()
    for n in range(1, 16):
        # gamma - tau has coefficients (n (a - 1), -1)
        c_psi = sum(a ** t * n * (a - 1) for t in range(n)) / n
        c_tau = sum(-a ** t for t in range(n)) / n + sum(a ** t - 1 for t in range(n)) / n + 1
        check(c_psi == a ** n - 1 and c_tau == 0, '(30), n = %d' % n)
    # The Schwarz step: on a finite group, psi(c) = psi(1) implies phi(c) = 1, for
    # all phi with phi(1) = 1, values in {0, 1/2, 1}.
    Z4 = [[(i + j) % 4 for j in range(4)] for i in range(4)]
    inv4 = [(-i) % 4 for i in range(4)]
    S3 = SymmetricGroup(3).list()
    S3 = [SymmetricGroup(3).identity()] + [g for g in S3 if g != SymmetricGroup(3).identity()]
    idx = {g: i for i, g in enumerate(S3)}
    mulS = [[idx[x * y] for y in S3] for x in S3]
    for mul, N in ((Z4, 4), (mulS, 6)):
        nonproper = 0
        for vals in itertools.product((QQ(0), QQ(1) / 2, QQ(1)), repeat=N - 1):
            phi = (QQ(1),) + vals
            psi = [sum(phi[mul[u][x]] * phi[x] for x in range(N)) for u in range(N)]
            for c in range(1, N):
                check(psi[c] <= psi[0], 'Cauchy-Schwarz')
                if psi[c] == psi[0]:
                    check(phi[c] == 1, 'psi(c) = psi(1) implies phi(c) = 1')
                    nonproper += 1
        check(nonproper > 0, 'the equality case does occur')
    # Lemma 42 on the line, U = [-1, 1].  The printed statement fails for N
    # without 1: N = {+-1/3}, V = (-1/2, -1/4) union (1/4, 1/2) has no neighbourhood
    # of 0 inside it.
    N_bad = (QQ(1) / 3, QQ(-1) / 3)
    check(all(QQ(1) / 4 < abs(x) < QQ(1) / 2 for x in N_bad) and
          not (QQ(1) / 4 < 0 < QQ(1) / 2), 'N subset V, 0 is not in V')
    refuted(QQ(1) / 4 < 0 < QQ(1) / 2,
            'p. 134: a neighbourhood W_j of 1 lies in this V')
    # The printed list contains sets that are not neighbourhoods of 1: the ball
    # of centre 1/2, radius 1/4, intersected with its inverse, is empty.
    lo, hi = QQ(1) / 4, QQ(3) / 4
    refuted(max(lo, -hi) < min(hi, -lo), 'the symmetric set of this ball is nonempty')
    # The corrected list: finite unions of balls (u, r) with rational centre in U,
    # rational radius, containing 0, closure in U.  For N containing 0 and V open
    # symmetric in U, W_j exists.  On the line a symmetric interval suffices.
    data = [
        (QQ(1) / 2, QQ(3) / 4),         # N = [-1/2, 1/2], V = (-3/4, 3/4)
        (QQ(0), QQ(1) / 100),
        (QQ(9) / 10, QQ(1)),
    ]
    for rN, rV in data:
        rW = (rN + rV) / 2
        rC = (rW + rV) / 2
        check(rN < rW < rC < rV <= 1, 'N subset W subset closure W subset V')
        check(rW in QQ and -rW <= 0 <= rW, 'the ball (0, r_W) is in the list')
    # Yamabe system with Q not in U: support outside U^5.  G = R, U = [-1, 1],
    # Q = [-10, 10]: n = 1, Delta = 1 off 0, phi = theta, psi = theta * theta with
    # support [-2, 2], psi(0) = 2/3.
    psi0 = QQ(2) / 3
    def psi_t(u):
        # the autocorrelation of the triangle function theta(x) = max(0, 1 - |x|)
        u = abs(QQ(u))
        if u >= 2:
            return QQ(0)
        if u <= 1:
            return QQ(2) / 3 - u ** 2 + u ** 3 / 2
        return (2 - u) ** 3 / 6
    check(psi_t(0) == psi0 and psi_t(1) == QQ(1) / 6, 'psi at 0, 1')
    q = QQ(10)
    refuted(psi_t(q - q) - psi_t(q) == 0,
            'p. 136: q psi - psi vanishes outside U^5, for q in Q')
    check(abs(q) > 5, 'q is outside U^5')
    check(abs(q) <= 10 + 4, 'q lies in the compact set (closure of Q) U^4')
    # Theorem 17 on Z/p^K x R: every subgroup in V = p^a Z/p^K x (-1/2, 1/2) lies
    # in the first factor, as an element with t != 0 has a multiple outside.
    for p_, K in ((2, 4), (3, 3), (5, 2)):
        M = p_ ** K
        for a_ in range(0, K + 1):
            sub = [x for x in range(M) if x % p_ ** a_ == 0]
            check(all((x + y) % M in sub for x in sub for y in sub),
                  'p^a Z/p^K is a subgroup')
            for t in (QQ(1) / 3, QQ(-1) / 7, QQ(1) / 100):
                k = floor(QQ(1) / 2 / abs(t)) + 1
                check(abs(k * t) >= QQ(1) / 2, 'multiple of (z, t) leaves V')
    # GL_2(Z/p^K): the congruence subgroups.
    for p_, K in ((2, 3), (3, 2)):
        M = p_ ** K
        for k in range(1, K):
            step = p_ ** k
            els = []
            for e in itertools.product(range(0, M, step), repeat=4):
                els.append(((1 + e[0]) % M, e[1], e[2], (1 + e[3]) % M))
            S = set(els)
            check(len(S) == (M // step) ** 4 and len(S) > 1, 'Gamma_k has several elements')
            for x in els:
                for y in els:
                    z = ((x[0] * y[0] + x[1] * y[2]) % M,
                         (x[0] * y[1] + x[1] * y[3]) % M,
                         (x[2] * y[0] + x[3] * y[2]) % M,
                         (x[2] * y[1] + x[3] * y[3]) % M)
                    check(z in S, 'Gamma_k is closed under multiplication')
            # a nonscalar element: the image in PSL_2 is not trivial
            check((1, step, 0, 1) in S, 'I + p^k E_12 lies in Gamma_k')
    # The solenoid at level K: x_k = p^(K-k) x_K in Q/Z.
    def fr(x):
        x = QQ(x)
        return x - floor(x)
    for p_ in (2, 3):
        K = 5
        for x in (QQ(1) / p_ ** 3, QQ(5) / p_ ** 4, QQ(1) / 7, QQ(2) / 11):
            seq = [fr(p_ ** (K - k) * x) for k in range(K + 1)]
            check(all(fr(p_ * seq[k + 1]) == seq[k] for k in range(K)),
                  'coherent: p x_(k+1) = x_k')
        for k in range(K + 1):
            order = p_ ** (K - k)
            Nk = [fr(QQ(j) / order) for j in range(order)]
            check(all(fr(p_ ** (K - k) * z) == 0 for z in Nk), 'x_k = 0 on N_k')
            check(all(fr(p_ ** (K - i) * z) == 0 for z in Nk for i in range(k + 1)),
                  'x_i = 0 for i <= k on N_k: N_k lies in small neighbourhoods')
            check(all(fr(y + z) in Nk for y in Nk for z in Nk), 'N_k is a subgroup')
            check(len(Nk) == order, 'its order at level K is p^(K-k)')
        # the lift of Y(t) = t mod 1 through S_p -> S_p/N_0 = circle: X(t) = (t/p^k)_k
        for t in (QQ(1) / 3, QQ(7) / 5, QQ(-2)):
            seq = [fr(t / p_ ** k) for k in range(K + 1)]
            check(all(fr(p_ * seq[k + 1]) == seq[k] for k in range(K)),
                  'the lift is coherent')
            check(seq[0] == fr(t), 'and it projects to Y(t)')
            for s in (QQ(1) / 2, QQ(5)):
                seq2 = [fr((t + s) / p_ ** k) for k in range(K + 1)]
                seq3 = [fr(t / p_ ** k + s / p_ ** k) for k in range(K + 1)]
                check(seq2 == seq3, 'the lift is a homomorphism')
    # T^n: the quotients of T^oo have unbounded dimension: the box (coordinates
    # k + 1, ... free) contains N_k, a subgroup: item 4, exercise 4 of § 1.
    for n in range(1, 8):
        e = [QQ(1) / 3 if j >= n else QQ(0) for j in range(n + 3)]
        check(all(e[j] == 0 for j in range(n)) and any(v != 0 for v in e),
              'an element of N_n')


# ---------------------------------------------------------------- § 11
def normal_subgroups_kernel():
    for G in (SymmetricGroup(4), DihedralGroup(4), QuaternionGroup(),
              CyclicPermutationGroup(12)):
        g = libgap(G)
        Ns = list(libgap.NormalSubgroups(g))
        for N in Ns:
            for H in Ns:
                piN = libgap.NaturalHomomorphismByNormalSubgroup(g, N)
                piH = libgap.NaturalHomomorphismByNormalSubgroup(g, H)
                KN = libgap.Kernel(piN)
                KH = libgap.Kernel(piH)
                I = libgap.Intersection(KN, KH)
                check(libgap.Size(I) == libgap.Size(libgap.Intersection(N, H)),
                      'kernel of G -> G/N x G/H is the intersection')
                check(libgap.IsNormal(g, I), 'and it is normal')
                # and G/(N inter H) embeds: its order divides |G/N| |G/H|
                oq = libgap.Size(g) / libgap.Size(I)
                check(ZZ(libgap.Size(g) / libgap.Size(N)) *
                      ZZ(libgap.Size(g) / libgap.Size(H)) % ZZ(oq) == 0,
                      'item 3 (a): G/(N inter H) lies in G/N x G/H')


def ad(A, B):
    return A * B - B * A


def items_9_12():
    Rs = PowerSeriesRing(QQ, 't', default_prec=12)
    t = Rs.gen()
    for A0, B0 in (([[1, 2], [3, 4]], [[0, 1], [-1, 5]]),
                   ([[0, 1, 2], [1, 0, 0], [3, 1, 1]],
                    [[2, 0, -1], [0, 1, 1], [1, -1, 0]])):
        n = len(A0)
        A = matrix(Rs, A0)
        B = matrix(Rs, B0)
        I = identity_matrix(Rs, n)

        def ser(M, s):
            out, T = I, I
            for k in range(1, 12):
                T = T * M * s / k
                out = out + T
            return out.apply_map(lambda c: c.add_bigoh(12))
        L = ser(A, t) * B * ser(A, -t)
        L = L.apply_map(lambda c: c.add_bigoh(12))
        R = B
        T = B
        for k in range(1, 12):
            T = ad(A, T) * t / k
            R = R + T
        R = R.apply_map(lambda c: c.add_bigoh(12))
        check(L == R, 'S_(exp(t A)) = exp(t ad A) mod t^12')
        check(L.apply_map(lambda c: c[1]) == ad(A, B).apply_map(lambda c: c[0]),
              'Lambda(X) Y is the commutator [A, B]')
        check(ad(A, A) == 0 and ad(A, B) == -ad(B, A), 'anticommutative')
    # exact, on the strictly upper triangular 4 x 4 matrices, over QQ[t]:
    Rt = PolynomialRing(QQ, 't')
    tt = Rt.gen()
    A = matrix(Rt, [[0, 1, 2, 0], [0, 0, 1, 3], [0, 0, 0, 1], [0, 0, 0, 0]])
    B = matrix(Rt, [[0, 2, 0, 1], [0, 0, -1, 1], [0, 0, 0, 2], [0, 0, 0, 0]])
    L = mexp(tt * A) * B * mexp(-tt * A)
    R = B
    T = B
    for k in range(1, 7):
        T = ad(A, T) * tt / k
        R = R + T
    check(L == R, 'S_(exp(t A)) = exp(t ad A), exact')
    # Item 10.  Heisenberg: g = exp(A/i) exp(B/j) exp(-A/i) exp(-B/j) = I + E_13/(i j).
    E12 = matrix(QQ, [[0, 1, 0], [0, 0, 0], [0, 0, 0]])
    E23 = matrix(QQ, [[0, 0, 0], [0, 0, 1], [0, 0, 0]])
    E13 = matrix(QQ, [[0, 0, 1], [0, 0, 0], [0, 0, 0]])
    I3 = identity_matrix(QQ, 3)
    check(ad(E12, E23) == E13, '[A, B] = E_13')
    for i in (1, 2, 5, 10):
        for j in (1, 3, 10, 100):
            g = mexp(E12 / i) * mexp(E23 / j) * mexp(-E12 / i) * mexp(-E23 / j)
            check(g == I3 + E13 / (i * j), 'the group commutator is I + E_13/(i j)')
            for r in (QQ(1) / 2, QQ(1), QQ(5) / 3):
                k = floor(r * i * j)
                G = g ** k
                check(abs(G[0, 2] - r) <= QQ(1) / (i * j), 'the limit is r')
                if r * i * j > 1:
                    refuted(abs(G[0, 2] + r) <= QQ(1) / (i * j),
                            'the opposite sign exp(-r [A, B])')
    # 4 x 4: inner limit j -> oo, outer limit i -> oo.
    Aq = matrix(QQ, [[0, 1, 2, 0], [0, 0, 1, 3], [0, 0, 0, 1], [0, 0, 0, 0]])
    Bq = matrix(QQ, [[0, 2, 0, 1], [0, 0, -1, 1], [0, 0, 0, 2], [0, 0, 0, 0]])
    I4 = identity_matrix(QQ, 4)
    for i in (1, 2, 3):
        Bp = mexp(Aq / i) * Bq * mexp(-Aq / i)
        r = QQ(1)
        target = mexp(r * i * (Bp - Bq))
        errs = []
        for j in (10, 100, 1000):
            g = mexp(Aq / i) * mexp(Bq / j) * mexp(-Aq / i) * mexp(-Bq / j)
            k = floor(r * i * j)
            errs.append(norm_inf(target.inverse() * g ** k - I4) * j)
        check(errs[2] <= errs[0] + 1, 'inner limit exp(r i (B\' - B)), rate C/j')
    Pw = PolynomialRing(QQ, 'w')
    w = Pw.gen()
    Aw, Bw = matrix(Pw, Aq), matrix(Pw, Bq)
    # i (exp(ad A/i) B - B) = [A, B] + w (ad A)^2 B/2 + ..., w = 1/i: exact.
    Bpw = mexp(w * Aw) * Bw * mexp(-w * Aw)
    q = (Bpw - Bw).apply_map(lambda c: c // w)
    check((Bpw - Bw) == w * q, 'B\' - B is divisible by 1/i')
    check(q.apply_map(lambda c: c(0)) == ad(Aq, Bq), 'outer limit: i (B\' - B) -> [A, B]')
    # The second order term on gl_2: g = I + e d [A, B] + (terms of order >= 3).
    P2 = PolynomialRing(QQ, 'e,d')
    e, d = P2.gens()
    A2 = matrix(P2, [[1, 2], [3, 4]])
    B2 = matrix(P2, [[0, 1], [-1, 5]])
    I2 = identity_matrix(P2, 2)

    def tr(M, s):
        return I2 + s * M + (s * M) ** 2 / 2 + (s * M) ** 3 / 6
    g = tr(A2, e) * tr(B2, d) * tr(A2, -e) * tr(B2, -d) - I2
    for row in range(2):
        for col in range(2):
            pol = g[row, col]
            low = sum(c * m for c, m in pol if m.degree() <= 2)
            check(low == e * d * ad(A2, B2)[row, col],
                  'the group commutator is e d [A, B] to the second order')
    # Items 11, 12: symbolic.
    for n in (2, 3):
        names = ['a%d' % i for i in range(n * n)] + ['b%d' % i for i in range(n * n)] + ['c%d' % i for i in range(n * n)]
        P = PolynomialRing(QQ, names)
        gs = P.gens()
        X = matrix(P, n, n, gs[:n * n])
        Y = matrix(P, n, n, gs[n * n:2 * n * n])
        Z = matrix(P, n, n, gs[2 * n * n:])
        check(ad(ad(X, Y), Z) == ad(X, ad(Y, Z)) - ad(Y, ad(X, Z)),
              'item 12: ad [X, Y] = [ad X, ad Y] on Z, the Jacobi identity')
        check(ad(X, ad(Y, Z)) + ad(Y, ad(Z, X)) + ad(Z, ad(X, Y)) == 0, 'Jacobi')
        check(ad(X, Y).trace() == 0, 'item 11: det: gl_n -> gl_1 is tr, tr [X, Y] = 0')
        # item 13: sl_n is an ideal of gl_n, gl_n/sl_n has dimension 1
        check(ad(X, Y).trace() == 0, 'item 13: [gl_n, gl_n] lies in sl_n')
    # det exp(t A) = exp(t tr A), so L(GL_2/SL_2) = gl_2/sl_2 by the trace.
    Rs2 = PowerSeriesRing(QQ, 't', default_prec=12)
    t2 = Rs2.gen()
    for A0 in ([[1, 2], [3, 4]], [[0, 1], [-1, 0]], [[5, -1], [2, 2]]):
        A = matrix(Rs2, A0)
        I = identity_matrix(Rs2, 2)
        E, T = I, I
        for k in range(1, 12):
            T = T * A * t2 / k
            E = E + T
        lhs = (E[0, 0] * E[1, 1] - E[0, 1] * E[1, 0]).add_bigoh(12)
        tr_ = A0[0][0] + A0[1][1]
        rhs = sum((tr_ * t2) ** k / factorial(k) for k in range(12)).add_bigoh(12)
        check(lhs == rhs, 'det exp(t A) = exp(t tr A) mod t^12')
    # The centre of the Heisenberg algebra is an ideal, with quotient R^2.
    for M in (E12, E23, E13):
        check(ad(M, E13) == 0, 'E_13 is central')
    check(E12 * E12 == 0, 'exp(t E_12) = I + t E_12')


def item_14():
    K = QuadraticField(2, 's')
    s = K.gen()
    # (t, t s) in Z^2 only for t = 0: m s = n has only m = n = 0.
    for m in range(1, 200):
        root = ZZ(2 * m ** 2).isqrt()
        for n in (root, root + 1):
            check(m * s != n, 'the line is injective in T^2')
    # Not closed: Pell solutions n^2 - 2 m^2 = +-1 give (m, m s) arbitrarily close
    # to 0 in T^2 with t = m != 0, by |n - m s| = 1/(n + m s) <= 1/(2 m).
    n, m = 1, 1
    for _ in range(15):
        check(abs(n ** 2 - 2 * m ** 2) == 1, 'Pell')
        check((n - m * s) * (n + m * s) == n ** 2 - 2 * m ** 2,
              '(n - m s)(n + m s) = +-1')
        check((n - m * s) ** 2 * (2 * m) ** 2 <= 1, 'hence |n - m s| <= 1/(2 m)')
        n, m = n + 2 * m, n + m


def gamma_op(V, N):
    """Gamma(V) = sum (ad V)^k/(k + 1)! as a function on matrices."""
    def op(M):
        out = M
        T = M
        for k in range(1, 2 * N):
            T = ad(V, T) / (k + 1)
            out = out + T
        return out
    return op


def delta_op(V, N):
    """Delta(V) = Gamma(V)^(-1) = sum (1 - Gamma(V))^j, a finite sum here."""
    G = gamma_op(V, N)

    def op(M):
        out = M
        T = M
        for _ in range(2 * N):
            T = T - G(T)
            out = out + T
        return out
    return op


def item_15():
    Rt = PolynomialRing(QQ, 't')
    t = Rt.gen()
    cases = [
        ([[0, 1, 2, 0], [0, 0, 1, 3], [0, 0, 0, 1], [0, 0, 0, 0]],
         [[0, 2, 0, 1], [0, 0, -1, 1], [0, 0, 0, 2], [0, 0, 0, 0]]),
        ([[0, 1, 0, 0, 2], [0, 0, 3, 0, 0], [0, 0, 0, 1, 1], [0, 0, 0, 0, 2],
          [0, 0, 0, 0, 0]],
         [[0, 0, 1, 1, 0], [0, 0, 1, 2, 0], [0, 0, 0, 0, 3], [0, 0, 0, 0, 1],
          [0, 0, 0, 0, 0]]),
    ]
    for Xl, Zl in cases:
        n = len(Xl)
        X, Z = matrix(Rt, Xl), matrix(Rt, Zl)
        W = mlog(mexp(X) * mexp(t * Z))
        check(mexp(W) == mexp(X) * mexp(t * Z), 'exp(X x t Z) = exp X exp(t Z)')
        Wd = W.apply_map(lambda c: c.derivative())
        check(gamma_op(-W, n)(Wd) == Z, 'Gamma(-W) W\' = Z')
        check(delta_op(-W, n)(Z) == Wd, '(31): W\' = Delta(-W) Z')
        refuted(delta_op(W, n)(Z) == Wd, '(31) without the minus sign')
        V = mlog(mexp(-X) * mexp(t * Z))
        refuted(delta_op(V, n)(Z) == Wd, 'the reading (-X) x t Z in (31)')
        # Gamma(V) = int_0^1 S_(V(s)) ds on a test matrix, exact.
        Vq = matrix(Rt, Xl)
        Y = matrix(Rt, Zl)
        S = mexp(t * Vq) * Y * mexp(-t * Vq)
        I_ = S.apply_map(lambda c: c.integral())
        G1 = I_.apply_map(lambda c: c(1))
        check(G1 == gamma_op(Vq, n)(Y), 'Gamma(X) is the integral of S_(X(t))')
        check(gamma_op(zero_matrix(Rt, n, n), n)(Y) == Y, 'Gamma(0) = I')
        # the derivative of (-X) x (X + t Y) at t = 0 is Gamma(-X) Y
        U = mlog(mexp(-X) * mexp(X + t * Y))
        Ud = U.apply_map(lambda c: c.derivative()(0))
        check(U.apply_map(lambda c: c(0)) == 0, 'the curve starts at 0')
        check(Ud == gamma_op(-Vq, n)(Y).apply_map(lambda c: c(0)),
              'the derivative at t = 0 is Gamma(-X) Y')


def main():
    section_10()
    normal_subgroups_kernel()
    items_9_12()
    item_14()
    item_15()
    print('ok %s: %d checks' % (SCOPE, COUNT[0]))


if __name__ == '__main__':
    main()
