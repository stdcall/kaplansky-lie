"""Exact checks of Chapter I, §§ 7-8 (printed pp. 67-87) of I. Kaplansky,
"Алгебры Ли и локально компактные группы" (Moscow: Mir, 1974).

Run from the project root: sage -python checks/sage/chapter-1d.py
(plain asserts; do not use -O).  The last line is "ok chapter-1d: N checks".
Pages are the printed pages; labels are those of content/01-07-*, 01-08-*.
Conventions of the book: operators act on the right, x y of a Lie algebra is
the bracket, [X Y] = X Y - Y X, a representation S has S(x y) = [S(x), S(y)] with
row vectors, a h = alpha(h) a, (x y, z) = (x, y z).  Everything is computed
over GF(p) (a few places GF(q)) with Python integers or numpy integer arrays reduced
mod p; no floating point.  The axioms of § 8 ask for an algebraically closed field:
the algebras below are split over GF(p), the axioms and all statements checked
are linear conditions that survive extension of scalars.  Expected values are the
book's, as literals; a printed reading that is wrong stays as a refuted check
(`refuted`) beside the corrected one.

section_7 (pp. 67-76).
  th:derivation-power-p, eq:leibniz-power: on the truncated polynomial algebra
  F[x]/(x^p) with D = d/dx, x d/dx, (1 + x) d/dx and on a random non-associative
  graded algebra, p in {2, 3, 5, 7}, all basis pairs; on sl_2 with D = ad; D^2 is not a
  derivation, so "p-th power" matters.  eq:restricted-power: for the matrix algebras
  sl_n (p not dividing n), so_n, sp_n, psl_n (p | n), G_2 in its 7-dimensional
  representation (derivations of the octonions), closure under p-th powers
  and y x^p = y ad(x)^p; the Witt algebra W_1 exhaustively for p = 5, on
  samples for p = 7, 11; the Zassenhaus algebra W(1; 2), p = 5, is centerless and not
  restricted.  p. 69: for (n, p) in {(2,2), (3,3), (4,2), (5,5), (6,2), (6,3), (7,7),
  (8,2), (9,3), (10,2), (10,5)}: Z = center of M, Z in M, N = M/Z simple (MeatAxe of
  GAP, absolutely irreducible adjoint module) except (2, 2), the form Tr(XY) on N
  well defined, invariant, nondegenerate; Block's vanishing for the representations
  tried: the adjoint representation and Sym^a V (x) Sym^a V* (a <= 40 through the
  numeric coefficient, a <= 3 on matrices), nothing beyond these.  p. 70: the
  bordering of Seligman's representations.  th:restricted-via-form,
  th:projective-restricted: the element c of the proof for sl_2, sl_3, sp_4 bordered
  into psl_p, so_5 in psl_5 (p = 5), so_7 and G_2 in psl_7 (p = 7).  The remark of
  p. 71: an explicit non-restricted projective representation of sl_2 with nondegenerate
  form.  th:commutator-identity-irreducible: the matrices A_1, B_1, A_1 B_1, the traces,
  p up to 13, the normal form by the proof on random conjugates, absolute irreducibility;
  the printed hypothesis "совершенным полем" refuted: over F_q the F_q-form
  of F_(q^d)^p is irreducible of dimension d p (F_2 < F_4, F_3 < F_9, F_3 < F_27,
  F_5 < F_25), and A^p is not scalar; with "алгебраически замкнутым" this cannot
  happen.  th:commutator-identity-trace: all pairs (A, B) in M_3(F_3), M_2(F_2)
  (where the trace is 1: p > 2 is needed), direct sums and nonsplit extensions; no
  solutions for n not divisible by p (M_2(F_3)).
  th:nilpotent-representation-trace: the algebras (B_1, I, A_1, ..., A_1^k) in dimension
  p, unitriangular algebras; a in L^2 with a L . L = 0 are computed and f(a, L) = 0;
  nilpotency is needed.  th:nilpotent-projective-form: the same algebras in N: the form
  is degenerate; an abelian example with nondegenerate form.  th:projective-form-cartan,
  th:projective-form-center, th:v-algebra-from-projective: Engel subalgebras of random
  elements of psl_5, sl_3, so_5, sp_4, G_2 (p = 5, 7): every one that is a Cartan
  subalgebra is abelian and ad-semisimple (R^(p^k) = R), a^p = 0 only for a = 0.
  H is closed under the p-th power (tacit in th:v-algebra-from-projective).  The
  hypotheses are needed: the Witt algebra has rank 1, all of GF(p)^* as roots, no nonzero
  invariant form, the form of F[x]/(x^p) is 0; sl_2 (x) F[t]/(t^p) has a nondegenerate
  invariant form, no center, L^2 = L, but a = h (x) t != 0 in H has a^p = 0 and R_a is
  not semisimple, so that form comes from no projective representation.
  th:linear-lie-element: linear spaces of B over sl_3, sl_5 for A = A_1, I + A_1; refuted
  without [A^p L] central, refuted at p = 2 (gl_2).  th:commuting-matrices-power: tori and
  non-split tori; each hypothesis needed.  exc:form-vanishes-trace-zero: all invariant
  forms on gl_n / Z vanish on M/Z for (n, p) = (2,2), (3,3), (4,2), (5,5), (6,2), (6,3),
  not so when p does not divide n.

section_8 (pp. 77-87).
  V-algebras: every simple type up to rank 8 reduced mod p (Sage's Chevalley basis,
  invariant form = Killing form over ZZ divided by the gcd of its values, which
  survives even where the Killing form itself vanishes, as for E_8 at p = 5), for
  p in {5, 7, 11, 13} (p in {5, 7} for E_7, E_8, D_8, B_8, C_8), except A_n with
  p | n + 1; psl_n (p | n) for (5,5), (7,7); gl_n; products; the algebras with isotropic
  roots: exc:four-dim-isotropic, its version with two-dimensional root spaces, the
  algebra on F_p^2 (h_1, h_2, t_1, t_2, e_beta, e_beta e_gamma = omega(beta, gamma)
  e_(beta+gamma)) where all roots are isotropic and proportional roots exist.  On them:
  axioms; th:root-spaces-inclusion, th:negative-root, th:root-element-unique;
  th:nonisotropic-root and the rank 1 subalgebras of its proof; th:no-isotropic-roots with
  its consequence that isotropic roots are orthogonal to all roots; th:orthogonal-roots
  with the corrected L_beta h_alpha = 0; th:five-root-string; th:root-sum-product;
  th:root-string-mod-p (the printed beta = +-alpha refuted); th:cartan-integers-char-p (the
  values mod p: for p = 5, 7 they fill GF(p), the statement is empty there);
  th:root-string-length-char-p; the string products p_i q_i = (i+1)(lambda + i/2) that
  close the argument of p. 86; (m, r, s) of the verbatim argument at p = 5.
  th:rank-one-v-algebra: the Jacobi identity for all rank 1 candidates (form normalised):
  Groebner bases show that no structure exists for root sets in GF(p) with
  one-dimensional root spaces, p in {5, 7, 11, 13}, other than {+-1}, for p = 5 with
  root multiplicities up to 2 (and 3 on {+-1}), and for p = 5, 7 on a nonintegral
  line lambda + GF(p), lambda in GF(p^2).  Arithmetic of steps (b)-(e), (h), (j),
  p < 200.  Theorem 58 and "для всех i": a module where u A^p = 0, lambda not in GF(p), so
  only i < p follows.  th:no-isotropic-roots: step (a), formula (15) on modules; the inner
  products of steps (b), (c), (d) and of the end of the proof as polynomial identities; step
  (d), printed j = 1 - 2 i refuted, j = -1/(2 i) checked, p < 200;
  exc:h-cartan-subalgebra, exc:derived-algebra (all parts on all examples; part (e) as
  printed refuted by the algebra of exc:four-dim-isotropic, with "если Z = 0" checked),
  exc:quotient-by-center, exc:no-center-perfect, exc:infinite-matrices (finite windows),
  exc:matrices-p-divides-n ((5,5), (7,7): the forms on L^2, L/Z are computed),
  exc:four-dim-isotropic: the printed form refuted (4 violations), the corrected form,
  "только один корень" refuted literally (two roots, one up to sign).

What this does NOT establish.  Theorems 74-84, 85-96 are not proved here: only the
listed algebras and characteristics are covered, over GF(p).  The Groebner computations
are exhaustive only within the stated classes.  Infinite-dimensional algebras are
seen only through finite windows.  Block's theorem is sampled, not proved.  The scripts
do not show that the typeset text agrees with the printed book.  Lean files:
DerivationPower (theorem 73, formula (11)), WeylTrace (the steps and traces of theorems 76,
77), VAlgebraSteps (formulas (15), steps (b), (d), the string products of theorems 93-96).
"""
import itertools
import random

import numpy as np
from sage.all import (
    CartanType,
    GF,
    LieAlgebra,
    PolynomialRing,
    QQ,
    ZZ,
    binomial,
    gcd,
    libgap,
    matrix,
    prime_range,
)

MTX_ABS = libgap.eval("MTX.IsAbsolutelyIrreducible")
MTX_IRR = libgap.eval("MTX.IsIrreducible")

SECTIONS = {}
CURRENT = None


def begin(name):
    global CURRENT
    CURRENT = name
    SECTIONS[name] = 0


def check(cond, msg=""):
    assert cond, msg
    SECTIONS[CURRENT] += 1


def refuted(cond, msg=""):
    """A printed reading (or one without a needed hypothesis) that fails."""
    assert not cond, msg
    SECTIONS[CURRENT] += 1


# ---------------------------------------------------------------------------
# Linear algebra mod p on numpy integer arrays
# ---------------------------------------------------------------------------


def rref(M, p):
    M = np.array(M, dtype=np.int64) % p
    if M.ndim != 2 or M.size == 0:
        return M.reshape((0, M.shape[1] if M.ndim == 2 else 0)), []
    rows, cols = M.shape
    piv = []
    r = 0
    for c in range(cols):
        if r >= rows:
            break
        nz = np.nonzero(M[r:, c])[0]
        if nz.size == 0:
            continue
        k = r + int(nz[0])
        if k != r:
            M[[r, k]] = M[[k, r]]
        M[r] = (M[r] * pow(int(M[r, c]), -1, p)) % p
        idx = np.nonzero(M[:, c])[0]
        idx = idx[idx != r]
        if idx.size:
            M[idx] = (M[idx] - np.outer(M[idx, c], M[r])) % p
        piv.append(c)
        r += 1
    return M[:r], piv


def rank(M, p):
    return len(rref(M, p)[1])


def nullspace(M, p, cols=None):
    """Vectors v with M v = 0, as rows."""
    M = np.array(M, dtype=np.int64)
    if M.size == 0:
        return np.eye(cols, dtype=np.int64)
    R, piv = rref(M, p)
    n = M.shape[1]
    free = [c for c in range(n) if c not in piv]
    out = np.zeros((len(free), n), dtype=np.int64)
    for i, f in enumerate(free):
        out[i, f] = 1
        for r, c in enumerate(piv):
            out[i, c] = (-R[r, f]) % p
    return out


def solve(M, b, p):
    """x with M x = b, or None."""
    M = np.array(M, dtype=np.int64)
    A = np.concatenate([M, np.array(b, dtype=np.int64).reshape((-1, 1))], axis=1)
    R, piv = rref(A, p)
    n = M.shape[1]
    if n in piv:
        return None
    x = np.zeros(n, dtype=np.int64)
    for r, c in enumerate(piv):
        x[c] = R[r, n]
    return x


def matpow(M, e, p):
    R = np.eye(M.shape[0], dtype=np.int64)
    B = M % p
    while e:
        if e & 1:
            R = R @ B % p
        B = B @ B % p
        e >>= 1
    return R


def trace(M, p):
    return int(np.trace(M)) % p


def is_semisimple(R, p, limit=5000):
    """R^(p^k) = R for some k: then x^(p^k) - x, squarefree, annihilates R, so R is
    diagonalizable over the algebraic closure; the sequence is eventually periodic
    and R lies on the cycle iff R is semisimple."""
    seen = set()
    cur = R % p
    start = cur.tobytes()
    for _ in range(limit):
        cur = matpow(cur, p, p)
        b = cur.tobytes()
        if b == start:
            return True
        if b in seen:
            return False
        seen.add(b)
    raise AssertionError("cycle too long")


# ---------------------------------------------------------------------------
# Algebras by structure constants
# ---------------------------------------------------------------------------


class Alg:
    """e_i e_j = sum C[i, j, k] e_k over GF(p)."""

    def __init__(self, C, p):
        self.C = np.array(C, dtype=np.int64) % p
        self.p = p
        self.n = self.C.shape[0]

    def prod(self, u, v):
        return np.einsum("i,j,ijk->k", u, v, self.C) % self.p

    def R(self, v):
        """The matrix of R_v on row vectors: e_i R_v = row i."""
        return np.einsum("j,ijk->ik", v, self.C) % self.p

    def basis(self, i):
        e = np.zeros(self.n, dtype=np.int64)
        e[i] = 1
        return e

    def jacobi(self):
        p, C, n = self.p, self.C, self.n
        anti =((C + np.transpose(C, (1, 0, 2))) % p == 0).all()
        diag = all((C[i, i] % p == 0).all() for i in range(n))
        # (e_i e_j) e_k + cyclic
        T = np.einsum("ijl,lkm->ijkm", C, C) % p
        J = (T + np.transpose(T, (1, 2, 0, 3)) + np.transpose(T, (2, 0, 1, 3))) % p
        return anti and diag and not J.any()

    def center(self):
        """Basis (rows) of {z : z e_j = 0 for all j}."""
        n = self.n
        M = np.transpose(self.C, (1, 2, 0)).reshape((n * n, n))
        return nullspace(M, self.p)

    def derived(self):
        """A basis (rows) of the span of all products."""
        n = self.n
        return rref(self.C.reshape((n * n, n)), self.p)[0]

    def is_perfect(self):
        return self.derived().shape[0] == self.n

    def inner_power(self, x):
        """y with R_y = R_x^p, or None; unique when the center is 0."""
        n, p = self.n, self.p
        target = matpow(self.R(x), p, p).reshape(n * n)
        # columns: the matrices R_(e_j) flattened
        A = np.transpose(self.C, (0, 2, 1)).reshape((n * n, n))
        return solve(A, target, p)

    def invariant_forms(self):
        """A basis of the invariant symmetric bilinear forms: f(x y, z) = f(x, y z),
        as an array (count, n, n)."""
        n, p = self.n, self.p
        pairs = [(i, j) for i in range(n) for j in range(i, n)]
        idx = {}
        for t, (i, j) in enumerate(pairs):
            idx[(i, j)] = t
            idx[(j, i)] = t
        rows = {}
        pivots = {}
        # sparse elimination
        def reduce(row):
            while row:
                t = min(row)
                if t not in pivots:
                    return row
                f = row[t]
                pr = pivots[t]
                for k, v in pr.items():
                    nv = (row.get(k, 0) - f * v) % p
                    if nv:
                        row[k] = nv
                    else:
                        row.pop(k, None)
            return row

        nz = [[list(zip(*np.nonzero(self.C[i, j]))) for j in range(n)] for i in range(n)]
        for x in range(n):
            for y in range(n):
                for z in range(n):
                    row = {}
                    for (k,) in nz[x][y]:
                        t = idx[(k, z)]
                        row[t] = (row.get(t, 0) + int(self.C[x, y, k])) % p
                    for (k,) in nz[y][z]:
                        t = idx[(x, k)]
                        row[t] = (row.get(t, 0) - int(self.C[y, z, k])) % p
                    row = {k: v for k, v in row.items() if v}
                    row = reduce(row)
                    if row:
                        t = min(row)
                        inv = pow(row[t], -1, p)
                        pivots[t] = {k: v * inv % p for k, v in row.items()}
        free = [t for t in range(len(pairs)) if t not in pivots]
        forms = []
        for f in free:
            sol = {f: 1}
            for t in sorted(pivots, reverse=True):
                s = 0
                for k, v in pivots[t].items():
                    if k != t and k in sol:
                        s += v * sol[k]
                if s % p:
                    sol[t] = (-s) % p
            G = np.zeros((n, n), dtype=np.int64)
            for t, v in sol.items():
                i, j = pairs[t]
                G[i, j] = v
                G[j, i] = v
            forms.append(G)
        return forms


def alg_from_mats(mats, p):
    """The Lie algebra x y = [X, Y] on a basis of a space of matrices closed under
    the commutator; asserts closure."""
    n = len(mats)
    k = mats[0].shape[0]
    A = np.array([m.reshape(k * k) for m in mats], dtype=np.int64).T  # columns are the basis
    C = np.zeros((n, n, n), dtype=np.int64)
    for i in range(n):
        for j in range(i):
            br = (mats[i] @ mats[j] - mats[j] @ mats[i]) % p
            x = solve(A, br.reshape(k * k), p)
            assert x is not None, "not closed under the commutator"
            C[i, j] = x
            C[j, i] = (-x) % p
    return Alg(C, p)


def quotient(alg, S, drop):
    """L / span(S), S a list of vectors spanning an ideal; basis: the old basis vectors
    except the indices in `drop`, which must form a complement.  Returns (Alg, kept)."""
    n, p = alg.n, alg.p
    kept = [i for i in range(n) if i not in drop]
    rows = [list(s) for s in S] + [list(alg.basis(i)) for i in kept]
    Q = np.array(rows, dtype=np.int64) % p  # the new basis: S, then kept
    assert rank(Q, p) == n
    # coordinates of old basis vectors in the new basis
    A = np.concatenate([Q, np.eye(n, dtype=np.int64)], axis=1)
    R, piv = rref(A, p)
    Qinv = R[:, n:]  # e_i = sum Qinv[i, j] new_j
    m = len(kept)
    s = len(S)
    C = np.zeros((m, m, m), dtype=np.int64)
    for a, i in enumerate(kept):
        for b, j in enumerate(kept):
            v = alg.C[i, j]
            co = (v @ Qinv) % p
            C[a, b] = co[s:]
    return Alg(C, p), kept


# ---------------------------------------------------------------------------
# Matrix algebras
# ---------------------------------------------------------------------------


def E(n, i, j):
    m = np.zeros((n, n), dtype=np.int64)
    m[i, j] = 1
    return m


def gl_basis(n):
    return [E(n, i, j) for i in range(n) for j in range(n)]


def sl_basis(n):
    out = [E(n, i, j) for i in range(n) for j in range(n) if i != j]
    out += [E(n, i, i) - E(n, i + 1, i + 1) for i in range(n - 1)]
    return out


def sub_basis_by_condition(n, cond_mats, p):
    """Matrices X with J-condition given as a list of functions flattened: use the linear
    system built by `cond(X)` on the basis of all matrices."""
    basis = gl_basis(n)
    A = np.array([cond_mats(b).reshape(-1) for b in basis], dtype=np.int64).T
    ns = nullspace(A, p)
    return [v.reshape((n, n)) for v in ns]


def so_basis(n, p):
    J = np.zeros((n, n), dtype=np.int64)
    for i in range(n):
        J[i, n - 1 - i] = 1
    return sub_basis_by_condition(n, lambda X: (X.T @ J + J @ X) % p, p)


def sp_basis(n, p):
    J = np.zeros((n, n), dtype=np.int64)
    m = n // 2
    for i in range(m):
        J[i, n - 1 - i] = 1
        J[n - 1 - i, i] = -1
    return sub_basis_by_condition(n, lambda X: (X.T @ J + J @ X) % p, p)


def octonion_table(p):
    """e_i e_j = sign e_k on the basis 0..7 of the Cayley-Dickson algebra over GF(p)."""
    def conj(x):
        return [x[0]] + [(-c) % p for c in x[1:]]

    def mult(x, y):
        n = len(x)
        if n == 1:
            return [x[0] * y[0] % p]
        h = n // 2
        a, b = x[:h], x[h:]
        c, d = y[:h], y[h:]
        # (a, b)(c, d) = (a c - conj(d) b, d a + b conj(c))
        ac = mult(a, c)
        db = mult(conj(d), b)
        da = mult(d, a)
        bc = mult(b, conj(c))
        return [(u - v) % p for u, v in zip(ac, db)] + [(u + v) % p for u, v in zip(da, bc)]

    table = {}
    for i in range(8):
        for j in range(8):
            ei = [1 if k == i else 0 for k in range(8)]
            ej = [1 if k == j else 0 for k in range(8)]
            table[(i, j)] = mult(ei, ej)
    return table


def g2_basis(p):
    """The derivations of the octonions on the 7 imaginary units, row convention, as 7 x 7
    matrices; dimension 14 for p > 3."""
    t = octonion_table(p)
    # D: e_i -> sum D_ij e_j (i, j = 1..7), D e_0 = 0; unknowns D_ij.
    idx = lambda i, j: (i - 1) * 7 + (j - 1)
    rows = []
    for a in range(1, 8):
        for b in range(1, 8):
            prod = t[(a, b)]
            # D(e_a e_b) - (D e_a) e_b - e_a (D e_b) = 0 in each coordinate c = 0..7
            for c in range(8):
                row = [0] * 49
                for k in range(1, 8):
                    if prod[k]:
                        if c >= 1:
                            row[idx(k, c)] = (row[idx(k, c)] + prod[k]) % p
                for j in range(1, 8):
                    co = t[(j, b)][c]
                    if co:
                        row[idx(a, j)] = (row[idx(a, j)] - co) % p
                    co = t[(a, j)][c]
                    if co:
                        row[idx(b, j)] = (row[idx(b, j)] - co) % p
                rows.append(row)
    ns = nullspace(np.array(rows, dtype=np.int64), p)
    return [v.reshape((7, 7)) for v in ns]


def border(m, size):
    out = np.zeros((size, size), dtype=np.int64)
    k = m.shape[0]
    out[:k, :k] = m
    return out


def A1(p):
    A = np.zeros((p, p), dtype=np.int64)
    for i in range(p - 1):
        A[i, i + 1] = 1
    return A


def B1(p):
    B = np.zeros((p, p), dtype=np.int64)
    for i in range(1, p):
        B[i, i - 1] = i
    return B


def in_span(mats, X, p):
    k = X.shape[0]
    A = np.array([m.reshape(k * k) for m in mats], dtype=np.int64).T
    return solve(A, X.reshape(k * k) % p, p) is not None


def trace_form_gram(mats, p):
    return np.array([[trace(a @ b, p) for b in mats] for a in mats], dtype=np.int64) % p


# ---------------------------------------------------------------------------
# Section 7
# ---------------------------------------------------------------------------


def section_7_derivations():
    rng = random.Random(1)
    for p in (2, 3, 5, 7):
        # F[x]/(x^p), derivations d/dx, x d/dx, (1 + x) d/dx
        def mul(u, v):
            out = [0] * p
            for i, a in enumerate(u):
                for j, b in enumerate(v):
                    if a and b and i + j < p:
                        out[i + j] = (out[i + j] + a * b) % p
            return out

        def der(f):
            def D(u):
                du = [(i * u[i]) % p if i else 0 for i in range(p)]
                du = du[1:] + [0]
                return mul(f, du)
            return D

        fs = {"d/dx": [1] + [0] * (p - 1)}
        if p >= 2:
            fs["x d/dx"] = [0, 1] + [0] * (p - 2)
            fs["(1+x) d/dx"] = [1, 1] + [0] * (p - 2)
        for name, f in fs.items():
            D = der(f)

            def power(u, n):
                for _ in range(n):
                    u = D(u)
                return u

            for i in range(p):
                for j in range(p):
                    x = [1 if k == i else 0 for k in range(p)]
                    y = [1 if k == j else 0 for k in range(p)]
                    # D is a derivation of the truncated algebra
                    lhs = D(mul(x, y))
                    rhs = [(a + b) % p for a, b in zip(mul(D(x), y), mul(x, D(y)))]
                    check(lhs == rhs, "derivation %s" % name)
                    # formula (11)
                    left = power(mul(x, y), p)
                    right = [0] * p
                    for t in range(p + 1):
                        c = int(binomial(p, t)) % p
                        term = mul(power(x, p - t), power(y, t))
                        right = [(a + c * b) % p for a, b in zip(right, term)]
                    check(left == right, "(11)")
                    # the conclusion: D^p is a derivation
                    check(left == [(a + b) % p for a, b in zip(mul(power(x, p), y), mul(x, power(y, p)))],
                          "th:derivation-power-p")
        # D^2 is not a derivation for p > 2 (x d/dx: D^2 (x x) = 4 x^2 against 2 x^2)
        if p > 2:
            D = der([0, 1] + [0] * (p - 2))
            x = [0, 1] + [0] * (p - 2)
            xx = mul(x, x)
            lhs = D(D(xx))
            rhs = [(a + b) % p for a, b in zip(mul(D(D(x)), x), mul(x, D(D(x))))]
            refuted(lhs == rhs, "D^2 is not a derivation")
        # a random non-associative algebra graded by Z/p, D e_i = i e_i
        c = [[rng.randrange(p) for _ in range(p)] for _ in range(p)]

        def nmul(u, v):
            out = [0] * p
            for i in range(p):
                for j in range(p):
                    out[(i + j) % p] = (out[(i + j) % p] + c[i][j] * u[i] * v[j]) % p
            return out

        def D(u):
            return [(i * u[i]) % p for i in range(p)]

        def Dn(u, n):
            for _ in range(n):
                u = D(u)
            return u

        for _ in range(20):
            x = [rng.randrange(p) for _ in range(p)]
            y = [rng.randrange(p) for _ in range(p)]
            left = Dn(nmul(x, y), p)
            right = [0] * p
            for t in range(p + 1):
                cc = int(binomial(p, t)) % p
                term = nmul(Dn(x, p - t), Dn(y, t))
                right = [(a + cc * b) % p for a, b in zip(right, term)]
            check(left == right, "(11) in a non-associative algebra")
    # sl_2, D = R_x
    for p in (3, 5, 7):
        L = alg_from_mats(sl_basis(2), p)
        for x in range(3):
            Rx = L.R(L.basis(x))
            D = matpow(Rx, p, p)
            for i in range(3):
                for j in range(3):
                    ei, ej = L.basis(i), L.basis(j)
                    left = L.prod(ei, ej) @ D % p
                    right = (L.prod(ei @ D % p, ej) + L.prod(ei, ej @ D % p)) % p
                    check((left == right).all(), "R_x^p is a derivation of sl_2")


def restricted_on_matrices(mats, p, trials, rng, name):
    """Closure under p-th powers, and y x^p = y ad(x)^p."""
    k = mats[0].shape[0]
    for _ in range(trials):
        cs = [rng.randrange(p) for _ in mats]
        X = sum(c * m for c, m in zip(cs, mats)) % p
        Xp = matpow(X, p, p)
        check(in_span(mats, Xp, p), "x^p in the algebra, %s" % name)
        for Y in mats:
            v = Y
            for _ in range(p):
                v = (v @ X - X @ v) % p
            check(((Y @ Xp - Xp @ Y) % p == v).all(), "(12), %s" % name)


def psl(n, p):
    """(M, N): M = sl_n with basis E_ij, d_i, N = M/Z dropping the last d_i.  p | n."""
    mats = sl_basis(n)
    M = alg_from_mats(mats, p)
    k = n * n
    A = np.array([m.reshape(k) for m in mats], dtype=np.int64).T
    co = solve(A, np.eye(n, dtype=np.int64).reshape(k), p)
    assert co is not None
    # the coefficient of the last d_i in I is n - 1, nonzero mod p
    last = M.n - 1
    assert co[last] % p
    N, kept = quotient(M, [co], [last])
    return M, N, mats, co, kept


def witt(p):
    """W_1: basis e_i, i = -1..p-2, e_i e_j = (j - i) e_(i+j)."""
    n = p
    C = np.zeros((n, n, n), dtype=np.int64)
    for a in range(n):
        for b in range(n):
            i, j = a - 1, b - 1
            if -1 <= i + j <= p - 2:
                C[a, b, i + j + 1] = (j - i) % p
    return Alg(C, p)


def zassenhaus(p):
    """W(1; 2): basis e_i, i = -1..p^2 - 2, in divided powers."""
    n = p * p
    C = np.zeros((n, n, n), dtype=np.int64)
    for a in range(n):
        for b in range(n):
            i, j = a - 1, b - 1
            if -1 <= i + j <= n - 2:
                u = int(binomial(i + j + 1, j)) if j >= 0 and i + j + 1 >= 0 else 0
                v = int(binomial(i + j + 1, i)) if i >= 0 and i + j + 1 >= 0 else 0
                C[a, b, i + j + 1] = (u - v) % p
    return Alg(C, p)


def witt_rep(p):
    """S(e_i) on F[x]/(x^p): minus the row matrix of x^(i+1) d/dx."""
    mats = []
    for i in range(-1, p - 1):
        M = np.zeros((p, p), dtype=np.int64)
        for k in range(p):
            t = k + i
            if 0 <= t < p:
                M[k, t] = (-k) % p
        mats.append(M)
    return mats


def section_7_restricted():
    rng = random.Random(2)
    for p, ns in ((3, (2, 4)), (5, (2, 3, 4)), (7, (2, 3))):
        for n in ns:
            restricted_on_matrices(sl_basis(n), p, 4, rng, "sl_%d mod %d" % (n, p))
    for p in (3, 5, 7):
        for n in (3, 4, 5):
            restricted_on_matrices(so_basis(n, p), p, 3, rng, "so_%d mod %d" % (n, p))
        restricted_on_matrices(sp_basis(4, p), p, 3, rng, "sp_4 mod %d" % p)
    for p in (5, 7):
        G = g2_basis(p)
        check(len(G) == 14, "G_2 has dimension 14")
        L = alg_from_mats(G, p)
        check(L.jacobi() and L.center().shape[0] == 0 and L.is_perfect(), "G_2 simple-looking")
        check(rank(trace_form_gram(G, p), p) == 14, "the 7-dimensional trace form is nondegenerate")
        restricted_on_matrices(G, p, 3, rng, "G_2 mod %d" % p)
    # the Witt algebra: restricted and centerless; p-th power of every element for p = 5
    for p in (5, 7, 11):
        W = witt(p)
        check(W.jacobi(), "W_1 is a Lie algebra")
        check(W.center().shape[0] == 0 and W.is_perfect(), "W_1: no center, W^2 = W")
        if p == 5:
            for cs in itertools.product(range(p), repeat=p):
                x = np.array(cs, dtype=np.int64)
                assert W.inner_power(x) is not None
            check(True, "W_1, p = 5: R_x^p inner for all 3125 elements")
        else:
            for _ in range(60):
                x = np.array([rng.randrange(p) for _ in range(p)], dtype=np.int64)
                check(W.inner_power(x) is not None, "W_1 restricted")
    # W(1; 2): centerless, not restricted
    p = 5
    Z2 = zassenhaus(p)
    check(Z2.jacobi(), "W(1; 2) is a Lie algebra")
    check(Z2.center().shape[0] == 0 and Z2.is_perfect())
    refuted(Z2.inner_power(Z2.basis(0)) is not None, "R^p of e_(-1) is not inner in W(1; 2)")


def section_7_p69():
    # M, Z, N = M/Z (p. 69)
    def simple_by_meataxe(N):
        p = N.p
        # the adjoint representation; all basis elements
        F = GF(p)
        mats = [matrix(F, N.n, N.n, [int(c) for c in N.R(N.basis(i)).reshape(-1)]) for i in range(N.n)]
        # a generating subset to keep it short: all R_x with x in a basis
        gens = [m for m in mats if not m.is_zero()]
        if not gens:
            return False
        G = libgap.GModuleByMats([libgap(m) for m in gens[:12] + gens[-6:]], libgap.GF(p))
        G2 = libgap.GModuleByMats([libgap(m) for m in gens], libgap.GF(p))
        return bool(MTX_ABS(G2))

    for n, p in ((2, 2), (3, 3), (4, 2), (5, 5), (6, 2), (6, 3), (7, 7), (8, 2), (9, 3), (10, 2), (10, 5)):
        M, N, mats, co, kept = psl(n, p)
        I = np.eye(n, dtype=np.int64)
        check(trace(I, p) == 0, "Z in M since p | n")
        # center of M is exactly the scalars
        check(M.center().shape[0] == 1, "center of M one-dimensional, (%d, %d)" % (n, p))
        check(((M.center()[0] * co[np.nonzero(co)[0][0]] - co * M.center()[0][np.nonzero(co)[0][0]]) % p == 0).all())
        if (n, p) == (2, 2):
            check(not N.C.any(), "N is abelian of dimension 2: the only exception")
            refuted(simple_by_meataxe(N), "N is not simple for n = p = 2")
        else:
            check(simple_by_meataxe(N), "N simple, (%d, %d)" % (n, p))
            check(N.center().shape[0] == 0, "N has no center")
        # the form f(X*, Y*) = Tr(X Y): radical of Tr(XY) on M is Z
        G = trace_form_gram(mats, p)
        check(rank(G, p) == len(mats) - 1, "radical of the form on M is one-dimensional")
        check(not ((co @ G) % p).any(), "Tr(C Y) = 0: the form is well defined")
        # invariance on M, hence on N
        if len(mats) <= 35:
            for i, j in itertools.product(range(len(mats)), repeat=2):
                br = (mats[i] @ mats[j] - mats[j] @ mats[i]) % p
                for k in range(len(mats)):
                    br2 = (mats[j] @ mats[k] - mats[k] @ mats[j]) % p
                    assert trace(br @ mats[k], p) == trace(mats[i] @ br2, p)
            check(True, "invariance on M")
    # The remark of p. 69: on gl_n / Z the form Tr(XY) is not well defined, Tr(C Y) != 0 for a scalar C
    for n, p in ((3, 3), (5, 5)):
        refuted(trace(np.eye(n, dtype=np.int64) @ E(n, 0, 0), p) == 0, "traces 0 are essential")
    # Block's vanishing, on the representations tried.  Adjoint representation of N:
    for n, p in ((3, 3), (5, 5), (4, 2), (6, 2), (6, 3)):
        M, N, mats, co, kept = psl(n, p)
        K = np.array([[trace(N.R(N.basis(i)) @ N.R(N.basis(j)), p) for j in range(N.n)] for i in range(N.n)], dtype=np.int64)
        check(not K.any(), "the Killing form of N is 0, (%d, %d)" % (n, p))
    # Sym^a V (x) Sym^a V*: the form is 2 dim(Sym^a) binom(n + a, n + 1) Tr(XY)
    for n, p in ((3, 3), (5, 5), (6, 3), (10, 5), (7, 7)):
        for a in range(1, 41):
            check(2 * binomial(n + a - 1, a) * binomial(n + a, n + 1) % p == 0, "Sym^%d, (%d, %d)" % (a, n, p))
    # ... the coefficient on matrices, n = 3, p = 3, a <= 3; the representation Sym^a is built on
    # monomials, X acts by the derivation rule.
    def sym_rep(X, a, p):
        n = X.shape[0]
        mons = [m for m in itertools.product(range(a + 1), repeat=n) if sum(m) == a]
        idx = {m: i for i, m in enumerate(mons)}
        out = np.zeros((len(mons), len(mons)), dtype=np.int64)
        for m in mons:
            for i in range(n):
                if m[i]:
                    for j in range(n):
                        if X[i, j]:
                            t = list(m)
                            t[i] -= 1
                            t[j] += 1
                            out[idx[m], idx[tuple(t)]] += m[i] * int(X[i, j])
        return out % p

    n, p = 3, 3
    base = sl_basis(n)
    for a in (1, 2, 3):
        rho = [sym_rep(b, a, p) for b in base]
        # it is a representation
        for i, j in itertools.product(range(len(base)), repeat=2):
            br = (base[i] @ base[j] - base[j] @ base[i]) % p
            check(((rho[i] @ rho[j] - rho[j] @ rho[i]) % p == sym_rep(br, a, p)).all())
        dim = rho[0].shape[0]
        for i, j in itertools.product(range(len(base)), repeat=2):
            t = trace(rho[i] @ rho[j], p)
            check((2 * dim * t) % p == 0, "the form of Sym^a (x) Sym^a* vanishes on M")
    # Seligman's algebras (p. 70): bordering with zeros keeps the form and lands in M.
    for p in (3, 5, 7):
        base = sl_basis(2)
        size = p if p > 2 else 2
        B = [border(m, size) for m in base]
        for m, b in zip(base, B):
            check(trace(b, p) == 0, "L^2 = L makes the traces 0")
        G0 = trace_form_gram(base, p)
        G1 = trace_form_gram(B, p)
        check((G0 == G1).all(), "the same invariant form")
        # no nonzero element of L becomes scalar
        I = np.eye(size, dtype=np.int64).reshape(size * size)
        A = np.array([b.reshape(size * size) for b in B] + [I], dtype=np.int64)
        check(rank(A, p) == len(B) + 1, "the projective representation is faithful")


def check_theorem_74(mats, p, trials, rng, name):
    """The element c of the proof of th:restricted-via-form in N = M/Z: mats are
    matrices of size divisible by p, closed under the commutator, the form is Tr."""
    k = mats[0].shape[0]
    check(k % p == 0, "the size is divisible by p")
    check(all(trace(m, p) == 0 for m in mats), "in M")
    G = trace_form_gram(mats, p)
    check(rank(G, p) == len(mats), "the form is nondegenerate on A: %s" % name)
    A = np.array([m.reshape(k * k) for m in mats], dtype=np.int64)
    I = np.eye(k, dtype=np.int64).reshape(k * k)
    check(rank(np.concatenate([A, I.reshape(1, -1)]), p) == len(mats) + 1, "A meets Z in 0")
    L = alg_from_mats(mats, p)
    check(L.center().shape[0] == 0, "A has no center: %s" % name)
    for _ in range(trials):
        cs = np.array([rng.randrange(p) for _ in mats], dtype=np.int64)
        X = sum(int(c) * m for c, m in zip(cs, mats)) % p
        Xp = matpow(X, p, p)
        # a -> (a, x^p) = Tr(a X^p) is generated by c in A
        rhs = np.array([trace(m @ Xp, p) for m in mats], dtype=np.int64)
        c = solve(G, rhs, p)
        check(c is not None, "c exists")
        C = sum(int(ci) * m for ci, m in zip(c, mats)) % p
        for Y in mats:
            lhs = (Y @ C - C @ Y) % p
            v = Y
            for _ in range(p):
                v = (v @ X - X @ v) % p
            check((lhs == v).all(), "R_c = R_x^p on A: %s" % name)
    return L


def section_7_theorem_74():
    rng = random.Random(3)
    for p in (5, 7):
        check_theorem_74([border(m, p) for m in sl_basis(2)], p, 5, rng, "sl_2")
        check_theorem_74([border(m, p) for m in sl_basis(3)], p, 3, rng, "sl_3")
        check_theorem_74([border(m, p) for m in sp_basis(4, p)], p, 3, rng, "sp_4")
    check_theorem_74(so_basis(5, 5), 5, 3, rng, "so_5")
    check_theorem_74(so_basis(7, 7), 7, 2, rng, "so_7")
    check_theorem_74(g2_basis(7), 7, 3, rng, "G_2")

    # The remark of p. 71.  sl_2 on V_2 + Z_c1 + Z_c2 + zeros: a -> A, x -> X, h -> H,
    # with Z_c the module of dimension p where v_(p-1) A = c v_0.
    for p in (5, 7):
        lam = 3 % p  # a weight in GF(p)
        def module(r, l, c=0):
            A = np.zeros((r, r), dtype=np.int64)
            X = np.zeros((r, r), dtype=np.int64)
            H = np.zeros((r, r), dtype=np.int64)
            for i in range(r):
                H[i, i] = (l + i) % p
                if i + 1 < r:
                    A[i, i + 1] = 1
                if i >= 1:
                    X[i, i - 1] = (i * l + i * (i - 1) // 2) % p
            A[r - 1, 0] = c
            return A, X, H

        half = pow(2, -1, p)
        V2 = module(2, (-half) % p)
        Z1 = module(p, lam, 1)
        Z2 = module(p, lam, 2)
        for T in (V2, Z1, Z2):
            A, X, H = T
            check(((A @ H - H @ A) % p == A).all())
            check(((X @ H - H @ X) % p == (-X) % p).all())
            check(((A @ X - X @ A) % p == H).all(), "a representation of sl_2")
        check((matpow(Z1[0], p, p) == np.eye(p, dtype=np.int64)).all(), "A^p = c I on Z_c")
        check((matpow(Z2[0], p, p) == 2 * np.eye(p, dtype=np.int64) % p).all())
        size = 3 * p

        def assemble(i):
            M = np.zeros((size, size), dtype=np.int64)
            pos = 0
            for T in (V2, Z1, Z2):
                r = T[i].shape[0]
                M[pos:pos + r, pos:pos + r] = T[i]
                pos += r
            return M

        S = [assemble(0), assemble(1), assemble(2)]
        Sa, Sx, Sh = S
        G = trace_form_gram(S, p)
        check(rank(G, p) == 3, "the form is nondegenerate on L")
        # the traces on Z_c vanish (p > 3), the form is that of V_2
        check((G == trace_form_gram(list(V2), p)).all())
        # S(a)^p is not scalar, while a^[p] = 0 in L: the projective representation is not restricted
        Pw = matpow(Sa, p, p)
        check(((Pw - Pw[0, 0] * np.eye(size, dtype=np.int64)) % p).any(), "S(a)^p is not scalar")
        L = alg_from_mats(S, p)
        check(L.center().shape[0] == 0)
        check(not L.inner_power(L.basis(0)).any(), "a^[p] = 0 in L")
        # c of the proof is a^[p] = 0, though S(a)^p != S(0) in N
        rhs = np.array([trace(m @ Pw, p) for m in S], dtype=np.int64)
        check(not solve(G, rhs, p).any(), "c = 0")


def section_7_theorem_76():
    rng = random.Random(4)
    for p in (2, 3, 5, 7, 11, 13):
        A, B = A1(p), B1(p)
        I = np.eye(p, dtype=np.int64)
        check(((A @ B - B @ A) % p == I).all(), "[A_1, B_1] = I")
        AB = np.diag([i for i in range(1, p)] + [0])
        check(((A @ B) == AB).all(), "the printed A_1 B_1")
        check(trace(A, p) == 0 and trace(B, p) == 0)
        check(sum(range(1, p)) == p * (p - 1) // 2, "1 + 2 + ... + p - 1")
        if p == 2:
            check(trace(A @ B, p) == 1, "Tr(A_1 B_1) = 1 for p = 2: p > 2 is needed")
        else:
            check(trace(A @ B, p) == 0, "Tr(A_1 B_1) = 0 for p > 2")
        # Tr(AB) = p lambda mu + lambda Tr B_1 + mu Tr A_1 + Tr(A_1 B_1)
        for lam, mu in itertools.product(range(p), repeat=2):
            T = (lam * I + A) @ (mu * I + B) % p
            check(trace(T, p) == trace(A @ B, p), "the printed expansion")
        # absolutely irreducible
        F = GF(p)
        gm = libgap.GModuleByMats(
            [libgap(matrix(F, p, p, [int(c) for c in A.reshape(-1)])), libgap(matrix(F, p, p, [int(c) for c in B.reshape(-1)]))],
            libgap.GF(p),
        )
        check(bool(MTX_ABS(gm)), "V irreducible")
        # the proof on a random conjugate over GF(p): the normal form is recovered
        for _ in range(4):
            while True:
                g = np.array([[rng.randrange(p) for _ in range(p)] for _ in range(p)], dtype=np.int64)
                if rank(g, p) == p:
                    break
            ginv = rref(np.concatenate([g, I], axis=1), p)[0][:, p:]
            lam, mu = rng.randrange(p), rng.randrange(p)
            Aq = g @ (lam * I + A) @ ginv % p
            Bq = g @ (mu * I + B) @ ginv % p
            check(((Aq @ Bq - Bq @ Aq) % p == I).all())
            Ap = matpow(Aq, p, p)
            Bp = matpow(Bq, p, p)
            check((Ap == lam**p * I % p).all() and (Bp == mu**p * I % p).all(), "A^p, B^p scalar")
            A0 = (Aq - lam * I) % p
            B0 = (Bq - mu * I) % p
            x = nullspace(B0.T, p)
            check(x.shape[0] == 1, "the vector x with x B = 0 is unique up to a scalar")
            x = x[0]
            rows = [x]
            for _ in range(p - 1):
                rows.append(rows[-1] @ A0 % p)
            Q = np.array(rows, dtype=np.int64) % p
            check(rank(Q, p) == p, "x, x A, ..., x A^(p-1) are independent")
            Qinv = rref(np.concatenate([Q, I], axis=1), p)[0][:, p:]
            check((Q @ A0 @ Qinv % p == A).all() and (Q @ B0 @ Qinv % p == B).all(), "the printed matrices")

    # The printed hypothesis "совершенным полем" fails.  Over F = GF(q0), with K = GF(q0^d),
    # V = K^p as a space over F, A = t^(1/p) + A_1 (A_1 over the prime field), B = B_1.
    for q0, d in ((2, 2), (3, 2), (3, 3), (5, 2)):
        p = q0
        K = GF(p**d, "z")
        t = K.multiplicative_generator()
        F = GF(p)
        # multiplication by t on K over F, row convention, basis 1, z, ..., z^(d-1)
        z = K.gen()
        basis = [z**i for i in range(d)]
        Mt = np.array([[int(c) for c in (b * t).polynomial().padded_list(d)] for b in basis], dtype=np.int64)
        Id = np.eye(d, dtype=np.int64)
        Ip = np.eye(p, dtype=np.int64)
        A = (np.kron(Mt, Ip) + np.kron(Id, A1(p))) % p
        B = np.kron(Id, B1(p)) % p
        n = d * p
        In = np.eye(n, dtype=np.int64)
        check(((A @ B - B @ A) % p == In).all(), "[A, B] = I over F_%d, dim %d" % (p, n))

        def to_gap(M):
            return libgap(matrix(F, n, n, [int(c) for c in M.reshape(-1)]))

        gm = libgap.GModuleByMats([to_gap(A), to_gap(B)], libgap.GF(p))
        check(bool(MTX_IRR(gm)), "V is irreducible over the perfect field")
        refuted(n == p, "printed: dim V = p over a perfect field")
        # A^p is not scalar, the step 'по лемме Шура, скалярно' fails
        Apow = matpow(A, p, p)
        refuted(((Apow - Apow[0, 0] * In) % p == 0).all(), "A^p is not scalar")
        check(((Apow @ B - B @ Apow) % p == 0).all() and ((Apow @ A - A @ Apow) % p == 0).all(), "A^p commutes with A, B")
        # not absolutely irreducible
        refuted(bool(MTX_ABS(gm)), "over the closure V splits")
        # the conclusion of th:commutator-identity-trace still holds here for p > 2
        if p > 2:
            check(trace(A @ B, p) == 0, "Tr(AB) = 0")

    # th:commutator-identity-trace: all pairs (A, B) in M_3(F_3), M_2(F_2)
    def all_pairs(n, p):
        identity = np.eye(n, dtype=np.int64).reshape(n * n)
        count = 0
        seen_traces = set()
        for vals in itertools.product(range(p), repeat=n * n):
            A = np.array(vals, dtype=np.int64).reshape((n, n))
            # B -> A B - B A
            T = (np.kron(A, np.eye(n, dtype=np.int64)) - np.kron(np.eye(n, dtype=np.int64), A.T)) % p
            B = solve(T, identity, p)
            if B is None:
                continue
            count += 1
            Bm = B.reshape((n, n))
            assert ((A @ Bm - Bm @ A) % p == np.eye(n, dtype=np.int64)).all()
            N = nullspace(T, p)
            seen_traces.add(trace(A @ Bm, p))
            for w in N:
                seen_traces.add(trace(A @ (Bm + w.reshape((n, n))) % p, p))
        return count, seen_traces

    count, tr = all_pairs(3, 3)
    check(count > 0 and tr == {0}, "all A in M_3(F_3): Tr(AB) = 0")
    count, tr = all_pairs(2, 2)
    check(count > 0 and tr == {1}, "all A in M_2(F_2): Tr(AB) = 1, so p > 2 is needed")
    count, tr = all_pairs(2, 3)
    check(count == 0, "M_2(F_3): no solutions since 3 does not divide 2")
    # direct sums and nonsplit extensions
    for p in (3, 5, 7):
        A, B = A1(p), B1(p)
        I = np.eye(p, dtype=np.int64)
        for k in (2, 3):
            J = np.zeros((k, k), dtype=np.int64)
            for i in range(k - 1):
                J[i, i + 1] = 1
            E2 = np.eye(k, dtype=np.int64)
            AA = (np.kron(A, E2) + np.kron(I, J)) % p
            BB = (np.kron(B, E2) + np.kron(I, J.T)) % p
            n = p * k
            check(((AA @ BB - BB @ AA) % p == (np.eye(n, dtype=np.int64) + np.kron(I, J @ J.T - J.T @ J)) % p).all())
            # with [J, J'] = 0 only: J and J^2
            BB = (np.kron(B, E2) + np.kron(I, J @ J)) % p
            check(((AA @ BB - BB @ AA) % p == np.eye(n, dtype=np.int64)).all(), "a nonsplit module")
            check(trace(AA @ BB, p) == 0, "Tr(AB) = 0 on it")


def lie_span(mats, p):
    """A basis of the Lie algebra generated by mats."""
    k = mats[0].shape[0]
    cur = rref(np.array([m.reshape(k * k) for m in mats], dtype=np.int64), p)[0]
    while True:
        ms = [r.reshape((k, k)) for r in cur]
        new = [((a @ b - b @ a) % p).reshape(k * k) for a in ms for b in ms]
        nxt = rref(np.concatenate([cur, np.array(new, dtype=np.int64)]), p)[0]
        if nxt.shape[0] == cur.shape[0]:
            return ms
        cur = nxt


def nilpotency_ok(L):
    """Is the algebra nilpotent?  The lower central series reaches 0."""
    p = L.p
    cur = np.eye(L.n, dtype=np.int64)
    for _ in range(L.n + 1):
        if cur.shape[0] == 0:
            return True
        prods = []
        for u in cur:
            for j in range(L.n):
                prods.append(L.prod(u, L.basis(j)))
        cur = rref(np.array(prods, dtype=np.int64), p)[0]
    return cur.shape[0] == 0


def section_7_theorem_78():
    # L = (B_1, I, A_1, ..., A_1^k): nilpotent, [A^i, B] = i A^(i-1)
    for p in (3, 5, 7):
        A, B = A1(p), B1(p)
        for k in range(2, p):
            gens = [B] + [matpow(A, i, p) for i in range(0, k + 1)]
            mats = lie_span(gens, p)
            L = alg_from_mats(mats, p)
            check(nilpotency_ok(L), "L is nilpotent")
            check(L.jacobi())
            # a in L^2 with a L . L = 0
            der = L.derived()
            n = L.n
            d = der.shape[0]
            mat_rows = []
            for j in range(n):
                for m in range(n):
                    ej, em = L.basis(j), L.basis(m)
                    mat_rows.append([L.prod(L.prod(der[i], ej), em) for i in range(d)])
            M = np.array(mat_rows, dtype=np.int64)  # (pairs, d, n)
            M2 = np.transpose(M, (0, 2, 1)).reshape((n * n * n, d))
            ns = nullspace(M2, p)
            good = (ns @ der) % p
            check(good.shape[0] >= 1, "there are such elements")
            # f(a, b) = Tr(S(a) S(b)) with S the identity: coordinates in mats
            G = trace_form_gram(mats, p)
            check(not ((good @ G) % p).any(), "th:nilpotent-representation-trace, dimension p")
            # a representation with larger dimension: V + V
            G2 = trace_form_gram([np.kron(m, np.eye(2, dtype=np.int64)) for m in mats], p)
            check(not ((good @ G2) % p).any())
            # there are a, b with [a, b] = I: case I occurs
            Am = A % p
            check(in_span(mats, Am, p), "A_1 in L")
            check(((A @ B - B @ A) % p == np.eye(p, dtype=np.int64)).all(), "case I: [A, B] = I")
            # th:nilpotent-projective-form: L_0 = L / (I) nonabelian: its form is degenerate
            check(rank(G, p) < L.n - 1, "the form on L_0 is degenerate")
    # unitriangular algebras in the natural representation and its sum with the adjoint
    for p, k in ((3, 3), (3, 4), (5, 4)):
        mats = [E(k, i, j) for i in range(k) for j in range(i + 1, k)]
        L = alg_from_mats(mats, p)
        check(nilpotency_ok(L))
        G = trace_form_gram(mats, p)
        check(not G.any(), "the natural form of a unitriangular algebra is 0")
    # nilpotency is needed: gl_3 mod 3, a = I in L^2 and central, f(I, E_11) = 1
    p = 3
    mats = gl_basis(3)
    L = alg_from_mats(mats, p)
    I = np.eye(3, dtype=np.int64)
    check(in_span(sl_basis(3), I, p), "I in L^2")
    refuted(trace(I @ E(3, 0, 0), p) == 0, "without nilpotency f(a, L) = 0 fails")
    refuted(nilpotency_ok(L), "gl_3 is not nilpotent")
    # th:nilpotent-projective-form, the abelian case: diagonal matrices mod scalars, p | n
    for n, p in ((3, 3), (5, 5), (6, 3), (7, 7)):
        D = [E(n, i, i) - E(n, i + 1, i + 1) for i in range(n - 1)]
        G = trace_form_gram(D, p)
        check(rank(G, p) == n - 2, "H of N: nondegenerate on H / Z")


def cartan_scan(L, trials, rng, name):
    """Engel subalgebras of random elements; for those that are Cartan subalgebras, the
    conclusions of th:projective-form-cartan, th:projective-form-center,
    th:v-algebra-from-projective."""
    p, n = L.p, L.n
    found = 0
    dims = set()
    for _ in range(trials):
        x = np.array([rng.randrange(p) for _ in range(n)], dtype=np.int64)
        Rx = L.R(x)
        E0 = nullspace(matpow(Rx, n, p).T, p)  # {v : v R_x^n = 0}
        if E0.shape[0] == 0:
            continue
        # nilpotent?
        sub = Alg(structure_on(L, E0), p)
        if not nilpotency_ok(sub):
            continue
        # self-normalizing?
        d = E0.shape[0]
        rows = []
        Q = rref(E0, p)[0]
        piv = rref(E0, p)[1]
        # y with y e in E for all e in E: use a complement functional
        comp = nullspace(Q, p)  # functionals vanishing on E
        for e in E0:
            Re = L.R(e)
            rows.append((Re @ comp.T) % p)
        M = np.concatenate(rows, axis=1)
        norm = nullspace(M.T, p)
        if norm.shape[0] != d:
            continue
        found += 1
        dims.add(d)
        check(not sub.C.any(), "Cartan subalgebra abelian, %s" % name)
        check(all(is_semisimple(L.R(e), p) for e in E0), "Cartan subalgebra diagonalizable, %s" % name)
        # a^[p] = 0 only for a = 0 on H; H is closed under the p-th power (used for
        # th:commuting-matrices-power in th:v-algebra-from-projective, tacitly)
        good = True
        for cs in itertools.product(range(p), repeat=d):
            if not any(cs):
                continue
            a = np.array(cs, dtype=np.int64) @ E0 % p
            good = good and bool(matpow(L.R(a), p, p).any())
        check(good, "th:projective-form-center, %s" % name)
        for e in E0:
            y = L.inner_power(e)
            check(y is not None and solve(E0.T, y, p) is not None, "H is closed under the p-th power, %s" % name)
    return found, dims


def structure_on(L, E0):
    """Structure constants of the subalgebra with rows E0 as a basis; asserts closure."""
    p = L.p
    d = E0.shape[0]
    C = np.zeros((d, d, d), dtype=np.int64)
    A = E0.T
    for i in range(d):
        for j in range(d):
            v = L.prod(E0[i], E0[j])
            x = solve(A, v, p)
            assert x is not None
            C[i, j] = x
    return C


def section_7_cartan():
    rng = random.Random(5)
    # psl_5, psl_3 as the hypotheses allow p > 2; sl_3 mod 5, so_5, sp_4, G_2
    examples = []
    M, N, mats, co, kept = psl(5, 5)
    examples.append(("psl_5 mod 5", N, 3))
    M, N, mats, co, kept = psl(3, 3)
    examples.append(("psl_3 mod 3", N, None))
    examples.append(("sl_3 mod 5", alg_from_mats(sl_basis(3), 5), 2))
    examples.append(("so_5 mod 5", alg_from_mats(so_basis(5, 5), 5), 2))
    examples.append(("sp_4 mod 7", alg_from_mats(sp_basis(4, 7), 7), 2))
    examples.append(("G_2 mod 5", alg_from_mats(g2_basis(5), 5), 2))
    examples.append(("G_2 mod 7", alg_from_mats(g2_basis(7), 7), 2))
    for name, L, rk in examples:
        check(L.center().shape[0] == 0 and L.is_perfect(), "%s: no center, L^2 = L" % name)
        found, dims = cartan_scan(L, 30, rng, name)
        check(found > 0, "%s: Cartan subalgebras found" % name)
        if rk is not None:
            check(dims == {rk}, "%s: dimension of the Cartan subalgebras %s" % (name, dims))
    # The hypothesis is needed: the Witt algebra.  All invariant forms vanish, the form of
    # F[x]/(x^p) is 0; S is a representation into M.
    for p in (5, 7, 11):
        W = witt(p)
        check(W.invariant_forms() == [], "W_1, p = %d: no nonzero invariant form" % p)
        S = witt_rep(p)
        for a in range(p):
            for b in range(p):
                br = sum(int(W.C[a, b, k]) * S[k] for k in range(p)) % p
                check(((S[a] @ S[b] - S[b] @ S[a]) % p == br).all(), "S is a representation")
            check(trace(S[a], p) == 0, "S lands in M")
        check(not trace_form_gram(S, p).any(), "the form of F[x]/(x^p) on W_1 is 0")
        # H = (e_0) has one-dimensional root spaces for all of GF(p)^*: rank 1, not sl_2, no form
        H0 = W.R(W.basis(1))
        check(sorted(int(H0[i, i]) for i in range(p)) == list(range(p)), "the roots of W_1 fill GF(p)")
    # Zassenhaus: no nonzero invariant form
    Z2 = zassenhaus(5)
    check(Z2.invariant_forms() == [], "W(1; 2): no nonzero invariant form")
    # The form must come from a representation: L = sl_2 (x) F[t]/(t^p) has no center, L^2 = L, and a
    # nondegenerate invariant form (Killing form (x) the coefficient of t^(p-1)), but its Cartan subalgebra
    # H = h (x) F[t]/(t^p) contains a = h (x) t != 0 with a^p = 0, R_a not semisimple: the conclusions of
    # th:projective-form-center and th:v-algebra-from-projective fail, so no projective representation
    # gives such a form.
    for p in (3, 5):
        S = alg_from_mats(sl_basis(2), p)  # basis E_12, E_21, h
        n = 3 * p
        C = np.zeros((n, n, n), dtype=np.int64)
        for i in range(3):
            for j in range(3):
                for s in range(p):
                    for t in range(p):
                        if s + t < p:
                            for k in range(3):
                                C[i * p + s, j * p + t, k * p + s + t] = S.C[i, j, k]
        L = Alg(C, p)
        check(L.jacobi() and L.center().shape[0] == 0 and L.is_perfect(), "sl_2 (x) F[t]/(t^p)")
        forms = L.invariant_forms()
        check(any(rank(F, p) == n for F in forms), "it has a nondegenerate invariant form")
        Hidx = [2 * p + s for s in range(p)]
        E0 = np.array([L.basis(i) for i in Hidx], dtype=np.int64)
        sub = Alg(structure_on(L, E0), p)
        check(not sub.C.any(), "H = h (x) F[t]/(t^p) is abelian")
        # H is its own normalizer: y h(x)1 in H forces y in H, the roots +-2 being nonzero
        Rh = L.R(L.basis(2 * p))
        check(rank(matpow(Rh, n, p), p) == n - p, "H is the Engel subalgebra of h (x) 1")
        a = L.basis(2 * p + 1)
        check(not matpow(L.R(a), p, p).any() and a.any(), "a^p = 0, a != 0")
        refuted(is_semisimple(L.R(a), p), "H is not diagonalizable")


def section_7_theorem_81():
    # th:linear-lie-element on sl_p, p = 3, 5: A = A_1, I + A_1
    for p in (3, 5):
        I = np.eye(p, dtype=np.int64)
        base = sl_basis(p)
        check(rref(np.array([((a @ b - b @ a) % p).reshape(p * p) for a in base for b in base]), p)[0].shape[0] == len(base),
              "sl_p is perfect")
        for A in (A1(p), (I + A1(p)) % p):
            Ap = matpow(A, p, p)
            for D in base:
                br = (Ap @ D - D @ Ap) % p
                check(not ((br - br[0, 0] * I) % p).any() and not (br % p).any(), "[A^p L] is central")
            # all B in sl_p with [A, B] scalar
            k = p * p
            A_l = np.array([b.reshape(k) for b in base], dtype=np.int64)  # rows
            # B = sum c_i b_i: A B - B A must be a scalar; impose its entries off the
            # diagonal and equal diagonal
            rows = []
            comm = [((A @ b - b @ A) % p) for b in base]
            for i in range(p):
                for j in range(p):
                    if i != j:
                        rows.append([int(c[i, j]) for c in comm])
                    elif i > 0:
                        rows.append([int((c[i, i] - c[0, 0]) % p) for c in comm])
            sols = nullspace(np.array(rows, dtype=np.int64), p)
            check(sols.shape[0] >= 1, "there are such B")
            for v in sols:
                B = sum(int(c) * b for c, b in zip(v, base)) % p
                check(trace(A @ B, p) == 0, "Tr(A B) = 0")
    # needed: [A^p L] central
    p = 3
    A = np.diag([1, 2, 0])
    Ap = matpow(A, p, p)
    check((Ap == A).all(), "A^3 = A")
    refuted(all(not ((Ap @ D - D @ Ap) % p).any() for D in sl_basis(3)), "[A^p L] is not central")
    check(trace(A @ A, p) != 0 and not ((A @ A - A @ A) % p).any(), "without it Tr(AB) != 0")
    # needed: p > 2: gl_2 mod 2
    p = 2
    A, B = A1(2), B1(2)
    check(((A @ B - B @ A) % p == np.eye(2, dtype=np.int64)).all() and not matpow(A, 2, 2).any())
    check(in_span(sl_basis(2), B, p), "B in [L L] for L = gl_2")
    refuted(trace(A @ B, p) == 0, "p > 2 is needed")


def section_7_theorem_83():
    rng = random.Random(6)
    for p in (3, 5):
        for n in (2, 3, 4):
            I = np.eye(n, dtype=np.int64)
            while True:
                g = np.array([[rng.randrange(p) for _ in range(n)] for _ in range(n)], dtype=np.int64)
                if rank(g, p) == n:
                    break
            ginv = rref(np.concatenate([g, I], axis=1), p)[0][:, n:]
            S = [g @ E(n, i, i) @ ginv % p for i in range(n)]
            elements = []
            for cs in itertools.product(range(p), repeat=n):
                elements.append(sum(int(c) * s for c, s in zip(cs, S)) % p)
            for X in elements:
                check(any((matpow(X, p, p) == Y).all() for Y in elements), "closed under p-th powers")
            images = {matpow(X, p, p).tobytes() for X in elements}
            check(len(images) == len(elements), "the p-th power map is a bijection on T")
            # additive on commuting matrices
            for _ in range(5):
                X, Y = rng.choice(elements), rng.choice(elements)
                check((matpow((X + Y) % p, p, p) == (matpow(X, p, p) + matpow(Y, p, p)) % p).all())
    # semilinear, not linear
    K = GF(9, "w")
    w = K.gen()
    X = matrix(K, 2, 2, [1, 1, 0, 0])
    check((w * X)**3 == w**3 * X**3)
    refuted((w * X)**3 == w * X**3, "not linear")
    # hypotheses needed
    for p in (3, 5):
        N = np.array([[0, 1], [0, 0]], dtype=np.int64)
        C = (np.eye(2, dtype=np.int64) + N) % p
        # S = F C: no nilpotents; C^p = I is not in S; C is not diagonalizable
        Cp = matpow(C, p, p)
        check((Cp == np.eye(2, dtype=np.int64)).all())
        refuted(any(((c * C) % p == Cp).all() for c in range(p)), "closed under p-th powers")
        refuted(is_semisimple(C, p), "C is not diagonalizable")
        # S = (I, N): closed under powers, contains the nilpotent N, N is not diagonalizable
        refuted(is_semisimple(N, p), "N is not diagonalizable")
        # C^(p^k) is diagonalizable for a large k: a Jordan block of size 2
        check(is_semisimple(matpow(C, p, p), p))
        # non-split torus: F_p[theta] in M_2(F_p), no eigenvalue in F_p; semisimple only over the closure
        R = PolynomialRing(GF(p), "x")
        f = R.irreducible_element(2, algorithm="first_lexicographic")
        co = [int(c) for c in f.list()]
        Th = np.array([[0, 1], [(-co[0]) % p, (-co[1]) % p]], dtype=np.int64)
        check(is_semisimple(Th, p), "a torus over the closure")
        # no eigenvalues over F_p
        for lam in range(p):
            check(rank((Th - lam * np.eye(2, dtype=np.int64)) % p, p) == 2, "not diagonalizable over F_p")


def section_7_exercise():
    # exc:form-vanishes-trace-zero
    for n, p in ((2, 2), (3, 3), (4, 2), (5, 5), (6, 2), (6, 3)):
        mats = gl_basis(n)
        L = alg_from_mats(mats, p)
        I = np.eye(n, dtype=np.int64).reshape(n * n)
        k = n * n
        A = np.array([m.reshape(k) for m in mats], dtype=np.int64).T
        co = solve(A, I, p)
        # drop the last diagonal matrix E_nn: its coefficient in I is 1
        drop = (n - 1) * n + (n - 1)
        Q, kept = quotient(L, [co], [drop])
        forms = Q.invariant_forms()
        check(len(forms) >= 1, "L/Z has a nonzero invariant form: Tr(X) Tr(Y)")
        # M/Z in the basis kept: X = sum x_i b_i has trace = sum x_i Tr(b_i); elements of M/Z
        traces = np.array([trace(mats[i], p) for i in kept], dtype=np.int64)
        Mz = nullspace(traces.reshape((1, -1)), p)
        # all forms vanish on (M/Z) x (L/Z)
        for F in forms:
            check(not ((Mz @ F) % p).any(), "the form vanishes on M/Z, (%d, %d)" % (n, p))
        # and they are multiples of Tr(X) Tr(Y)
        T = np.outer(traces, traces) % p
        for F in forms:
            check(rank(np.array([T.reshape(-1), F.reshape(-1)]), p) == 1, "F = g Tr(X) Tr(Y)")
    # p does not divide n: the form Tr(XY) lives on sl_n = gl_n / Z
    p, n = 5, 2
    L = alg_from_mats(sl_basis(n), p)
    forms = L.invariant_forms()
    check(len(forms) == 1 and forms[0].any(), "p does not divide n: forms do not vanish on M/Z")


# ---------------------------------------------------------------------------
# Section 8
# ---------------------------------------------------------------------------


class VA:
    """A candidate V-algebra over GF(p) on a basis: mul sparse, H a list of indices, the
    other indices lie in root spaces; form as a dictionary on pairs of indices."""

    def __init__(self, name, p, n, mul, H, form):
        self.name, self.p, self.n, self.H = name, p, n, H
        self.mul = {}
        for key, d in mul.items():
            d = {k: c % p for k, c in d.items() if c % p}
            if d:
                self.mul[key] = d
        self.form = {}
        for key, c in form.items():
            if c % p:
                self.form[key] = c % p
        self.others = [i for i in range(n) if i not in set(H)]
        self.wt = {}
        zero = tuple(0 for _ in H)
        for i in H:
            self.wt[i] = zero
        for i in self.others:
            v = []
            for h in H:
                d = self.mul.get((i, h), {})
                assert set(d) <= {i}, "a h = alpha(h) a"
                v.append(d.get(i, 0))
            self.wt[i] = tuple(v)
        self.roots = {}
        for i in self.others:
            self.roots.setdefault(self.wt[i], []).append(i)
        self.Rset = set(self.roots)
        self.G_H = np.array([[self.form.get((a, b), 0) for b in H] for a in H], dtype=np.int64)

    def f(self, u, v):
        out = 0
        for i, a in u.items():
            for j, b in v.items():
                out += a * b * self.form.get((i, j), 0)
        return out % self.p

    def prod(self, u, v):
        out = {}
        for i, a in u.items():
            for j, b in v.items():
                for k, c in self.mul.get((i, j), {}).items():
                    out[k] = (out.get(k, 0) + a * b * c) % self.p
        return {k: c for k, c in out.items() if c}

    def add_wt(self, a, b, c=1):
        return tuple((x + c * y) % self.p for x, y in zip(a, b))

    def neg_wt(self, a):
        return tuple((-x) % self.p for x in a)

    def h_of(self, a):
        """Coordinates on H of h_alpha: (h_alpha, k) = alpha(k)."""
        x = solve(self.G_H, list(a), self.p)
        assert x is not None
        return tuple(int(c) for c in x)

    def setup_h(self):
        self.h = {a: self.h_of(a) for a in self.Rset}
        self.G_list = self.G_H.tolist()

    def ip(self, a, b):
        """(h_alpha, h_beta) = beta(h_alpha)."""
        return sum(x * y for x, y in zip(b, self.h[a])) % self.p


def check_axioms(V, jacobi=True):
    p, name = V.p, V.name
    # H abelian
    check(all((a, b) not in V.mul for a in V.H for b in V.H), "H abelian, %s" % name)
    zero = tuple(0 for _ in V.H)
    # roots: distinct nonzero functions: every others-index has a nonzero weight
    check(zero not in V.Rset, "roots are nonzero, %s" % name)
    check(len(V.others) > 0, "L != H")
    # symmetric, antisymmetric
    check(all(V.form.get((j, i), 0) == c for (i, j), c in V.form.items()), "symmetric form")
    check(all(((V.mul.get((j, i), {}).get(k, 0) + c) % p) == 0 for (i, j), d in V.mul.items() for k, c in d.items()), "antisymmetric")
    # nondegenerate
    Gm = np.zeros((V.n, V.n), dtype=np.int64)
    for (i, j), c in V.form.items():
        Gm[i, j] = c
    check(rank(Gm, p) == V.n, "the form is nondegenerate, %s" % name)
    # th:root-spaces-inclusion
    ok85 = True
    for (i, j), d in V.mul.items():
        w = V.add_wt(V.wt[i], V.wt[j])
        for k in d:
            ok85 = ok85 and V.wt[k] == w
    check(ok85, "th:root-spaces-inclusion, %s" % name)
    # th:negative-root: orthogonality; L_alpha, L_-alpha dual; nondegenerate on H
    ok86 = True
    for (i, j), c in V.form.items():
        ok86 = ok86 and V.add_wt(V.wt[i], V.wt[j]) == zero
    check(ok86, "L_alpha orthogonal to L_beta unless beta = -alpha, %s" % name)
    check(rank(V.G_H, p) == len(V.H), "nondegenerate on H, %s" % name)
    good = True
    for a, idx in V.roots.items():
        na = V.neg_wt(a)
        good = good and na in V.Rset and len(V.roots[na]) == len(idx)
        M = np.array([[V.form.get((i, j), 0) for j in V.roots[na]] for i in idx], dtype=np.int64)
        good = good and rank(M, p) == len(idx)
    check(good, "-alpha is a root, L_alpha and L_-alpha are dual, %s" % name)
    # invariance, on triples of opposite total weight
    by_wt = {}
    for i in range(V.n):
        by_wt.setdefault(V.wt[i], []).append(i)
    inv = True
    for i in range(V.n):
        for j in range(V.n):
            w = V.neg_wt(V.add_wt(V.wt[i], V.wt[j]))
            for k in by_wt.get(w, []):
                left = sum(c * V.form.get((m, k), 0) for m, c in V.mul.get((i, j), {}).items())
                right = sum(c * V.form.get((i, m), 0) for m, c in V.mul.get((j, k), {}).items())
                inv = inv and (left - right) % p == 0
    check(inv, "the form is invariant, %s" % name)
    # Jacobi
    if jacobi:
        ok = True
        for x in range(V.n):
            for y in range(x + 1, V.n):
                for z in range(y + 1, V.n):
                    t = {}
                    for (s1, s2, s3) in ((x, y, z), (y, z, x), (z, x, y)):
                        for m, c in V.mul.get((s1, s2), {}).items():
                            for w, e in V.mul.get((m, s3), {}).items():
                                t[w] = (t.get(w, 0) + c * e) % p
                    if any(t.values()):
                        ok = False
        check(ok, "Jacobi identity, %s" % name)
    V.setup_h()
    # th:root-element-unique
    ok87 = True
    for a, idx in V.roots.items():
        ha = V.h[a]
        # (h_alpha, k) = alpha(k)
        for j in range(len(V.H)):
            ok87 = ok87 and sum(ha[i] * V.G_list[i][j] for i in range(len(V.H))) % p == a[j]
        for i1 in idx:
            for i2 in V.roots[V.neg_wt(a)]:
                pr = V.mul.get((i1, i2), {})
                c = V.form.get((i1, i2), 0)
                target = {V.H[t]: (-c * ha[t]) % p for t in range(len(V.H)) if (-c * ha[t]) % p}
                ok87 = ok87 and pr == target
    check(ok87, "a x = -(a, x) h_alpha, %s" % name)
    # beta(h_alpha) = alpha(h_beta) = (h_alpha, h_beta)
    ok = True
    roots = list(V.Rset)
    for a in roots[:40]:
        for b in roots[:40]:
            ok = ok and V.ip(a, b) == V.ip(b, a)
    check(ok, "beta(h_alpha) = alpha(h_beta), %s" % name)


def center_dim(V):
    """dim {z : z e_j = 0 for all j} by sparse elimination."""
    return V.n - sparse_rank(center_rows(V), V.p)


def center_rows(V):
    rows = {}
    for (i, j), d in V.mul.items():
        for k, c in d.items():
            rows.setdefault((j, k), {})[i] = c
    return list(rows.values())


def sparse_rank(rows, p):
    pivots = {}
    for row in rows:
        row = dict(row)
        while row:
            t = min(row)
            if t not in pivots:
                inv = pow(row[t], -1, p)
                pivots[t] = {k: v * inv % p for k, v in row.items()}
                break
            f = row[t]
            for k, v in pivots[t].items():
                nv = (row.get(k, 0) - f * v) % p
                if nv:
                    row[k] = nv
                else:
                    row.pop(k, None)
    return len(pivots)


def check_exercises(V):
    p, name = V.p, V.name
    nH = len(V.H)
    # exc:h-cartan-subalgebra: H is abelian and self-normalizing: y h in H for all h forces
    # y in H, since each root is nonzero on some h
    check(all(any(a) for a in V.Rset), "H self-normalizing, %s" % name)
    # exc:derived-algebra (a): L^2 = H* + sum L_alpha
    rows = list(V.mul.values())
    der = sparse_rank(rows, p)
    Hstar = np.array([V.h[a] for a in V.Rset], dtype=np.int64)
    rk = rank(Hstar, p)
    check(der == rk + len(V.others), "L^2 = H* + sum L_alpha, %s" % name)
    # (b): Z is the orthogonal complement of H* in H
    Z = center_dim(V)
    check(Z == nH - rk, "Z = orthogonal complement of H*, %s" % name)
    # the complement consists of central elements: alpha(z) = 0 for all alpha
    W = np.array(list(V.Rset), dtype=np.int64)
    zs = nullspace(W, p)
    check(zs.shape[0] == Z, "alpha(z) = 0 for all alpha describes Z")
    # (c): L^2 = L gives Z = 0; exc:no-center-perfect: Z = 0 gives L^2 = L here (H finite)
    if der == V.n:
        check(Z == 0, "L^2 = L gives Z = 0")
    if Z == 0:
        check(der == V.n, "exc:no-center-perfect, %s" % name)
        # (d), (e): L^2 = L here, the statements hold trivially
    # (e) as corrected: Z = 0 gives L^2 . L^2 = L^2; the printed form: see section_8_exercises
    # theorem 90: no center implies no isotropic roots
    iso = [a for a in V.Rset if V.ip(a, a) == 0]
    if Z == 0:
        check(iso == [], "th:no-isotropic-roots, %s" % name)
    # for isotropic alpha: alpha is orthogonal to all roots, h_alpha is central
    for a in iso:
        check(all(V.ip(a, b) == 0 for b in V.Rset), "isotropic alpha orthogonal to all roots, %s" % name)
    return iso, Z


def root_level(V):
    """Theorems 89, 91-96 for a V-algebra with nonisotropic roots."""
    p, name = V.p, V.name
    Rs = list(V.Rset)
    Rset = V.Rset
    zero = tuple(0 for _ in V.H)
    ok = dict(dim1=True, prop=True, t91=True, t91b=True, t92=True, t93=True, t94=True, t95=True, t96=True)
    residues = {x % p for x in (0, 1, -1, 2, -2, 3, -3)}
    r_values = {x % p: x for x in (3, 2, 1, 0)}
    inv = {}
    for a in Rs:
        ok["dim1"] = ok["dim1"] and len(V.roots[a]) == 1
        for c in range(2, p - 1):
            ok["prop"] = ok["prop"] and tuple(c * x % p for x in a) not in Rset
    string_ok = True
    for a in Rs:
        naa = V.ip(a, a)
        iaa = pow(naa, -1, p)
        na = V.neg_wt(a)
        ia = V.roots[a][0]
        ix = V.roots[na][0]
        for b in Rs:
            ib = V.roots[b][0]
            vab = V.ip(a, b)
            q = 2 * vab * iaa % p
            ok["t95"] = ok["t95"] and q in residues
            bp = V.add_wt(b, a)
            bm = V.add_wt(b, a, -1)
            # th:five-root-string
            five = all(V.add_wt(b, a, i) in Rset for i in (-2, -1, 0, 1, 2))
            ok["t92"] = ok["t92"] and not five
            if b == a or b == na:
                continue
            # th:orthogonal-roots
            if bp not in Rset and bm not in Rset:
                ok["t91"] = ok["t91"] and vab == 0
                # L_beta h_alpha = 0, the corrected line of the proof
                ok["t91b"] = ok["t91b"] and V.prod({ib: 1}, {V.H[t]: V.h[a][t] for t in range(len(V.H))}) == {}
            # th:root-sum-product
            if bp in Rset:
                ok["t93"] = ok["t93"] and (ib, ia) in V.mul
            # th:root-string-mod-p, th:root-string-length-char-p
            if bm not in Rset:
                r = (-q) % p
                if r not in r_values:
                    ok["t94"] = False
                    continue
                r = r_values[r]
                run = all(V.add_wt(b, a, i) in Rset for i in range(0, r + 1))
                top = V.add_wt(b, a, r + 1) in Rset
                ok["t94"] = ok["t94"] and run and not top
                # the length by walking: theorem 96
                t = 0
                while V.add_wt(b, a, t + 1) in Rset and t < p:
                    t += 1
                ok["t96"] = ok["t96"] and t == r
                # the products along the string: with a x = h (normalised),
                # u_i R_a R_x = (i + 1)(lambda + i/2) u_i, lambda = (h_alpha, h_beta)/(h_alpha, h_alpha)
                c_ax = V.form.get((ia, ix), 0)
                s = (-pow(c_ax, -1, p) * iaa) % p  # x' = s x gives a x' = h
                lam = vab * iaa % p
                half = pow(2, -1, p)
                for i in range(0, r + 1):
                    wt = V.add_wt(b, a, i)
                    iu = V.roots[wt][0]
                    v = V.prod(V.prod({iu: 1}, {ia: 1}), {ix: s})
                    expected = (i + 1) * (lam + i * half) % p
                    string_ok = string_ok and v.get(iu, 0) == expected and set(v) <= {iu}
                    if i < r:
                        string_ok = string_ok and expected != 0
    check(ok["dim1"], "th:nonisotropic-root: L_alpha one-dimensional, %s" % name)
    check(ok["prop"], "th:nonisotropic-root: no proportional roots, %s" % name)
    check(ok["t91"], "th:orthogonal-roots, %s" % name)
    check(ok["t91b"], "L_beta h_alpha = 0, %s" % name)
    check(ok["t92"], "th:five-root-string, %s" % name)
    check(ok["t93"], "th:root-sum-product, %s" % name)
    check(ok["t94"], "th:root-string-mod-p, %s" % name)
    check(ok["t95"], "th:cartan-integers-char-p, %s" % name)
    check(ok["t96"], "th:root-string-length-char-p, %s" % name)
    check(string_ok, "the products along the strings, %s" % name)
    # the rank 1 subalgebra of the proof of th:nonisotropic-root
    good = True
    for a in Rs[:60]:
        ia = V.roots[a][0]
        ix = V.roots[V.neg_wt(a)][0]
        ha = {V.H[t]: V.h[a][t] for t in range(len(V.H)) if V.h[a][t]}
        good = good and V.f(ha, ha) != 0
        good = good and V.prod({ia: 1}, ha) == ({ia: V.ip(a, a)})
        pr = V.prod({ia: 1}, {ix: 1})
        c = V.form.get((ia, ix), 0)
        good = good and pr == {k: (-c * v) % p for k, v in ha.items()}
    check(good, "H_0 + L_alpha + L_-alpha is a V-algebra of rank 1, %s" % name)


CHEV = {}


def chevalley_data(t):
    if t in CHEV:
        return CHEV[t]
    if isinstance(t[0], tuple):
        ct = CartanType([[s[0], s[1]] for s in t])
    else:
        ct = CartanType([t[0], t[1]])
    A = LieAlgebra(QQ, cartan_type=ct)
    keys = list(A.basis().keys())
    idx = {k: i for i, k in enumerate(keys)}
    n = len(keys)
    mul = {}
    for (x, y), v in A.structure_coefficients().items():
        d = {idx[k]: int(c) for k, c in v.monomial_coefficients().items()}
        mul[(idx[x], idx[y])] = d
        mul[(idx[y], idx[x])] = {k: -c for k, c in d.items()}
    H = [i for k, i in idx.items() if "check" in str(k)]
    # Killing form as a trace, over ZZ, on H x H and on the pairs of opposite roots
    triples = [{} for _ in range(n)]
    for (z, x), d in mul.items():
        for w, c in d.items():
            triples[x][(z, w)] = c
    def killing(x, y):
        return sum(c * triples[y].get((w, z), 0) for (z, w), c in triples[x].items())
    form = {}
    I = list(ct.index_set())
    neg = {}
    for k, i in idx.items():
        if "check" not in str(k):
            neg[i] = idx[-k]
    for a in H:
        for b in H:
            v = killing(a, b)
            if v:
                form[(a, b)] = v
    for i, j in neg.items():
        form[(i, j)] = killing(i, j)
    g = 0
    for v in form.values():
        g = gcd(g, v)
    form = {k: int(ZZ(v) // g) for k, v in form.items()}
    CHEV[t] = (n, mul, H, form, ct, int(g))
    return CHEV[t]


def chevalley(t, p):
    n, mul, H, form, ct, g = chevalley_data(t)
    name = "%s mod %d" % (t, p)
    return VA(name, p, n, mul, H, form)


def gl_va(n, p):
    """gl_n with H the diagonal, the form Tr(XY).  Basis: E_ij."""
    idx = {(i, j): i * n + j for i in range(n) for j in range(n)}
    mul = {}
    for (i, j), a in idx.items():
        for (k, l), b in idx.items():
            d = {}
            if j == k:
                d[idx[(i, l)]] = d.get(idx[(i, l)], 0) + 1
            if l == i:
                d[idx[(k, j)]] = d.get(idx[(k, j)], 0) - 1
            d = {m: c for m, c in d.items() if c}
            if d:
                mul[(a, b)] = d
    H = [idx[(i, i)] for i in range(n)]
    form = {(idx[(i, j)], idx[(j, i)]): 1 for i in range(n) for j in range(n)}
    return VA("gl_%d mod %d" % (n, p), p, n * n, mul, H, form)


def psl_va(n, p):
    """L^2 / Z of gl_n, p | n: the kept basis is E_ij (i != j), d_1, ..., d_(n-2)."""
    M, N, mats, co, kept = psl(n, p)
    m = N.n
    mul = {}
    for i in range(m):
        for j in range(m):
            nz = np.nonzero(N.C[i, j])[0]
            if nz.size:
                mul[(i, j)] = {int(k): int(N.C[i, j, k]) for k in nz}
    keptm = [mats[i] for i in kept]
    H = [i for i in range(m) if (keptm[i] == np.diag(np.diag(keptm[i]))).all()]
    form = {}
    for i in range(m):
        for j in range(m):
            v = trace(keptm[i] @ keptm[j], p)
            if v:
                form[(i, j)] = v
    return VA("psl_%d mod %d" % (n, p), p, m, mul, H, form), keptm


def oscillator(k, p):
    """a_i, x_i (i < k), h, t: a_i x_i = h, a_i t = a_i, x_i t = -x_i.  Form: (a_i, x_i) = -1,
    (h, t) = 1.  k = 1 is exc:four-dim-isotropic."""
    n = 2 * k + 2
    a = list(range(k))
    x = list(range(k, 2 * k))
    h, t = 2 * k, 2 * k + 1
    mul = {}
    form = {(h, t): 1, (t, h): 1}
    for i in range(k):
        mul[(a[i], x[i])] = {h: 1}
        mul[(x[i], a[i])] = {h: -1}
        mul[(a[i], t)] = {a[i]: 1}
        mul[(t, a[i])] = {a[i]: -1}
        mul[(x[i], t)] = {x[i]: -1}
        mul[(t, x[i])] = {x[i]: 1}
        form[(a[i], x[i])] = -1
        form[(x[i], a[i])] = -1
    return VA("oscillator_%d mod %d" % (k, p), p, n, mul, [h, t], form)


def hamiltonian_like(p):
    """h_1, h_2, t_1, t_2, e_beta (beta in GF(p)^2 minus 0): e_beta t_i = beta_i e_beta,
    e_beta e_gamma = omega(beta, gamma) e_(beta+gamma), e_beta e_(-beta) = -h_beta.
    Form: (h_i, t_i) = 1, (e_beta, e_(-beta)) = 1.  All roots are isotropic and h_beta is
    central; beta and 2 beta are both roots."""
    elems = [(u, v) for u in range(p) for v in range(p) if (u, v) != (0, 0)]
    idx = {b: i + 4 for i, b in enumerate(elems)}
    h1, h2, t1, t2 = 0, 1, 2, 3
    n = len(elems) + 4
    mul = {}
    form = {(h1, t1): 1, (t1, h1): 1, (h2, t2): 1, (t2, h2): 1}
    for b in elems:
        i = idx[b]
        mul[(i, t1)] = {i: b[0]}
        mul[(t1, i)] = {i: -b[0]}
        mul[(i, t2)] = {i: b[1]}
        mul[(t2, i)] = {i: -b[1]}
        nb = ((-b[0]) % p, (-b[1]) % p)
        form[(i, idx[nb])] = 1
        for c in elems:
            j = idx[c]
            s = ((b[0] + c[0]) % p, (b[1] + c[1]) % p)
            if s == (0, 0):
                mul[(i, j)] = {h1: -b[0], h2: -b[1]}
            else:
                w = (b[0] * c[1] - b[1] * c[0]) % p
                if w:
                    mul[(i, j)] = {idx[s]: w}
    return VA("hamiltonian-like mod %d" % p, p, n, mul, [h1, h2, t1, t2], form)


def direct_sum(V1, V2):
    p = V1.p
    n1 = V1.n
    mul = dict(V1.mul)
    for (i, j), d in V2.mul.items():
        mul[(i + n1, j + n1)] = {k + n1: c for k, c in d.items()}
    form = dict(V1.form)
    for (i, j), c in V2.form.items():
        form[(i + n1, j + n1)] = c
    H = V1.H + [h + n1 for h in V2.H]
    return VA(V1.name + " + " + V2.name, p, n1 + V2.n, mul, H, form)


def rank_one_system(F, dims):
    """The Jacobi identity for a candidate of rank 1: dims is a dictionary root -> dimension
    (symmetric under i -> -i, roots elements of the field F), H = (h), (h, h) = 1,
    e_i h = i e_i, a pairing (e_i^s, e_(-i)^t) = delta_st; by invariance the products of
    root vectors are a totally antisymmetric tensor C on the triples with sum 0, and
    e_i^s e_(-i)^t = -delta_st i h.  Returns (ring, ideal generators)."""
    basis = [(i, s) for i, d in dims.items() for s in range(d)]
    order = {b: k for k, b in enumerate(basis)}
    triples = []
    for x, y, z in itertools.combinations(basis, 3):
        if x[0] + y[0] + z[0] == 0:
            triples.append((x, y, z))
    names = ["t%d" % k for k in range(len(triples))]
    if names:
        R = PolynomialRing(F, names, order="degrevlex")
        gens = R.gens()
    else:
        R = PolynomialRing(F, "t0")
        gens = ()
    val = {}
    for g, tr in zip(gens, triples):
        for perm, sign in (((0, 1, 2), 1), ((1, 2, 0), 1), ((2, 0, 1), 1), ((1, 0, 2), -1), ((0, 2, 1), -1), ((2, 1, 0), -1)):
            val[(tr[perm[0]], tr[perm[1]], tr[perm[2]])] = sign * g

    def partner(b):
        return (-b[0], b[1])

    def product(u, v):
        """u, v dictionaries basis -> polynomial; 'h' is the key of h."""
        out = {}
        for a, ca in u.items():
            for b, cb in v.items():
                c = ca * cb
                if a == "h" and b == "h":
                    continue
                if b == "h":
                    out[a] = out.get(a, R(0)) + c * a[0]
                elif a == "h":
                    out[b] = out.get(b, R(0)) - c * b[0]
                elif a[0] + b[0] == 0:
                    if a[1] == b[1]:
                        out["h"] = out.get("h", R(0)) - c * a[0]
                else:
                    for d in range(dims.get(a[0] + b[0], 0)):
                        target = (a[0] + b[0], d)
                        k = (a, b, partner(target))
                        if k in val:
                            out[target] = out.get(target, R(0)) + c * val[k]
        return {k: v for k, v in out.items() if v != 0}

    eqs = set()
    for x, y, z in itertools.combinations_with_replacement(basis, 3):
        ex, ey, ez = {x: R(1)}, {y: R(1)}, {z: R(1)}
        total = {}
        for d in (product(product(ex, ey), ez), product(product(ey, ez), ex), product(product(ez, ex), ey)):
            for k, v in d.items():
                total[k] = total.get(k, R(0)) + v
        for v in total.values():
            if v != 0:
                eqs.add(v)
    return R, list(eqs)


def rank_one_has_solution(F, dims):
    R, eqs = rank_one_system(F, dims)
    if not eqs:
        return True
    return R.ideal(eqs).groebner_basis() != [R(1)]


def section_8_rank_one():
    # Positive controls of the system below: the root set {+-i} is sl_2 with another unit
    for p in (5, 7):
        F = GF(p)
        for i in range(1, (p - 1) // 2 + 1):
            check(rank_one_has_solution(F, {F(i): 1, F(-i): 1}), "{+-i} is sl_2")
    # Theorem 88: root sets in GF(p), all root spaces one-dimensional
    for p in (5, 7, 11, 13):
        F = GF(p)
        halves = [F(i) for i in range(2, (p - 1) // 2 + 1)]
        for choice in itertools.product((0, 1), repeat=len(halves)):
            dims = {F(1): 1, F(-1): 1}
            for c, i in zip(choice, halves):
                if c:
                    dims[i] = 1
                    dims[-i] = 1
            sol = rank_one_has_solution(F, dims)
            if len(dims) == 2:
                check(sol, "sl_2 exists, p = %d" % p)
            else:
                refuted(sol, "rank 1, roots %s mod %d" % (sorted(int(k) for k in dims), p))
    # p = 5 with multiplicities: step (a), (g), (h), (i)
    F = GF(5)
    one, two = F(1), F(2)
    for d1, d2 in ((2, 0), (3, 0), (1, 1), (2, 1), (1, 2), (2, 2)):
        dims = {one: d1, -one: d1}
        if d2:
            dims[two] = d2
            dims[-two] = d2
        refuted(rank_one_has_solution(F, dims), "rank 1, p = 5, multiplicities %s" % ((d1, d2),))
    # step (j): a nonintegral line lambda + GF(p), lambda in GF(p^2)
    for p in (5, 7):
        K = GF(p**2, "z")
        z = K.gen()
        P = [K(i) for i in range(p)]
        lambdas = []
        seen = set()
        for c in range(1, p):
            lam = c * z
            if lam in seen:
                continue
            for i in P:
                seen.add(lam + i)
                seen.add(-lam + i)
            lambdas.append(lam)
        for lam in lambdas[:3 if p == 5 else 1]:
            dims = {K(1): 1, K(-1): 1}
            for i in P:
                dims[lam + i] = 1
                dims[-lam - i] = 1
            refuted(rank_one_has_solution(K, dims), "rank 1, a line through %s mod %d" % (lam, p))
    # arithmetic of steps (b), (c), (e), (j)
    for p in prime_range(5, 200):
        half = (p + 1) // 2
        for j in range(half, p - 1):
            bound = p - j + 2
            check(bound < p, "r < p, step (b): theorem 58 applies")
            for r in range(1, bound + 1):
                assert (r - (1 - 2 * j)) % p != 0, "(14)"
            # r = 2 p + 1 - 2 j lies in 5..p, against r <= p - j + 2
            r0 = 2 * p + 1 - 2 * j
            check(5 <= r0 <= p and (r0 - (1 - 2 * j)) % p == 0 and r0 > bound, "r = 2p + 1 - 2j, step (b)")
        # step (c): -1 = ((p + 1)/2) (-2)
        check((half * (-2) + 1) % p == 0, "step (c)")
        # step (e): 1 = 2 ((p+1)/2)
        check((2 * half - 1) % p == 0, "step (e)")
        # step (d): the range [(p+1)/2, p-3], its negatives, and 1, 2, p-2, p-1 cover 1..p-1
        cover = set(range(half, p - 2)) | {p - j for j in range(half, p - 2)} | {1, 2, p - 2, p - 1}
        check(cover == set(range(1, p)), "step (d)")
        # step (h): 1, 2, 4 are nonzero
        check(all(x % p for x in (1, 2, 4)), "step (h)")
    # step (j): (lambda - 1)/(lambda + 1) is not in GF(p) for lambda not in GF(p)
    for p in (5, 7, 11):
        K = GF(p**2, "z")
        P = {K(i) for i in range(p)}
        for lam in K:
            if lam in P:
                continue
            check((lam - 1) / (lam + 1) not in P, "step (j)")
    # "для всех i": from theorem 58 only i < p follows; a module with u A^p = 0, u A^(p-1) != 0,
    # u X = 0, u H = lambda u, lambda not in GF(p): printed "для всех i" does not follow.
    for p in (5, 7):
        K = GF(p**2, "z")
        lam = K.gen()
        A = matrix(K, p, p, sparse=True)
        X = matrix(K, p, p, sparse=True)
        H = matrix(K, p, p, sparse=True)
        for i in range(p):
            H[i, i] = lam + i
            if i + 1 < p:
                A[i, i + 1] = 1
            if i >= 1:
                X[i, i - 1] = K(i) * lam + K(ZZ(i * (i - 1)) // 2)
        check(A * H - H * A == A and X * H - H * X == -X and A * X - X * A == H)
        u = matrix(K, 1, p, [1] + [0] * (p - 1))
        check(u * X == 0 and u * H == lam * u)
        check(u * A ** (p - 1) != 0, "u A^i != 0 for i < p")
        refuted(u * A**p != 0, "printed: u A^i != 0 for all i does not follow")
    # step (f): x = 0 in L_-1, R_x is not injective when L_2 != 0: the map is 0
    W = witt(5)  # the algebra is not a V-algebra, the claim about R_0 is formal
    check(not W.R(np.zeros(5, dtype=np.int64)).any(), "R_0 = 0: step (f) needs x != 0")
    # exc in the rank 1 theorem: sl_2 is simple, three-dimensional
    for p in (5, 7, 11, 13):
        V = chevalley(("A", 1), p)
        check_axioms(V)
        check(V.n == 3 and len(V.Rset) == 2, "rank 1: two roots, dimension 3")


def section_8_examples():
    # the V-algebras: simple types
    simple = (
        [("A", n) for n in range(1, 9)]
        + [("B", n) for n in range(2, 9)]
        + [("C", n) for n in range(3, 9)]
        + [("D", n) for n in range(4, 9)]
        + [("E", 6), ("E", 7), ("E", 8), ("F", 4), ("G", 2)]
    )
    big = {("E", 7), ("E", 8), ("D", 8), ("B", 8), ("C", 8), ("A", 8)}
    seen_killing_zero = False
    for t in simple:
        primes = (5, 7) if t in big else (5, 7, 11, 13)
        for p in primes:
            if t[0] == "A" and (t[1] + 1) % p == 0:
                continue
            V = chevalley(t, p)
            dim = V.n
            check_axioms(V, jacobi=dim <= 52)
            iso, Z = check_exercises(V)
            check(Z == 0 and iso == [], "no center, nonisotropic, %s" % V.name)
            root_level(V)
            # the Killing form may vanish while the normalised form does not
            n, mul, H, form, ct, g = chevalley_data(t)
            if g % p == 0:
                seen_killing_zero = True
    check(seen_killing_zero, "some Killing form vanishes mod p: the form need not be Killing's")
    # A_n with p | n + 1: the form of the Chevalley basis is degenerate on H
    V = chevalley(("A", 4), 5)
    refuted(rank(V.G_H, 5) == 4, "sl_5 mod 5 is not a V-algebra with this form")
    # the same with psl_n (p | n)
    for n, p in ((5, 5), (7, 7)):
        V, keptm = psl_va(n, p)
        check_axioms(V, jacobi=(n == 5))
        iso, Z = check_exercises(V)
        check(Z == 0 and iso == [], "psl_n: no center, nonisotropic")
        check(V.n == n * n - 2 and len(V.H) == n - 2)
        root_level(V)
    # products
    for t, p in (((("A", 2), ("G", 2)), 5), ((("B", 2), ("A", 1)), 7), ((("A", 1), ("A", 1)), 5)):
        V = chevalley(t, p)
        check_axioms(V)
        iso, Z = check_exercises(V)
        check(Z == 0 and iso == [])
        root_level(V)
    # gl_n: center, nonisotropic roots; exc:matrices-p-divides-n
    for n, p in ((3, 5), (4, 5), (5, 5)):
        V = gl_va(n, p)
        check_axioms(V, jacobi=(n <= 4))
        iso, Z = check_exercises(V)
        check(Z == 1 and iso == [], "gl_n: center of dimension 1, nonisotropic roots")
        root_level(V)
    # isotropic roots
    for p in (5, 7):
        for k in (1, 2):
            V = oscillator(k, p)
            check_axioms(V)
            iso, Z = check_exercises(V)
            check(Z == 1 and len(iso) == 2 and len(V.Rset) == 2, "oscillator: one center, two isotropic roots")
            # the dimension of L_alpha is k: the nonisotropic hypothesis of th:nonisotropic-root is needed
            check(all(len(v) == k for v in V.roots.values()))
        V = hamiltonian_like(p)
        check_axioms(V, jacobi=(p == 5))
        iso, Z = check_exercises(V)
        check(Z == 2 and len(iso) == p * p - 1, "all roots isotropic, center of dimension 2")
        # proportional roots exist
        a = next(iter(V.Rset))
        check(tuple(2 * x % p for x in a) in V.Rset, "beta and 2 beta are roots: isotropic roots behave badly")
        # sl_2 + oscillator: both kinds of roots
        V = direct_sum(chevalley(("A", 1), p), oscillator(1, p))
        check_axioms(V)
        iso, Z = check_exercises(V)
        check(Z == 1 and len(iso) == 2 and len(V.Rset) == 4)


def add_tuples(u, v):
    return tuple(a + b for a, b in zip(u, v))


def section_8_steps():
    # theorem 90 (a): (15) on a module for the Heisenberg algebra: a x = h, h acts as b != 0,
    # a h = 0, u x = 0.
    for p in (5, 7, 11):
        A, X = A1(p), B1(p)
        H = (A @ X - X @ A) % p
        check((H == np.eye(p, dtype=np.int64)).all())
        b = 1
        u = np.zeros(p, dtype=np.int64)
        u[0] = 1
        check(not (u @ X % p).any())
        v = u
        for i in range(1, p):
            w = v @ A % p
            check(((w @ X) % p == (i * b * v) % p).all(), "(15) with i = %d" % i)
            v = w
        # since u A^(p-1) != 0 here, "beta - alpha" is a root in the sense of step (a)
        check((u @ matpow(A, p - 1, p) % p).any(), "u A^(p-1) != 0 for u != 0")
    # the inner products of steps (a)-(d) and of the end of the proof, symbolically: h = a h_alpha +
    # b h_beta, with (h_alpha, h_alpha) = 0, (h_alpha, h_beta) = x, (h_beta, h_beta) = y
    R = PolynomialRing(ZZ, "x,y,i,j")
    x, y, i, j = R.gens()

    def ip(u, v):
        return u[0] * v[1] * x + u[1] * v[0] * x + u[1] * v[1] * y

    al, be = (R(1), R(0)), (R(0), R(1))
    def comb(a, b):
        return (R(a), R(b))
    check(ip(al, comb(1, 1)) == x, "(b): (h_alpha, h_(alpha+beta)) = (h_alpha, h_beta)")
    check(ip(be, comb(2, 1)).subs(y=0) == 2 * x, "(b): 2 alpha + beta is not orthogonal to beta")
    check(ip(comb(1, 1), comb(1, 1)).subs(y=0) == 2 * x, "(b): (h_(alpha+beta), h_(alpha+beta)) = 2 x")
    check(ip(al, comb(1, -2)) == -2 * x, "(c): alpha - 2 beta is not orthogonal to alpha")
    check(ip(al, comb(1, -1)) == -x, "(c): alpha - beta is not orthogonal to alpha")
    # (c): applied to the root 2 alpha - 2 beta, (a) gives alpha - 2 beta and 3 alpha - 2 beta, not
    # alpha - beta: the sentence means (a) for beta and -(beta - alpha)
    check(add_tuples((2, -2), (-1, 0)) == (1, -2) and add_tuples((2, -2), (1, 0)) == (3, -2))
    gamma = comb(j, 1)
    check(ip(gamma, gamma).subs(x=i * y) == y * (1 + 2 * i * j), "(d)")
    delta_val = ip(be, comb(1, -1)).subs(x=i * y)
    check(delta_val == y * (i - 1), "the end: lambda = (h_delta, h_(alpha-delta))/(h_delta, h_delta) = i - 1")
    # theorem 90 (d): printed j = 1 - 2 i fails, corrected j = -1/(2 i)
    printed_count = {}
    for p in prime_range(5, 200):
        bad = 0
        for i in range(1, p):
            j = (-pow(2 * i, -1, p)) % p
            check(1 <= j <= p - 1 and (1 + 2 * i * j) % p == 0, "step (d), corrected")
            jp = (1 - 2 * i) % p
            if (1 + 2 * i * jp) % p == 0:
                bad += 1
        printed_count[p] = bad
    check(printed_count[5] == 1 and printed_count[7] == 0 and printed_count[11] == 2 and printed_count[13] == 0 and printed_count[17] == 0,
          "the printed j works for so few i")
    refuted((1 + 2 * 1 * ((1 - 2 * 1) % 5)) % 5 == 0, "printed j at p = 5, i = 1")
    # theorem 90, the end: lambda = -(r - 1)/2 for r <= 3 is an integer mod p; the proof uses r < p
    for p in (5, 7, 11):
        check(all(r % p for r in (1, 2, 3)), "r <= 3 is not divisible by p: theorem 58 applies")
    # theorem 94: printed "beta = +-alpha": in sl_2, beta = -alpha gives r = 2, and beta + alpha = 0 is
    # not a root; beta = alpha gives r = -2, and beta + alpha = 2 alpha is not a root.
    for p in (5, 7, 11, 13):
        V = chevalley(("A", 1), p)
        V.setup_h()
        a = next(iter(V.Rset))
        na = V.neg_wt(a)
        naa = V.ip(a, a)
        # beta = -alpha
        r = (-2 * V.ip(a, na) * pow(naa, -1, p)) % p
        check(r == 2 % p)
        check(V.add_wt(na, a, -1) not in V.Rset, "beta - alpha is not a root for beta = -alpha")
        refuted(V.add_wt(na, a) in V.Rset, "printed: beta + alpha is a root for beta = -alpha")
        # beta = alpha
        r = (-2 * V.ip(a, a) * pow(naa, -1, p)) % p
        check(r == (-2) % p)
        check(tuple(0 for _ in a) not in V.Rset, "beta - alpha = 0 is not a root for beta = alpha")
        if p == 5:
            # -2 = 3: then 2 alpha would have to be a root
            refuted(V.add_wt(a, a) in V.Rset, "printed, p = 5, beta = alpha")
        else:
            refuted(r in (0, 1, 2, 3), "printed, beta = alpha, r = -2")
    # theorem 95: the printed values mod p
    check({x % 5 for x in (0, 1, -1, 2, -2, 3, -3)} == set(range(5)), "p = 5: all residues")
    check({x % 7 for x in (0, 1, -1, 2, -2, 3, -3)} == set(range(7)), "p = 7: all residues")
    check(len({x % 11 for x in (0, 1, -1, 2, -2, 3, -3)}) == 7, "p = 11: 7 of 11 residues")
    # theorem 93: the verbatim argument of § 5.  s = r + 2 m mod p, s <= m + r, m + r <= 4.
    cases = {}
    for p in (5, 7, 11, 13):
        cases[p] = [
            (m, r, s)
            for m in range(1, 4)
            for r in range(1, 5)
            for s in range(1, 5)
            if m + r <= 4 and s <= m + r and (s - r - 2 * m) % p == 0
        ]
    check(cases[5] == [(2, 2, 1), (3, 1, 2)], "p = 5: two cases are left by the verbatim argument: %s" % cases[5])
    check(cases[7] == [] and cases[11] == [] and cases[13] == [], "no cases for p >= 7")
    # the recursion excludes them: for a string of length t = m + r the bottom has lambda = -(t-1)/2,
    # c_0 = lambda != 0; s = 1 would need c_0 = 0; s = 2 needs c_1 = 0.
    p = 5
    half = pow(2, -1, p)
    for (m, r, s), t in zip(cases[5], (4, 4)):
        lam = (-(t - 1) * half) % p
        c = [(i + 1) * (lam + i * half) % p for i in range(t)]
        check(c[t - 1] == 0 and all(c[i] != 0 for i in range(t - 1)), "the string products")
        check(c[s - 1] != 0, "s is not the length of the string from the bottom")


def section_8_exercises():
    # exc:four-dim-isotropic
    for p in (5, 7, 11, 13):
        V = oscillator(1, p)
        a, x, h, t = 0, 1, 2, 3
        check(V.mul[(a, x)] == {h: 1} and V.mul[(a, t)] == {a: 1} and V.mul[(x, t)] == {x: p - 1}, "the printed table")
        # the printed form (a, x) = (h, k) = 1
        pf = {(a, x): 1, (x, a): 1, (h, t): 1, (t, h): 1}
        violations = 0
        cf = dict(V.form)
        corrected_viol = 0
        for i, j, k in itertools.product(range(4), repeat=3):
            def left(F):
                return sum(c * F.get((m, k), 0) for m, c in V.mul.get((i, j), {}).items()) % p
            def right(F):
                return sum(c * F.get((i, m), 0) for m, c in V.mul.get((j, k), {}).items()) % p
            if left(pf) != right(pf):
                violations += 1
            if left(cf) != right(cf):
                corrected_viol += 1
        check(violations > 0, "the printed form is not invariant")
        refuted(violations == 0, "printed: (a, x) = (h, k) = 1")
        check(corrected_viol == 0, "(a, x) = -1, (h, k) = 1 is invariant")
        check(cf[(a, x)] == p - 1 and cf[(h, t)] == 1)
        # h_alpha = h: theorem 87
        check_axioms(V)
        al = V.wt[a]
        check(V.h[al] == (1, 0), "h_alpha = h")
        check(V.ip(al, al) == 0, "alpha is isotropic")
        # "только один корень": literally two
        refuted(len(V.Rset) == 1, "printed: only one root")
        check(len(V.Rset) == 2 and V.wt[x] == V.neg_wt(al), "two roots, alpha and -alpha; one up to sign")
        # exc:derived-algebra (e): printed refuted, L^2 has a, x, h, L^2 . L^2 has h
        der = {a, x, h}
        prods = set()
        for i, j in itertools.product(der, repeat=2):
            prods |= set(V.mul.get((i, j), {}))
        check(sparse_rank(list(V.mul.values()), p) == 3, "dim L^2 = 3")
        check(prods == {h}, "dim L^2 . L^2 = 1")
        refuted(prods == der, "printed part (e)")
    # part (e) with Z = 0 and also for gl_n (Z != 0, nonisotropic), chevalley examples
    for t, p in ((("A", 2), 5), (("G", 2), 5), (("B", 2), 7)):
        V = chevalley(t, p)
        rows = list(V.mul.values())
        check(sparse_rank(rows, p) == V.n, "L^2 = L, so L^2 . L^2 = L^2")
    V = gl_va(5, 5)
    # L^2 = sl_5: trace zero span
    der_rows = list(V.mul.values())
    check(sparse_rank(der_rows, 5) == 24 and center_dim(V) == 1)
    # exc:quotient-by-center: L/Z has no center, on the algebras with center
    def alg_of(V):
        C = np.zeros((V.n, V.n, V.n), dtype=np.int64)
        for (i, j), d in V.mul.items():
            for k, c in d.items():
                C[i, j, k] = c
        return Alg(C, V.p)

    for V in (oscillator(1, 5), oscillator(2, 5), hamiltonian_like(5), gl_va(3, 5), gl_va(5, 5), direct_sum(chevalley(("A", 1), 5), oscillator(1, 5))):
        L = alg_of(V)
        Z = L.center()
        check(Z.shape[0] >= 1)
        Zb = rref(Z, V.p)[0]
        drop = rref(Z, V.p)[1]
        Q, kept = quotient(L, list(Zb), drop)
        check(Q.center().shape[0] == 0, "exc:quotient-by-center, %s" % V.name)
    # exc:matrices-p-divides-n: gl_n, p | n: neither L^2 nor L/Z has a nondegenerate invariant form, L^2/Z has
    for n, p in ((5, 5),):
        mats = gl_basis(n)
        L = alg_from_mats(mats, p)
        check(L.center().shape[0] == 1)
        check(L.derived().shape[0] == n * n - 1, "L != L^2")
        # L^2 = M
        M, N, smats, co, kept = psl(n, p)
        forms_M = M.invariant_forms()
        # the scalar I is in the common radical of all forms on M
        for F in forms_M:
            check(not ((co @ F) % p).any(), "every invariant form on L^2 has Z in its radical")
        check(len(forms_M) == 1, "the only invariant form on L^2 is Tr(XY), up to a scalar")
        k = n * n
        A = np.array([m.reshape(k) for m in mats], dtype=np.int64).T
        I = np.eye(n, dtype=np.int64).reshape(k)
        cog = solve(A, I, p)
        drop = (n - 1) * n + (n - 1)
        Q, keptq = quotient(L, [cog], [drop])
        forms_Q = Q.invariant_forms()
        traces = np.array([trace(mats[i], p) for i in keptq], dtype=np.int64)
        Mz = nullspace(traces.reshape((1, -1)), p)
        for F in forms_Q:
            check(not ((Mz @ F) % p).any(), "every invariant form on L/Z has M/Z in its radical")
        forms_N = N.invariant_forms()
        check(len(forms_N) == 1 and rank(forms_N[0], p) == N.n, "L^2/Z has a nondegenerate form")
    # exc:infinite-matrices: finite windows.  A finitely supported x lies in gl_N; x commuting with
    # gl_(N+1) is scalar on N+1 indices, so 0 (its last diagonal entry is 0).  E_11 is outside L^2.
    for p in (5, 7):
        for N in (2, 3, 4, 5):
            mats = gl_basis(N + 1)
            L = alg_from_mats(mats, p)
            Z = L.center()
            check(Z.shape[0] == 1, "the centralizer of gl_(N+1) is the scalars")
            z = Z[0].reshape((N + 1, N + 1))
            check(z[N, N] != 0, "a nonzero scalar has a nonzero last entry, so finite support gives 0")
            # traces: products have trace 0, E_11 has trace 1
            check(all(trace((a @ b - b @ a) % p, p) == 0 for a in mats for b in mats))
            check(trace(E(N + 1, 0, 0), p) == 1, "L^2 != L")
            # form and roots: e_i - e_j distinct, nonzero; (h, h) = 2
            V = gl_va(N + 1, p)
            check(len(V.Rset) == (N + 1) * N, "distinct roots")
            check(rank(V.G_H, p) == N + 1, "the form on the diagonal is nondegenerate")
            V.setup_h()
            check(all(V.ip(a, a) == 2 for a in V.Rset), "(h_alpha, h_alpha) = 2")
            # exc:derived-algebra (d), (e) here, where Z = 0 and L^2 != L: L^2 = the matrices of
            # trace 0 (finite support).  L^2 . L^2 = L^2 on the window, for N + 1 >= 3.
            if N + 1 >= 3:
                s = sl_basis(N + 1)
                prods = [((a @ b - b @ a) % p).reshape(-1) for a in s for b in s]
                check(rank(np.array(prods, dtype=np.int64), p) == len(s), "L^2 . L^2 = L^2 on the window")
            # H* = the diagonal matrices of trace 0: the form is nondegenerate on H*, since a
            # nonzero h supported on 1..N pairs with E_ii - E_(N+1,N+1), and the roots stay distinct
            if N <= 3:
                for cs in itertools.product(range(p), repeat=N):
                    if not any(cs) or sum(cs) % p:
                        continue
                    i0 = next(i for i in range(N) if cs[i])
                    check(cs[i0] != 0, "(h, E_ii - E_(N+1,N+1)) = h_i != 0")
            basis_star = [tuple((1 if t == i else 0) - (1 if t == i + 1 else 0) for t in range(N + 1)) for i in range(N)]
            restr = set()
            for a in range(N + 1):
                for b in range(N + 1):
                    if a != b:
                        restr.add(tuple((h[a] - h[b]) % p for h in basis_star))
            check(len(restr) == (N + 1) * N and (0,) * N not in restr, "roots restricted to H* are distinct, nonzero")


def main():
    begin("section_7")
    section_7_derivations()
    section_7_restricted()
    section_7_p69()
    section_7_theorem_74()
    section_7_theorem_76()
    section_7_theorem_78()
    section_7_cartan()
    section_7_theorem_81()
    section_7_theorem_83()
    section_7_exercise()
    begin("section_8")
    section_8_rank_one()
    section_8_examples()
    section_8_steps()
    section_8_exercises()
    total = sum(SECTIONS.values())
    for name, n in SECTIONS.items():
        print("%s: %d checks" % (name, n))
    print("ok chapter-1d: %d checks" % total)


if __name__ == "__main__":
    main()
