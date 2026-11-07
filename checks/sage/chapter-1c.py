"""Exact checks of Chapter I, §§ 5-6 (printed pp. 51-67) of I. Kaplansky,
"Алгебры Ли и локально компактные группы" (Moscow: Mir, 1974).

Run from the project root: sage -python checks/sage/chapter-1c.py
(plain asserts; do not use -O).  The last line is "ok chapter-1c: N checks".
Pages are the printed pages; labels are those of content/01-05-*, 01-06-*.
Conventions of the book: operators act on the right, u R_x = u x; an algebra
product x y of a Lie algebra is the bracket [x, y]; a h = alpha(h) a for a in
L_alpha, so the book's L_alpha is the classical L_(-alpha); (x y, z) = (x, y z);
h_alpha is defined by (h_alpha, k) = alpha(k).  Expected values are the book's
statements, written as literals; a printed reading that is wrong stays as a
refuted check (`refuted`) beside the corrected one.

Coverage.  SIMPLE: all simple types up to rank 8: A_1..A_8, B_2..B_8, C_3..C_8,
D_4..D_8, E_6, E_7, E_8, F_4, G_2 (31 types).  REDUCIBLE: A1xA1, A1xA1xA1,
A2xG2, B2xA1, D4xA1, A2xA2.  Root systems are generated in the script by simple
reflections from the Gram matrix of Sage's ambient simple roots and compared
with Sage's list.  Lie algebras are Sage's Chevalley bases over QQ, with the
Killing form computed as an actual trace of R_x R_y.

section_5 (pp. 51-58): th:nonzero-root-element (needs characteristic 0: the
  Heisenberg algebra acting on F^p by the matrices of th:commutator-identity-
  perfect refutes it in characteristic p; the Jacobi defect of the candidate
  with beta(h) != 0, alpha(h) = 0 in characteristic 0);
  th:semisimple-root-element-zero (semisimplicity needed: the 4-dimensional
  algebra of exc:four-dim-isotropic over QQ); th:semisimple-root-spaces on every
  type, including the trace equation (-1 + sum i d_i) alpha(h) = 0 of its proof
  and the sign of p. 53 (printed -alpha(k)(x, y) refuted, alpha(k)(x, y)
  checked); the decomposition of pp. 53-54; beta(h_alpha) = alpha(h_beta) =
  (h_alpha, h_beta); th:root-product-formula on every pair +-alpha;
  th:root-inner-product-rational including (h, h) = sum beta(h)^2 and
  (h, h) = 1 / sum r(alpha, beta)^2; th:roots-span-cartan,
  th:killing-positive-definite, th:rational-form-dimension; th:sl2-triple-vector:
  eq:sl2-h-action, eq:sl2-x-action as identities over ZZ[lambda] in the free
  associative algebra on A, X, H modulo [AH] = A, [XH] = -X, [AX] = H, acting on
  u with uX = 0, uH = lambda u, for all i <= 24 (all i: Lean, SlTwoString), and
  on explicit modules over QQ, GF(p); the last statement for r <= 14, p in
  {2, 3, 5, 7, 11, 13}; "r not divisible by p" is needed (the modules of
  dimension p for every lambda in GF(p)); "u != 0" is needed (u = 0 refutes the
  printed "вектор"; "ненулевой вектор" is the corrected reading); p = 2: r odd
  and (r-1)/2 read as an integer; th:root-string-ratio with "u, a, x" on every
  ordered pair of roots of every type by actual powers of R_a; eq:string-r,
  eq:string-s and s = r + 2 m; th:root-spaces-product-equal on every pair;
  th:root-string on every pair, with the Killing form of the algebra; the
  vectors h_alpha form a C-system over QQ with the Killing form (p. 59).
section_6 (pp. 58-67): the axioms (1)-(5) on SIMPLE and REDUCIBLE and failures
  on non-examples; integrality for all pairs; th:cartan-integers,
  th:string-length (exact maxima per type); th:proportional-roots;
  th:reflection-invariance, i -> r - i on all maximal chains; angles and the
  table of p. 65 (cos^2 = k/4, exact); the plane: 30, 45, 60, 90 degrees between
  consecutive roots of G2, B2, A2, A1xA1; D-systems and well-embedding;
  th:well-embedded-exists: steps (1)-(5) of the proof for random lexicographic
  orders on every type; th:positive-root-minus-simple with "не принадлежащий
  Delta" for every well-embedded system used, the printed form refuted at every
  beta in Delta; the proof's inequality; th:isometry-extends: the positive roots
  rebuilt from the Gram matrix of Delta by the height induction of the proof
  (both directions of the chain length), and two realisations compared;
  th:well-embedded-conjugate: the reflection step for every eligible alpha_i,
  the count grows by exactly 1, the iteration ends in Delta;
  th:unique-decomposition, th:indecomposable-systems on REDUCIBLE and SIMPLE;
  th:classification-graphs: the printed graphs with the arrow of p. 66 (from the
  shorter root to the longer) against Sage's types for all ranks <= 8,
  the arrow reversed in B_n, C_n refuted for n >= 3, the modern arrow of Sage's
  diagrams is the opposite one; the remark on the ranks (B_1 = A_1, C_2 = B_2,
  D_3 = A_3, D_2 disconnected, no other coincidence); only B_n, C_n need the
  arrow; an exhaustive enumeration of all connected positive definite integral
  systems up to rank 8 gives exactly the printed list (the method is exhaustive
  for rank <= 8, not beyond); exc:root-in-well-embedded, exc:negative-d-system,
  exc:negative-well-embedded, exc:lexicographic-order on every type.

What this does NOT establish.  No general theorem is proved here: ranks above 8
are not covered and the theorems of §§ 5-6 for arbitrary semisimple L are not
derived.  Lie algebras are taken over QQ, so "rational multiple" in
th:nonzero-root-element is tested only through the identities behind it.  The
scripts do not show that the typeset text agrees with the printed book.
Lean files: SlTwoString (formulas (6), (7), last statement of theorem 58), CSystem
(theorems 62, 64, 65, 67 for an abstract C-system).
"""
from fractions import Fraction
import itertools
import random

from sage.all import (
    CartanType,
    DiGraph,
    GF,
    LieAlgebra,
    PolynomialRing,
    QQ,
    RootSystem,
    ZZ,
    cos,
    lcm,
    matrix,
    pi,
)

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
    """A printed reading (or a reading without a needed hypothesis) that fails."""
    assert not cond, msg
    SECTIONS[CURRENT] += 1


SIMPLE = (
    [("A", n) for n in range(1, 9)]
    + [("B", n) for n in range(2, 9)]
    + [("C", n) for n in range(3, 9)]
    + [("D", n) for n in range(4, 9)]
    + [("E", 6), ("E", 7), ("E", 8), ("F", 4), ("G", 2)]
)
REDUCIBLE = [
    (("A", 1), ("A", 1)),
    (("A", 1), ("A", 1), ("A", 1)),
    (("A", 2), ("G", 2)),
    (("B", 2), ("A", 1)),
    (("D", 4), ("A", 1)),
    (("A", 2), ("A", 2)),
]


def type_name(t):
    if isinstance(t[0], tuple):
        return "x".join(type_name(s) for s in t)
    return "%s%d" % t


def cartan(t):
    if isinstance(t[0], tuple):
        return CartanType([[s[0], s[1]] for s in t])
    return CartanType([t[0], t[1]])


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def add(x, y, c=1):
    return tuple(a + c * b for a, b in zip(x, y))


def neg(x):
    return tuple(-a for a in x)


def scale(c, x):
    return tuple(c * a for a in x)


class Roots:
    """A root system in coordinates of its simple roots, from a Gram matrix."""

    def __init__(self, name, gram):
        self.name = name
        self.G = gram
        self.n = len(gram)
        self.simple = [
            tuple(1 if i == j else 0 for j in range(self.n)) for i in range(self.n)
        ]
        self.roots = self._closure()
        self.Gv = {r: self.Gx(r) for r in self.roots}
        self.norm = {r: dot(r, self.Gv[r]) for r in self.roots}
        self.set = set(self.roots)

    def Gx(self, x):
        return tuple(dot(row, x) for row in self.G)

    def ip(self, x, y):
        return dot(x, self.Gx(y))

    def reflect(self, a, v):
        """The reflection of p. 60: v -> v - 2 (a, v) / (a, a) a; the quotient must
        be an integer here, as it is for roots (an assert fails otherwise)."""
        Ga = self.Gcache.get(a)
        if Ga is None:
            Ga = self.Gcache[a] = self.Gx(a)
        q, rem = divmod(2 * dot(Ga, v), dot(Ga, a))
        assert rem == 0
        return tuple(x - q * y for x, y in zip(v, a))

    def _closure(self):
        self.Gcache = {}
        seen = set(self.simple)
        todo = list(self.simple)
        while todo:
            v = todo.pop()
            for a in self.simple:
                w = self.reflect(a, v)
                if w not in seen:
                    seen.add(w)
                    todo.append(w)
        return sorted(seen)

    def positive(self):
        return [r for r in self.roots if all(c >= 0 for c in r)]


def gram_from_sage(t):
    ct = cartan(t)
    A = RootSystem(ct).ambient_space()
    I = ct.index_set()
    s = [A.simple_root(i) for i in I]
    G = [[QQ(a.inner_product(b)) for b in s] for a in s]
    d = lcm([x.denominator() for row in G for x in row])
    return [[int(x * d) for x in row] for row in G]


ROOTS = {}


def roots_of(t):
    if t not in ROOTS:
        R = Roots(type_name(t), gram_from_sage(t))
        ct = cartan(t)
        Q = RootSystem(ct).root_lattice()
        I = ct.index_set()
        sage_roots = {tuple(int(r.coefficient(i)) for i in I) for r in Q.roots()}
        assert sage_roots == R.set, t
        ROOTS[t] = R
    return ROOTS[t]


def c_axioms_failed(gamma, ip, rank_needed):
    """Which of the axioms (1)-(5) of pp. 58-59 fail for the finite set gamma."""
    gamma = set(gamma)
    failed = set()
    z = None
    for g in gamma:
        z = tuple(0 for _ in g)
        break
    if z in gamma:
        failed.add(0)
    if matrix(QQ, sorted(gamma)).rank() != rank_needed:
        failed.add(1)
    for a in gamma:
        if neg(a) not in gamma:
            failed.add(2)
        for m in list(range(2, 16)) + list(range(-15, -1)):
            if scale(m, a) in gamma:
                failed.add(3)
    for b in gamma:
        for a in gamma:
            if b == a or b == neg(a) or add(b, a, -1) in gamma:
                continue
            r = Fraction(-2 * ip(a, b), ip(a, a))
            if r.denominator != 1 or r < 0:
                failed.add(4)
                continue
            r = int(r)
            if any(add(b, a, i) not in gamma for i in range(1, r + 1)):
                failed.add(5)
            if add(b, a, r + 1) in gamma:
                failed.add(5)
    return failed


def is_positive_definite(M):
    """Sylvester's criterion by exact elimination; M a list of rows of Fractions."""
    n = len(M)
    A = [[Fraction(x) for x in row] for row in M]
    for i in range(n):
        if A[i][i] <= 0:
            return False
        for j in range(i + 1, n):
            f = A[j][i] / A[i][i]
            if f:
                for k in range(i, n):
                    A[j][k] -= f * A[i][k]
    return True


class Lie:
    """Sage's Chevalley basis over QQ, in the book's notation.  L[alpha] is the
    index of the basis element spanning the book's root space L_alpha; note that
    a h = alpha(h) a means that it is Sage's E[-alpha]."""

    def __init__(self, t):
        ct = cartan(t)
        self.R = roots_of(t)
        self.I = list(ct.index_set())
        A = LieAlgebra(QQ, cartan_type=ct)
        keys = list(A.basis().keys())
        self.dim = len(keys)
        idx = {k: i for i, k in enumerate(keys)}
        self.mul = {}
        for (x, y), v in A.structure_coefficients().items():
            d = {idx[k]: QQ(c) for k, c in v.monomial_coefficients().items()}
            self.mul[(idx[x], idx[y])] = d
            self.mul[(idx[y], idx[x])] = {k: -c for k, c in d.items()}
        self.L = {}
        self.H = [None] * len(self.I)
        for k, i in idx.items():
            coords = tuple(int(k.coefficient(j)) for j in self.I)
            if "check" in str(k):
                self.H[coords.index(1)] = i
            else:
                self.L[neg(coords)] = i
        # triples z R_x = sum c w, for traces
        self.R_of = [[] for _ in range(self.dim)]
        for (z, x), d in self.mul.items():
            for w, c in d.items():
                self.R_of[x].append((z, w, c))
        self.R_idx = [{} for _ in range(self.dim)]
        for x in range(self.dim):
            for z, w, c in self.R_of[x]:
                self.R_idx[x][(z, w)] = c

    def prod(self, u, v):
        out = {}
        for i, a in u.items():
            for j, b in v.items():
                for k, c in self.mul.get((i, j), {}).items():
                    out[k] = out.get(k, 0) + a * b * c
        return {k: c for k, c in out.items() if c}

    def killing(self, x, y):
        """Tr(R_x R_y) on basis elements."""
        return sum(c * self.R_idx[y].get((w, z), 0) for z, w, c in self.R_of[x])


def section_5_identities():
    # eq:sl2-h-action, eq:sl2-x-action in the free associative algebra on A, X, H
    # modulo the relations, acting on u: words are brought to H^a X^b A^c.
    Z = PolynomialRing(ZZ, "lam")
    lam = Z.gen()

    def normal(word, memo={}):
        if word in memo:
            return memo[word]
        for i in range(len(word) - 1):
            pair = word[i : i + 2]
            if pair == "AH":  # AH = HA + A
                res = dict(normal(word[:i] + "HA" + word[i + 2 :]))
                extra = normal(word[:i] + "A" + word[i + 2 :])
            elif pair == "XH":  # XH = HX - X
                res = dict(normal(word[:i] + "HX" + word[i + 2 :]))
                extra = {k: -v for k, v in normal(word[:i] + "X" + word[i + 2 :]).items()}
            elif pair == "AX":  # AX = XA + H
                res = dict(normal(word[:i] + "XA" + word[i + 2 :]))
                extra = normal(word[:i] + "H" + word[i + 2 :])
            else:
                continue
            for k, v in extra.items():
                res[k] = res.get(k, 0) + v
            res = {k: v for k, v in res.items() if v}
            memo[word] = res
            return res
        memo[word] = {word: 1}
        return memo[word]

    def act(word):
        """u . word, as a dictionary c -> coefficient of u A^c over ZZ[lam]."""
        out = {}
        for w, v in normal(word).items():
            a, b, c = w.count("H"), w.count("X"), w.count("A")
            assert w == "H" * a + "X" * b + "A" * c
            if b:
                continue  # u X = 0
            out[c] = out.get(c, Z(0)) + v * lam**a  # u H = lam u
        return {k: v for k, v in out.items() if v}

    for i in range(0, 25):
        e6 = act("A" * i + "H")
        check(e6 == ({i: lam + i} if lam + i else {}), "(6) at i=%d" % i)
        e7 = act("A" * i + "X")
        coeff = i * lam + ZZ(i * (i - 1)) / 2
        expected = {i - 1: Z(coeff)} if i >= 1 else {}
        check(e7 == expected, "(7) at i=%d" % i)
    # a printed-sign sanity: the coefficient with +1/2 i(i-1) is not -1/2 i(i-1)
    refuted(act("AAX") == {1: Z(2 * lam - 1)})

    # Explicit modules: row vectors v_i = u A^i, 0 <= i < r.
    def module(r, l, F):
        A = matrix(F, r, r, sparse=True)
        X = matrix(F, r, r, sparse=True)
        H = matrix(F, r, r, sparse=True)
        for i in range(r):
            H[i, i] = l + F(i)
            if i + 1 < r:
                A[i, i + 1] = 1
            if i >= 1:
                X[i, i - 1] = F(i) * l + F(ZZ(i * (i - 1)) / 2)
        return A, X, H

    def relations(A, X, H):
        return (
            A * H - H * A == A and X * H - H * X == -X and A * X - X * A == H
        )

    for r in range(1, 15):
        l = -QQ(r - 1) / 2
        A, X, H = module(r, l, QQ)
        check(relations(A, X, H), "module over QQ, r=%d" % r)
        # the last statement over QQ: another lambda does not give a module
        A2, X2, H2 = module(r, l + 1, QQ)
        refuted(relations(A2, X2, H2), "lambda must be -(r-1)/2")
    for p in (3, 5, 7, 11, 13):
        F = GF(p)
        for r in range(1, 15):
            if r % p == 0:
                continue
            l = -F(r - 1) / 2
            A, X, H = module(r, l, F)
            check(relations(A, X, H), "module mod %d, r=%d" % (p, r))
            for other in F:
                if other != l:
                    A2, X2, H2 = module(r, other, F)
                    refuted(relations(A2, X2, H2), "unique lambda mod p")
        # r = p: every lambda occurs, so "r not divisible by p" is needed
        for l in F:
            A, X, H = module(p, l, F)
            check(relations(A, X, H), "r = p, any lambda")
            v = [F(0)] * p
            v[0] = F(1)
            u = matrix(F, 1, p, v)
            check(u * X == 0 and u * H == l * u)
            check(u * A ** (p - 1) != 0 and u * A**p == 0)
    # p = 2: r odd, (r - 1)/2 is read as an integer, not through the residue of r
    F = GF(2)
    for r in range(1, 15, 2):
        l = F(-ZZ((r - 1) // 2))
        A, X, H = module(r, l, F)
        check(relations(A, X, H), "p = 2, r = %d" % r)
        A2, X2, H2 = module(r, l + 1, F)
        refuted(relations(A2, X2, H2))
    # r = 3, p = 2: reading r as the residue 1 would give lambda = 0; lambda = 1
    A, X, H = module(3, F(1), F)
    check(relations(A, X, H))
    A, X, H = module(3, F(0), F)
    refuted(relations(A, X, H))
    # r = 2, p = 2: rl + r(r-1)/2 = 1 != 0, r = 2 does not occur at all
    for l in F:
        A, X, H = module(2, l, F)
        refuted(relations(A, X, H))
    # "u != 0" is needed in the last statement: for u = 0 the least positive r
    # is 1, uX = 0 and uH = lambda u hold for every lambda, while -(r-1)/2 = 0.
    A, X, H = module(3, QQ(-1), QQ)
    u = matrix(QQ, 1, 3, [0, 0, 0])
    lam_any = QQ(5)
    check(u * X == 0 and u * H == lam_any * u and u * A == 0)
    refuted(lam_any == -QQ(1 - 1) / 2, "printed 'вектор' with u = 0 and r = 1")


def section_5_examples():
    # exc:four-dim-isotropic over QQ: a x = h, a k = a, x k = -x; h = a x satisfies
    # alpha(h) = 0, h != 0: "semisimple" cannot be dropped in
    # th:semisimple-root-element-zero.  The conclusion of th:nonzero-root-element
    # holds: the only roots are 0, +-alpha and they vanish on h.
    names = "a x h k".split()
    mul = {
        ("a", "x"): {"h": 1},
        ("a", "k"): {"a": 1},
        ("x", "k"): {"x": -1},
    }

    def bracket(u, v):
        if (u, v) in mul:
            return mul[(u, v)]
        if (v, u) in mul:
            return {k: -c for k, c in mul[(v, u)].items()}
        return {}

    def lin(d, v):
        out = {}
        for u, c in d.items():
            for w, e in bracket(u, v).items():
                out[w] = out.get(w, 0) + c * e
        return {k: c for k, c in out.items() if c}

    for x, y, z in itertools.product(names, repeat=3):
        t = {}
        for d in (lin(bracket(x, y), z), lin(bracket(y, z), x), lin(bracket(z, x), y)):
            for w, c in d.items():
                t[w] = t.get(w, 0) + c
        check(all(c == 0 for c in t.values()), "Jacobi, 4-dim algebra")
    h_acts_on_a = lin({"a": 1}, "h")
    check(h_acts_on_a == {} and bracket("a", "x") == {"h": 1})
    refuted(bracket("a", "x") == {}, "h = a x != 0 while alpha(h) = 0")

    # th:nonzero-root-element: a candidate a x = k, a k = x k = 0, u k = c u,
    # u a = u x = 0, where alpha(k) = 0 and beta(k) = c.  The Jacobi defect of
    # (u, a, x) is -c u, so c = 0: this is the trace argument in the smallest case.
    c = PolynomialRing(QQ, "c").gen()
    table = {("a", "x"): {"k": c.parent()(1)}, ("u", "k"): {"u": c}}

    def br(s, t):
        if (s, t) in table:
            return table[(s, t)]
        if (t, s) in table:
            return {w: -e for w, e in table[(t, s)].items()}
        return {}

    def br_lin(d, t):
        out = {}
        for s, e in d.items():
            for w, f in br(s, t).items():
                out[w] = out.get(w, 0) + e * f
        return out

    total = {}
    for d in (br_lin(br("u", "a"), "x"), br_lin(br("a", "x"), "u"), br_lin(br("x", "u"), "a")):
        for w, e in d.items():
            total[w] = total.get(w, 0) + e
    check(total == {"u": -c}, "the Jacobi identity forces beta(a x) = 0")

    # The theorem needs characteristic 0: over GF(p) the Heisenberg algebra a, x, z
    # with k acts on V = F^p by the matrices A_1, B_1, I, K of p. 71; in the
    # semidirect product L = (a, x, z, k) + V, H = (z, k), the elements a, x and the
    # rows v_i have roots +-alpha (alpha(k) = 1) and beta_i (beta_i(k) = i).  Here
    # h = a x = z, alpha(h) = 0, beta_i(h) = 1: no multiple of alpha(h).
    for p in (3, 5, 7):
        F = GF(p)
        A1 = matrix(F, p, p, sparse=True)
        B1 = matrix(F, p, p, sparse=True)
        K = matrix(F, p, p, sparse=True)
        for i in range(p):
            K[i, i] = i
            if i + 1 < p:
                A1[i, i + 1] = 1
                B1[i + 1, i] = i + 1
        I = matrix.identity(F, p, sparse=True)
        check(A1 * B1 - B1 * A1 == I, "a x = z acts as [A_1, B_1] = I")
        check(A1 * K - K * A1 == A1 and B1 * K - K * B1 == -B1, "a k = a, x k = -x")
        check(A1 * I - I * A1 == 0, "alpha(z) = 0: a z = 0")
        v = matrix(F, 1, p, [1] + [0] * (p - 1))
        check(v * I == v and F(1) != 0, "beta_0(z) = 1 != 0, not a multiple of alpha(z) = 0")


def section_5_algebra(t):
    L = Lie(t)
    R = L.R
    n = R.n
    # the decomposition of pp. 53-54: H abelian, root spaces one-dimensional, the
    # action of H, no multiples (th:semisimple-root-spaces)
    check(L.dim == n + len(R.roots), "dim L = rank + number of roots")
    for i in L.H:
        for j in L.H:
            check((i, j) not in L.mul, "H abelian")
    # alpha(h_i) from the actual product a h_i = alpha(h_i) a
    val = {}
    for a, ia in L.L.items():
        v = []
        for ih in L.H:
            d = L.mul.get((ia, ih), {})
            check(set(d) <= {ia}, "a h is a multiple of a")
            v.append(d.get(ia, QQ(0)))
        val[a] = tuple(v)
    for a in R.roots:
        check(val[neg(a)] == neg(val[a]), "(-alpha)(h) = -alpha(h)")
        for m in range(-8, 9):
            if m not in (-1, 0, 1):
                check(scale(m, a) not in R.set, "no multiples i alpha, i != 0, +-1")
    # linear functions: val is additive on the root lattice
    for i in R.simple:
        for j in R.simple:
            s = add(i, j)
            if s in R.set:
                check(val[s] == add(val[i], val[j]))
    # Killing form as a trace; L_alpha orthogonal to L_beta for beta != -alpha,
    # L_alpha orthogonal to H (th:root-spaces-orthogonal, used throughout)
    K = matrix(QQ, n, n, [L.killing(i, j) for i in L.H for j in L.H])
    check(K == K.transpose() and K.rank() == n, "form nondegenerate on H")
    for a, ia in L.L.items():
        for ih in L.H:
            check(L.killing(ia, ih) == 0, "(L_alpha, H) = 0")
    pos = R.positive()
    if len(R.roots) <= 112:
        for a, ia in L.L.items():
            for b, ib in L.L.items():
                if b != neg(a):
                    check(L.killing(ia, ib) == 0, "(L_alpha, L_beta) = 0")
    # Killing form on H as sum over the roots (p. 54)
    S = matrix(
        QQ,
        n,
        n,
        [sum(val[g][i] * val[g][j] for g in R.roots) for i in range(n) for j in range(n)],
    )
    check(S == K, "(h, k) = sum gamma(h) gamma(k)")
    Kinv = K.inverse()
    # h_alpha in the basis h_i
    h = {a: (Kinv * matrix(QQ, n, 1, list(val[a]))).list() for a in R.roots}

    def ipK(x, y):
        return sum(x[i] * K[i, j] * y[j] for i in range(n) for j in range(n))
    def evalf(a, x):
        return sum(val[a][i] * x[i] for i in range(n))
    hs = [h[s] for s in R.simple]
    gramK = [[ipK(a, b) for b in hs] for a in hs]
    # h_(alpha+beta) = h_alpha + h_beta on the lattice, so (h_a, h_b) is the form
    # with this Gram matrix on root coordinates
    def ipR(a, b):
        return sum(a[i] * gramK[i][j] * b[j] for i in range(n) for j in range(n))
    for a in R.roots:
        check(tuple(sum(c * x[i] for c, x in zip(a, hs)) for i in range(n)) == tuple(h[a]), "h linear")
    # beta(h_alpha) = alpha(h_beta) = (h_alpha, h_beta) on the simple roots and on
    # all pairs through linearity; all pairs for the small types
    sample = R.roots if len(R.roots) <= 72 else R.simple + pos[-3:]
    for a in sample:
        for b in sample:
            v = ipK(h[a], h[b])
            check(evalf(b, h[a]) == v and evalf(a, h[b]) == v, "beta(h_alpha) = alpha(h_beta)")
    # th:root-product-formula, th:root-inner-product-rational
    for a in R.roots:
        ia, ix = L.L[a], L.L[neg(a)]
        d = L.mul.get((ia, ix), {})
        kv = L.killing(ia, ix)
        check(kv != 0, "L_alpha, L_(-alpha) dual")
        hv = {L.H[i]: -kv * h[a][i] for i in range(n) if h[a][i]}
        check(d == hv, "x y = -(x, y) h_alpha")
        # the sign of p. 53: x in L_(-alpha), y in L_alpha, h = x y,
        # (h, k) = -(y, x k) = alpha(k) (x, y), printed -alpha(k)(x, y)
        x, y = ix, ia
        hxy = L.mul.get((x, y), {})
        for j, ih in enumerate(L.H):
            lhs = sum(c * L.killing(w, ih) for w, c in hxy.items())
            mid = -sum(c * L.killing(y, w) for w, c in L.mul.get((x, ih), {}).items())
            check(lhs == mid, "(x y, k) = -(y, x k)")
            right = val[a][j] * L.killing(x, y)
            check(lhs == right, "corrected sign, p. 53")
            if val[a][j]:
                refuted(lhs == -right, "printed sign, p. 53")
        hh = ipR(a, a)
        check(hh > 0, "(h_alpha, h_alpha) positive rational")
        rs = [ipR(a, b) / hh for b in R.roots]
        check(hh == 1 / sum(r**2 for r in rs), "(h, h) = 1 / sum r^2")
        # the trace equation of th:semisimple-root-spaces: V = x, H, L_alpha (the only
        # multiple); R_h has eigenvalues -alpha(h), 0, alpha(h), trace
        # (-1 + sum i d_i) alpha(h) = 0 with sum i d_i = 1
        ah = sum(val[a][j] * hxy.get(L.H[j], 0) for j in range(n))
        check(ah != 0, "alpha(h) != 0")
        tr = L.prod({x: QQ(1)}, hxy).get(x, 0) + L.prod({y: QQ(1)}, hxy).get(y, 0)
        tr += sum(L.prod({k: QQ(1)}, hxy).get(k, 0) for k in L.H)
        check(tr == 0 and L.prod({y: QQ(1)}, hxy).get(y, 0) == ah, "Tr(R_h | V) = 0")
    # th:roots-span-cartan, th:killing-positive-definite, th:rational-form-dimension
    check(matrix(QQ, [h[a] for a in R.roots]).rank() == n, "span of h_alpha is H")
    check(matrix(QQ, gramK).is_positive_definite(), "Killing form positive on H_0")
    check(matrix(QQ, [h[a] for a in R.simple]).rank() == n, "dim_Q H_0 = dim H")
    # Scale: the Killing form on roots is proportional to the ambient form (p. 59)
    c = Fraction(int(gramK[0][0].numerator()), int(gramK[0][0].denominator())) / R.G[0][0]
    if not isinstance(t[0], tuple):
        for i in range(n):
            for j in range(n):
                check(Fraction(int(gramK[i][j].numerator()), int(gramK[i][j].denominator())) == c * R.G[i][j])
    # th:root-string-ratio, th:root-spaces-product-equal: every ordered pair
    for a in R.roots:
        ia, ix = L.L[a], L.L[neg(a)]
        haa = ipR(a, a)
        # normalisation a x = h, A = R_a, X = R_x, H = R_h (p. 57)
        kv = L.killing(ia, ix)
        hn = tuple(c / haa for c in h[a])
        check(evalf(a, hn) == 1, "alpha(h) = 1 after the normalisation")
        for b in R.roots:
            iu = L.L[b]
            ux = L.mul.get((iu, ix), {})
            diff = add(b, a, -1)
            if diff in R.set:
                check(ux != {}, "L_beta L_(-alpha) = L_(beta-alpha), th:root-spaces-product-equal")
            if ux == {} and b != a:
                u = {iu: QQ(1)}
                r = 0
                v = u
                while v:
                    v = L.prod(v, {ia: QQ(1)})
                    r += 1
                check(r - 1 == -2 * ipR(a, b) / haa, "(8): r - 1 = -2 (h_a, h_b)/(h_a, h_a)")
            # th:root-spaces-product-equal directly
            s = add(a, b)
            if s in R.set:
                check(L.mul.get((ia, iu), {}) != {}, "L_a L_b = L_(a+b)")
            # (9): s = r + 2 m from h_gamma = h_beta - m h_alpha
            m = 0
            g = b
            while add(g, a, -1) in R.set:
                g = add(g, a, -1)
                m += 1
            sval = -2 * ipR(a, g) / haa + 1
            rval = -2 * ipR(a, b) / haa + 1
            check(sval == rval + 2 * m, "s = r + 2 m")
            # th:root-string with the form of the algebra (0 counted as a root)
            if diff not in R.set and b != a:
                rr = -2 * ipR(a, b) / haa
                check(rr in ZZ and rr >= 0, "th:root-string: r non-negative integer")
                rr = int(rr)
                seq = [add(b, a, i) for i in range(1, rr + 2)]
                zero = tuple(0 for _ in b)
                check(all(x in R.set or x == zero for x in seq[:-1]) and seq[-1] not in R.set)
    # p. 59: the h_alpha form a C-system over QQ with the Killing form.
    d = lcm([x.denominator() for row in gramK for x in row])
    Gint = [[int(x * d) for x in row] for row in gramK]
    Rk = Roots(R.name + "-killing", Gint)
    check(Rk.set == R.set)
    check(c_axioms_failed(R.roots, Rk.ip, n) == set(), "h_alpha form a C-system")


def section_5():
    begin("section_5")
    section_5_identities()
    section_5_examples()
    for t in SIMPLE:
        section_5_algebra(t)
    for t in REDUCIBLE:
        section_5_algebra(t)


def lex_simple(R, B):
    """Simple roots for the lexicographic order: v is positive when the first
    nonzero value of the functionals in B is positive."""

    def is_pos(v):
        for row in B:
            s = dot(row, v)
            if s:
                return s > 0
        raise AssertionError("B must be invertible")

    P = [r for r in R.roots if is_pos(r)]
    sums = set()
    for x, y in itertools.combinations_with_replacement(P, 2):
        sums.add(add(x, y))
    return [r for r in P if r not in sums], P


def coordinates_in(Delta):
    """A function v -> the coordinates of v (simple coordinates) in the basis Delta,
    as Fractions."""
    M = matrix(QQ, Delta).inverse()
    d = int(M.denominator())
    rows = [[int(x * d) for x in M.column(j)] for j in range(M.ncols())]
    return lambda v: tuple(Fraction(dot(col, v), d) for col in rows)


def well_embedded(R, Delta):
    co = coordinates_in(Delta)
    for r in R.roots:
        c = co(r)
        if any(x.denominator != 1 for x in c):
            return False
        if not (all(x >= 0 for x in c) or all(x <= 0 for x in c)):
            return False
    return True


def is_d_system(R, Delta):
    if matrix(QQ, Delta).rank() != len(Delta) or len(Delta) != R.n:
        return False
    for a in Delta:
        for b in Delta:
            if a != b:
                r = Fraction(-2 * R.ip(a, b), R.ip(a, a))
                if r.denominator != 1 or r < 0:
                    return False
    return True


def positive_wrt(R, Delta):
    co = coordinates_in(Delta)
    P = {}
    for r in R.roots:
        c = co(r)
        assert all(x.denominator == 1 for x in c)
        if all(x >= 0 for x in c):
            P[r] = [int(x) for x in c]
    return P


def rebuild_from_gram(G):
    """th:isometry-extends: the positive roots, in coordinates of Delta, from the
    Gram matrix of Delta alone, by the height induction of the proof: gamma of
    height h + 1 is a root iff gamma = delta + alpha_i, where going down from delta
    in steps of alpha_i to the bottom epsilon, m steps, one has
    -2 (alpha_i, epsilon) / (alpha_i, alpha_i) >= m + 1."""
    n = len(G)
    def ip(x, y):
        return sum(x[i] * G[i][j] * y[j] for i in range(n) for j in range(n))
    e = [tuple(1 if i == j else 0 for j in range(n)) for i in range(n)]
    known = set(e)
    level = list(e)
    while level:
        new = set()
        for d in level:
            for i, a in enumerate(e):
                if d == a:
                    continue
                m = 0
                eps = d
                while add(eps, a, -1) in known:
                    eps = add(eps, a, -1)
                    m += 1
                q = Fraction(-2 * ip(a, eps), ip(a, a))
                assert q.denominator == 1 and q >= 0
                if q >= m + 1:
                    new.add(add(d, a))
        known |= new
        level = sorted(new)
    return known


def printed_graph(name, n):
    """The graphs of th:classification-graphs (p. 66), as printed.  Arcs carry
    -2 (u, v) / (u, u); an arrow runs from u (shorter) to v (longer), so that
    the arc u -> v has label 2 and v -> u has label 1 (the convention of p. 66)."""
    arcs = []

    def single(u, v):
        arcs.extend([(u, v, 1), (v, u, 1)])

    def arrow(u, v):
        arcs.extend([(u, v, 2), (v, u, 1)])

    if name == "A":
        for i in range(n - 1):
            single(i, i + 1)
    elif name == "B":  # the arrow runs from the end vertex to the chain
        for i in range(1, n - 1):
            single(i, i + 1)
        arrow(0, 1)
    elif name == "C":  # the arrow runs from the chain to the end vertex
        for i in range(1, n - 1):
            single(i, i + 1)
        arrow(1, 0)
    elif name == "D":  # a fork at the first vertex of the chain
        for i in range(2, n - 1):
            single(i, i + 1)
        single(0, 2)
        single(1, 2)
    elif name == "G":
        arcs.extend([(0, 1, 3), (1, 0, 1)])
    elif name == "F":
        single(0, 1)
        arrow(1, 2)
        single(2, 3)
    elif name == "E":  # a chain of n - 1 with one more vertex below the third
        for i in range(n - 2):
            single(i, i + 1)
        single(2, n - 1)
    D = DiGraph(multiedges=False, loops=False)
    D.add_vertices(range(n))
    D.add_edges(arcs)
    return D


def graph_of(G):
    n = len(G)
    D = DiGraph(multiedges=False, loops=False)
    D.add_vertices(range(n))
    for i in range(n):
        for j in range(n):
            if i != j and G[i][j]:
                q = Fraction(-2 * G[i][j], G[i][i])
                assert q.denominator == 1 and q > 0
                D.add_edge(i, j, int(q))
    return D


def reversed_arrows(D):
    """All arrows of double edges reversed."""
    E = D.copy()
    for u, v, l in D.edges(sort=False):
        if l == 2:
            E.delete_edge(u, v)
            E.delete_edge(v, u)
    for u, v, l in D.edges(sort=False):
        if l == 2:
            E.add_edge(v, u, 2)
            E.add_edge(u, v, 1)
    return E


PRINTED_RANGES = {"A": 1, "B": 2, "C": 3, "D": 4}


def printed_list(rank):
    out = []
    for name in "ABCD":
        if rank >= PRINTED_RANGES[name]:
            out.append((name, rank))
    if rank == 2:
        out.append(("G", 2))
    if rank == 4:
        out.append(("F", 4))
    if rank in (6, 7, 8):
        out.append(("E", rank))
    return out


def enumerate_systems(max_rank):
    """All connected Gram matrices of D-systems up to a common scalar, up to rank
    max_rank.  A connected graph has a vertex whose removal leaves it connected,
    so each system of rank m + 1 arises from one of rank m by adding a vertex; the
    new row runs through all values allowed by the integrality of
    -2 (u, v)/(u, u), -2 (u, v)/(v, v), pruned by the positive definiteness of
    the principal submatrix found so far.  Exhaustive for these ranks."""
    levels = {1: [[[Fraction(2)]]]}
    for m in range(1, max_rank):
        found = []
        graphs = []
        for G in levels[m]:
            lengths = {G[i][i] for i in range(m)}
            candidates = set()
            for d in lengths:
                for q in (Fraction(1), Fraction(2), Fraction(3), Fraction(1, 2), Fraction(1, 3)):
                    candidates.add(d * q)
            for L in candidates:
                rows = [[]]
                for i in range(m):
                    d = G[i][i]
                    options = [Fraction(0)]
                    for k in (1, 2, 3):
                        # k = -2 (u, v)/(u, u); then -2 (u, v)/(v, v) = k d / L
                        other = k * d / L
                        if other.denominator == 1:
                            options.append(-k * d / 2)
                    nxt = []
                    for row in rows:
                        for o in options:
                            cand = row + [o]
                            sub = [
                                [G[a][b] for b in range(i + 1)] + [cand[a]]
                                for a in range(i + 1)
                            ] + [cand + [L]]
                            if is_positive_definite(sub):
                                nxt.append(cand)
                    rows = nxt
                for row in rows:
                    if not any(row):
                        continue
                    new = [G[a] + [row[a]] for a in range(m)] + [row + [L]]
                    D = graph_of(new)
                    if not any(D.is_isomorphic(E, edge_labels=True) for E in graphs):
                        graphs.append(D)
                        found.append(new)
        levels[m + 1] = found
    return levels


def section_6():
    begin("section_6")
    all_types = SIMPLE + REDUCIBLE
    rng = random.Random(0)
    # Axioms (1)-(5)
    for t in all_types:
        R = roots_of(t)
        check(c_axioms_failed(R.roots, R.ip, R.n) == set(), "C-system %s" % R.name)
    # non-examples: each axiom does something
    def plain_ip(x, y):
        return dot(x, y)
    bc2 = [(1, 0), (-1, 0), (0, 1), (0, -1), (2, 0), (-2, 0), (0, 2), (0, -2),
           (1, 1), (1, -1), (-1, 1), (-1, -1)]
    check(3 in c_axioms_failed(bc2, plain_ip, 2), "BC_2 violates (3)")
    check(1 in c_axioms_failed([(1, 0), (-1, 0)], plain_ip, 2), "(1): must span")
    check(2 in c_axioms_failed([(1, 0), (0, 1), (0, -1)], plain_ip, 2), "(2)")
    a2_gram = [[2, -1], [-1, 2]]
    def a2_ip(x, y):
        return sum(x[i] * a2_gram[i][j] * y[j] for i in range(2) for j in range(2))
    check(5 in c_axioms_failed([(1, 0), (-1, 0), (0, 1), (0, -1)], a2_ip, 2), "(5): A2 without a+b")
    g = [[2, -1], [-1, 3]]
    def g_ip(x, y):
        return sum(x[i] * g[i][j] * y[j] for i in range(2) for j in range(2))
    check(4 in c_axioms_failed([(1, 0), (-1, 0), (0, 1), (0, -1)], g_ip, 2), "(4)")
    # The smallest system, used for th:positive-root-minus-simple
    check(c_axioms_failed([(1,), (-1,)], plain_ip, 1) == set())

    # Pairs: integrality, th:cartan-integers, th:string-length, th:proportional-roots
    value_union = set()
    for t in all_types:
        R = roots_of(t)
        values = set()
        kvals = set()
        run_max = 0
        for a in R.roots:
            na = R.norm[a]
            Ga = R.Gv[a]
            for b in R.roots:
                v = dot(Ga, b)
                q = Fraction(2 * v, na)
                check(q.denominator == 1, "2(a,b)/(a,a) integer") if len(R.roots) <= 72 else None
                assert q.denominator == 1
                values.add(int(q))
                k = Fraction(4 * v * v, na * R.norm[b])
                assert k.denominator == 1
                if b == a or b == neg(a):
                    assert k == 4
                else:
                    assert k in (0, 1, 2, 3), "k < 4 unless beta = +-alpha"
                    kvals.add(int(k))
                    # no other proportional roots, th:proportional-roots
                    assert v * v != na * R.norm[b]
                run = 0
                x = b
                while True:
                    x = add(x, a)
                    if x in R.set:
                        run += 1
                    else:
                        break
                run_max = max(run_max, run)
        check(values <= {0, 1, -1, 2, -2, 3, -3}, "th:cartan-integers %s" % R.name)
        value_union |= values
        check(run_max <= 3, "th:string-length %s" % R.name)
        names = {s[0] for s in t} if isinstance(t[0], tuple) else {t[0]}
        if "G" in names:
            check(run_max == 3 and 3 in values and 3 in kvals)
        else:
            check(3 not in values and 3 not in kvals)
            if names & {"B", "C", "F"}:
                check(run_max == 2 and 2 in kvals)
            else:
                # A_1 and its products have no strings at all
                orthogonal = all(s == ("A", 1) for s in t) if isinstance(t[0], tuple) else t == ("A", 1)
                check(run_max == (0 if orthogonal else 1) and 2 not in kvals)
        check(kvals <= {0, 1, 2, 3})
    check(value_union == {0, 1, -1, 2, -2, 3, -3}, "the printed list is attained")
    # th:proportional-roots, the proof: 2c and 2/c integers gives |c| = 1, 1/2, 2
    cs = {Fraction(n, 2) for n in range(-16, 17) if n
          if (Fraction(2) / Fraction(n, 2)).denominator == 1}
    check(cs == {Fraction(s * c, d) for s in (1, -1) for c, d in ((1, 1), (1, 2), (2, 1))})

    # th:reflection-invariance, and i -> r - i on the maximal chains (p. 60)
    for t in all_types:
        R = roots_of(t)
        invariant = True
        chains = True
        for a in R.roots:
            for b in R.roots:
                w = R.reflect(a, b)
                invariant = invariant and w in R.set
            for b in R.roots:
                if b == a or b == neg(a) or add(b, a, -1) in R.set:
                    continue
                r = Fraction(-2 * R.ip(a, b), R.norm[a])
                assert r.denominator == 1
                r = int(r)
                for i in range(r + 1):
                    w = R.reflect(a, add(b, a, i))
                    chains = chains and tuple(int(c) for c in w) == add(b, a, r - i)
        check(invariant, "th:reflection-invariance %s" % R.name)
        check(chains, "beta + i alpha -> beta + (r - i) alpha, %s" % R.name)
        # beta = +-alpha is outside the formula r = -2(a,b)/(a,a), axiom (2) covers it
        a = R.roots[0]
        check(Fraction(-2 * R.ip(a, a), R.norm[a]) == -2, "r = -2 at beta = alpha")
        check(R.reflect(a, a) == neg(a) and neg(a) in R.set)

    # Angles (pp. 60, 65).  The table: the angle between elements of a D-system is
    # obtuse or right, (angle: lines) = 90: 0, 120: 1, 135: 2, 150: 3, k = 4 cos^2;
    # the acute angles of p. 60: 30, 45, 60, 90 for k = 3, 2, 1, 0.
    for angle, lines in ((90, 0), (120, 1), (135, 2), (150, 3)):
        check(bool(4 * cos(pi * angle / 180) ** 2 == lines), "table of p. 65")
        check(lines == 0 or bool(cos(pi * angle / 180) < 0), "obtuse")
    for angle, lines in ((30, 3), (45, 2), (60, 1), (90, 0)):
        check(bool(4 * cos(pi * angle / 180) ** 2 == lines), "acute angles of p. 60")
    for t in all_types:
        R = roots_of(t)
        for i, a in enumerate(R.simple):
            for j, b in enumerate(R.simple):
                if i < j:
                    k = Fraction(4 * R.ip(a, b) ** 2, R.ip(a, a) * R.ip(b, b))
                    check(k in (0, 1, 2, 3) and R.ip(a, b) <= 0, "simple pair: table of p. 65")
    # Two dimensions (p. 60)
    expected = {("G", 2): (3, 12), ("B", 2): (2, 8), ("A", 2): (1, 6), (("A", 1), ("A", 1)): (0, 4)}
    for t, (k_min, count) in expected.items():
        R = roots_of(t)
        check(len(R.roots) == count, "number of vectors = 360 / angle")
        for a in R.roots:
            best = None
            nearest = 0
            for b in R.roots:
                if b == a:
                    continue
                v = R.ip(a, b)
                if v < 0:
                    continue
                k = Fraction(4 * v * v, R.norm[a] * R.norm[b])
                if best is None or k > best:
                    best, nearest = k, 1
                elif k == best:
                    nearest += 1
            check(best == k_min and nearest == 2, "angle between consecutive vectors")

    # th:well-embedded-exists: random lexicographic orders; th:positive-root-minus-
    # simple, for all well-embedded systems met.
    def verify_delta(R, Delta):
        check(is_d_system(R, Delta), "D-system")
        check(well_embedded(R, Delta), "well embedded")
        for a in Delta:
            for b in Delta:
                if a != b:
                    check(add(a, b, -1) not in R.set, "step (1)")
        P = positive_wrt(R, Delta)
        check(len(P) * 2 == len(R.roots), "half the roots are positive")
        good = True
        for b, c in P.items():
            if b in Delta:
                # the printed form fails at every element of Delta
                refuted(any(add(b, a, -1) in R.set for a in Delta), "th:positive-root-minus-simple, printed, beta in Delta")
            else:
                # the corrected form, and the elements outside Delta decompose in P
                good = good and any(add(b, a, -1) in P for a in Delta)
                # the proof: (beta, alpha_i) <= 0 if beta - alpha_i is not a root
                total = 0
                for ci, a in zip(c, Delta):
                    v = R.ip(b, a)
                    if add(b, a, -1) not in R.set:
                        good = good and v <= 0
                    total += ci * v
                good = good and total == R.ip(b, b) and total > 0
        check(good, "corrected th:positive-root-minus-simple and its proof, %s" % R.name)
        return P

    for t in all_types:
        R = roots_of(t)
        verify_delta(R, R.simple)
        check(lex_simple(R, R.simple)[0] == sorted(R.simple) or set(lex_simple(R, R.simple)[0]) == set(R.simple),
              "exc:lexicographic-order, the standard Delta")
        trials = 6 if len(R.roots) <= 128 else 3
        for _ in range(trials):
            while True:
                B = [[rng.randint(-9, 9) for _ in range(R.n)] for _ in range(R.n)]
                if matrix(QQ, B).rank() == R.n:
                    break
            Delta, Pos = lex_simple(R, B)
            check(len(Delta) == R.n, "step (5): simple roots are independent, as many as rank")
            verify_delta(R, Delta)
            # positive with respect to Delta = positive in the order, step (3)
            check(set(positive_wrt(R, Delta)) == set(Pos), "step (3)")
            # exc:lexicographic-order for this Delta: the ordered basis Delta itself
            M = matrix(QQ, Delta).inverse()
            cols = [list(M.column(i)) for i in range(R.n)]
            d = lcm([x.denominator() for c in cols for x in c])
            Bl = [[int(x * d) for x in c] for c in cols]
            check(set(lex_simple(R, Bl)[0]) == set(Delta), "exc:lexicographic-order")
            # exc:negative-*: -Delta
            minus = [neg(a) for a in Delta]
            check(is_d_system(R, minus) and well_embedded(R, minus), "exc:negative-d-system, exc:negative-well-embedded")
            # th:isometry-extends: the Gram matrix of Delta determines Gamma
            G = [[R.ip(a, b) for b in Delta] for a in Delta]
            rebuilt = rebuild_from_gram(G)
            check(rebuilt == {tuple(c) for c in positive_wrt(R, Delta).values()}, "th:isometry-extends")
            # th:well-embedded-conjugate: every eligible reflection adds exactly one
            P = set(positive_wrt(R, R.simple))
            D1 = list(Delta)
            P1 = set(positive_wrt(R, D1))
            steps = 0
            while P1 != P:
                inter = P1 & P
                eligible = [a for a in R.simple if a not in P1]
                check(eligible, "P != P_1 gives alpha_i outside P_1")
                for a in eligible:
                    S = lambda v: R.reflect(a, v)
                    P1S = {S(v) for v in P1}
                    check(a in P1S and S(neg(a)) == a, "S carries -alpha_i to alpha_i")
                    image = {S(v) for v in inter}
                    check(image <= P1S & P, "beta S stays in P")
                    check(a not in image, "alpha_i is new")
                    check(len(P1S & P) == len(inter) + 1, "the count grows by exactly 1")
                a = rng.choice(eligible)
                S = lambda v: R.reflect(a, v)
                D1 = [S(v) for v in D1]
                P1 = {S(v) for v in P1}
                steps += 1
            check(set(D1) == set(R.simple), "P = P_1 gives Delta = Delta_1")
            check(steps == len(R.positive()) - len(set(Pos) & P), "steps = |P minus P_1|")
        # th:isometry-extends for Delta = the standard one and Sage's ambient vectors
        if not isinstance(t[0], tuple):
            ct = cartan(t)
            A = RootSystem(ct).ambient_space()
            I = ct.index_set()
            s = [A.simple_root(i) for i in I]
            images = {
                tuple(sum(c * x[j] for c, x in zip(r, [v.to_vector() for v in s])) for j in range(len(s[0].to_vector())))
                for r in R.roots
            }
            ambient = {tuple(v.to_vector()) for v in A.roots()}
            check(images == ambient, "two realisations of the same Delta")

    # Theorem 67, smallest counterexample of the printed form, by hand
    gamma = {(1,), (-1,)}
    check((1,) in gamma and add((1,), (1,), -1) not in gamma)
    refuted(add((1,), (1,), -1) in gamma, "Gamma = {+-alpha}, beta = alpha")

    # Decompositions: th:unique-decomposition, th:indecomposable-systems
    def components(items, ip):
        items = list(items)
        comp = {x: i for i, x in enumerate(items)}
        changed = True
        while changed:
            changed = False
            for x in items:
                for y in items:
                    if ip(x, y) != 0 and comp[x] != comp[y]:
                        m = min(comp[x], comp[y])
                        old = max(comp[x], comp[y])
                        for z in items:
                            if comp[z] == old:
                                comp[z] = m
                        changed = True
        out = {}
        for x in items:
            out.setdefault(comp[x], []).append(x)
        return list(out.values())

    for t in all_types:
        R = roots_of(t)
        k = len(t) if isinstance(t[0], tuple) else 1
        comps_g = components(R.roots, R.ip)
        comps_d = components(R.simple, R.ip)
        check(len(comps_g) == k and len(comps_d) == k, "numbers of components")
        spans = []
        for c in comps_g:
            rank = matrix(QQ, c).rank()
            check(c_axioms_failed(c, R.ip, rank) == set(), "each part is a C-system")
            spans.append(rank)
        check(sum(spans) == R.n, "orthogonal decomposition of V")
        # the components of Gamma restrict to the components of Delta
        check(sorted(len([a for a in c if a in R.simple]) for c in comps_g) == sorted(len(c) for c in comps_d))
        for c in comps_g:
            members = {a for a in c if a in R.simple}
            check(any(set(d) == members for d in comps_d))

    # th:classification-graphs: the printed graphs against Sage's types
    for t in SIMPLE:
        name, n = t
        R = roots_of(t)
        G = R.G
        D = graph_of(G)
        check(D.is_isomorphic(printed_graph(name, n), edge_labels=True), "graph %s%d, arrow of p. 66" % t)
        check(D.num_verts() == n, "the index is the number of vertices")
        # the number of lines is the printed k
        for i in range(n):
            for j in range(i + 1, n):
                k = Fraction(4 * G[i][j] ** 2, G[i][i] * G[j][j])
                check(k.denominator == 1 and int(k) in (0, 1, 2, 3))
                if k == 2:
                    # one length is twice the other; the arrow from shorter to longer
                    check(G[i][i] == 2 * G[j][j] or G[j][j] == 2 * G[i][i])
    for n in range(3, 9):
        B = printed_graph("B", n)
        C = printed_graph("C", n)
        check(reversed_arrows(B).is_isomorphic(C, edge_labels=True), "B_n and C_n differ by the arrow")
        refuted(B.is_isomorphic(C, edge_labels=True), "B_n != C_n")
        refuted(graph_of(roots_of(("B", n)).G).is_isomorphic(reversed_arrows(B), edge_labels=True),
                "arrow from the longer to the shorter does not match type B")
        refuted(graph_of(roots_of(("C", n)).G).is_isomorphic(reversed_arrows(C), edge_labels=True),
                "arrow from the longer to the shorter does not match type C")
        # In B_n the end root is short, in C_n long
        RB, RC = roots_of(("B", n)), roots_of(("C", n))
        check(sum(1 for r in RB.roots if RB.norm[r] == min(RB.norm.values())) == 2 * n, "B_n: 2n short roots")
        check(sum(1 for r in RC.roots if RC.norm[r] == max(RC.norm.values())) == 2 * n, "C_n: 2n long roots")
        # Sage draws the modern arrow, towards the shorter root: the opposite one
        check("=>=" in CartanType(["B", n]).ascii_art() and "=<=" in CartanType(["C", n]).ascii_art())
    # F_4, G_2, B_2: symmetry makes the lengths irrelevant (p. 66)
    F = printed_graph("F", 4)
    check(reversed_arrows(F).is_isomorphic(F, edge_labels=True), "F_4: arrow irrelevant")
    G2 = printed_graph("G", 2)
    swapped = DiGraph([(0, 1, 1), (1, 0, 3)], multiedges=False)
    check(swapped.is_isomorphic(G2, edge_labels=True), "G_2: lengths irrelevant")
    # The remark on the ranks p. 66-67: limits avoid duplication
    check(printed_graph("B", 2).is_isomorphic(printed_graph("C", 2), edge_labels=True), "C_2 = B_2")
    check(printed_graph("A", 3).is_isomorphic(printed_graph("D", 3), edge_labels=True), "D_3 = A_3")
    B1 = DiGraph(multiedges=False)
    B1.add_vertex(0)
    check(B1.is_isomorphic(printed_graph("A", 1), edge_labels=True), "B_1 has one vertex = A_1")
    d2 = DiGraph(multiedges=False)
    d2.add_vertices([0, 1])
    check(not d2.is_connected(), "D_2 would be A_1 x A_1")
    # In these limits no coincidences up to rank 8
    for rank in range(1, 9):
        L = printed_list(rank)
        for x, y in itertools.combinations(L, 2):
            refuted(printed_graph(*x).is_isomorphic(printed_graph(*y), edge_labels=True), "no duplicates")
    # Only B_n, C_n need the arrow: forgetting arrows merges only those
    def underlying(D):
        E = DiGraph(multiedges=False)
        E.add_vertices(D.vertices(sort=True))
        for u, v, l in D.edges(sort=False):
            E.add_edge(u, v, max(l, D.edge_label(v, u)))
        return E
    for rank in range(1, 9):
        L = printed_list(rank)
        for x, y in itertools.combinations(L, 2):
            same = underlying(printed_graph(*x)).is_isomorphic(underlying(printed_graph(*y)), edge_labels=True)
            check(same == ({x[0], y[0]} == {"B", "C"}), "arrows matter only for B_n, C_n")
    # Exhaustive enumeration up to rank 8: exactly the printed list
    levels = enumerate_systems(8)
    counts = {m: len(levels[m]) for m in levels}
    check(counts == {1: 1, 2: 3, 3: 3, 4: 5, 5: 4, 6: 5, 7: 5, 8: 5}, "numbers of connected systems: %s" % counts)
    for rank, grams in levels.items():
        L = printed_list(rank)
        check(len(L) == len(grams))
        for G in grams:
            D = graph_of(G)
            check(sum(1 for x in L if D.is_isomorphic(printed_graph(*x), edge_labels=True)) == 1, "the graph is printed")
    # The levels (a), (b), (c) of p. 67: all the printed systems exist
    for t in SIMPLE:
        R = roots_of(t)
        check(matrix(QQ, R.G).is_positive_definite(), "(a) D-system exists")
        check(LieAlgebra(QQ, cartan_type=cartan(t)).dimension() == R.n + len(R.roots), "(c)")
    # exc:root-in-well-embedded: each root lies in w(Delta), with w a product of
    # reflections, and w(Delta) is well embedded (coordinates by applying w^-1)
    for t in all_types:
        R = roots_of(t)
        good = True
        for a in R.roots:
            word = []
            v = a
            # a descent to a simple root
            pos_simple = set(R.simple)
            while v not in pos_simple:
                if all(c <= 0 for c in v):
                    # a negative root goes up; -alpha_i goes to alpha_i
                    s = next(x for x in R.simple if R.ip(x, v) < 0)
                else:
                    s = next(x for x in R.simple if R.ip(x, v) > 0)
                v = R.reflect(s, v)
                word.append(s)

            # a = s_1 ... s_k (v); w = s_1 ... s_k; w^-1 = s_k ... s_1, as a matrix
            def inv(u):
                for s in word:
                    u = R.reflect(s, u)
                return u

            W = [inv(e) for e in R.simple]
            for g in R.roots:
                c = [sum(g[i] * W[i][j] for i in range(R.n)) for j in range(R.n)]
                good = good and (all(x >= 0 for x in c) or all(x <= 0 for x in c))
            good = good and inv(a) in pos_simple
        check(good, "exc:root-in-well-embedded %s" % R.name)


def main():
    section_5()
    section_6()
    total = sum(SECTIONS.values())
    for name, n in SECTIONS.items():
        print("%s: %d checks" % (name, n))
    print("ok chapter-1c: %d checks" % total)


if __name__ == "__main__":
    main()
