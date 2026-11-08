"""Self-contained exact arithmetic kit (no CAS): Z[x] polys ascending, GF(p) factoring,
Jacobi/Kronecker symbols, resultants, modular discriminant + CRT, Dedekind's criterion."""
from math import gcd

# ---------- Z[x], ascending coefficient lists, no trailing zeros ----------
def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a

def padd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])

def psub(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)])

def pmul(a, b):
    if a == [0] or b == [0]:
        return [0]
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    out[i + j] += x * y
    return trim(out)

def pscale(a, c):
    return trim([x * c for x in a])

def pshift(a, k):          # multiply by x^k
    return trim([0] * k + list(a))

def peval(a, v):
    r = 0
    for c in reversed(a):
        r = r * v + c
    return r

def pdeg(a):
    a = trim(a)
    return -1 if a == [0] else len(a) - 1

def pcontent(a):
    c = 0
    for x in a:
        c = gcd(c, abs(x))
    return c

# ---------- Dickson / Lucas polynomials ----------
def dickson_polys(N):
    """D_0 = 2, D_1 = T, D_{n+2} = T*D_{n+1} + D_n  (as polys in T)."""
    D = [[2], [0, 1]]
    for n in range(2, N + 1):
        D.append(padd(pshift(D[n - 1], 1), D[n - 2]))
    return D

def lucas_real_polys(p):
    """f_0 = 1, f_1 = A, f_{n+2} = 2A f_{n+1} + f_n (as polys in A).
    Claim (paper): D_p(2A) = 2 f_p(A)."""
    f = [[1], [0, 1]]
    for n in range(2, p + 1):
        f.append(padd(pshift(pscale(f[n - 1], 2), 1), f[n - 2]))
    return f

def g_poly(p):
    return psub(dickson_polys(p)[p], [2])

# ---------- Jacobi / Kronecker / Legendre ----------
def jacobi(a, n):
    """Jacobi symbol (a/n) for n odd positive; n==1 -> 1."""
    assert n > 0 and n % 2 == 1
    a %= n
    result = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a %= n
    return result if n == 1 else 0

def kronecker(a, n):
    """Kronecker symbol (a/n) for arbitrary nonzero n (incl. n<0, even)."""
    if n == 0:
        return 1 if a in (1, -1) else 0
    if n < 0:
        s = -1 if a < 0 else 1
        return s * kronecker(a, -n)
    res = 1
    e = 0
    while n % 2 == 0:
        n //= 2
        e += 1
    if e:
        if a % 2 == 0:
            return 0
        if e % 2 == 1 and a % 8 in (3, 5):
            res = -res
    return res * jacobi(a, n) if n > 1 else res

# ---------- GF(p)[x] ----------
def gtrim(a, p):
    a = [c % p for c in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a

def gdivmod(a, b, p):
    a = gtrim(a, p); b = gtrim(b, p)
    inv = pow(b[-1], p - 2, p)
    q = [0] * max(1, len(a) - len(b) + 1)
    r = list(a)
    db = len(b) - 1
    for i in range(len(a) - 1, db - 1, -1):
        c = r[i] * inv % p
        q[i - db] = c
        if c:
            for j in range(db + 1):
                r[i - db + j] = (r[i - db + j] - c * b[j]) % p
    return gtrim(q, p), gtrim(r, p)

def gmul(a, b, p):
    return gtrim([0] * (len(a) + len(b) - 1) if False else
                 [sum(a[i] * b[j] for i in range(len(a)) for j in range(len(b)) if i + j == k)
                  for k in range(len(a) + len(b) - 1)], p)

def ggcd(a, b, p):
    a = gtrim(a, p); b = gtrim(b, p)
    while b != [0]:
        _, r = gdivmod(a, b, p)
        a, b = b, r
    a = gtrim(a, p)
    if a != [0] and a[-1] != 1:
        inv = pow(a[-1], p - 2, p)
        a = gtrim([c * inv % p for c in a], p)
    return a

def gderiv(a, p):
    return gtrim([(i * a[i]) % p for i in range(1, len(a))], p) if len(a) > 1 else [0]

def gpowmod(a, e, f, p):
    r = [1]
    a = gdivmod(a, f, p)[1]
    while e:
        if e & 1:
            r = gdivmod(gmul(r, a, p), f, p)[1]
        a = gdivmod(gmul(a, a, p), f, p)[1]
        e >>= 1
    return r

def _split_poly(f, d, p, seed):
    """Split f (a product of >=2 distinct irreducibles, each of degree exactly d) over F_p."""
    import random
    f = gtrim(f, p); n = len(f) - 1
    if n == d:
        return [f]
    rnd = random.Random(seed)
    for _attempt in range(400):
        cand = gtrim([rnd.randrange(p) for _ in range(n)] + [1], p)
        if p == 2:
            h = [0]; cur = gdivmod(cand, f, p)[1]
            for _i in range(d):
                m = max(len(h), len(cur))
                h = gtrim([(h[k] if k < len(h) else 0) + (cur[k] if k < len(cur) else 0)
                           for k in range(m)], p)
                cur = gdivmod(gmul(cur, cur, p), f, p)[1]
            cands = [h, gtrim([(h[k] + (1 if k == 0 else 0)) % p for k in range(len(h))], p)]
        else:
            h = gpowmod(cand, (p ** d - 1) // 2, f, p)
            cands = [h, gtrim([(h[k] - (1 if k == 0 else 0)) % p for k in range(len(h))], p)]
        # exponent for CZ must be (p^d-1)/2 (d = common degree) for odd p
        for base in cands:
            g0 = ggcd(f, base, p); dd = len(g0) - 1
            if 0 < dd < n:
                q, _ = gdivmod(f, g0, p)
                return _split_poly(g0, d, p, seed + 1) + _split_poly(q, d, p, seed + 2)
    raise RuntimeError("split failed p=%d n=%d d=%d" % (p, n, d))

def factor_fp(f, p):
    """Distinct irreducible factors of f over F_p (list of monic polys)."""
    f = gtrim(f, p)
    res = []
    if len(f) - 1 <= 0:
        return res
    d = 1
    g = f
    xp = [0, 1]
    while len(g) - 1 >= 2 * d:
        xp = gpowmod(xp, p, g, p)
        # h = xp - x  (distinct-degree test for degree d)
        m = max(len(xp), 2)
        h = gtrim([(xp[i] if i < len(xp) else 0) - (1 if i == 1 else 0) for i in range(m)], p)
        hh = ggcd(g, h, p)
        if len(hh) - 1 > 0:
            res += _split_poly(hh, d, p, 1000 * p + d)
            g, _ = gdivmod(g, hh, p)
            if len(g) - 1 > 0:
                xp = gdivmod(xp, g, p)[1]
        d += 1
    if len(g) - 1 > 0:
        res.append(g)
    return res

# ---------- resultant over F_p ----------
def resultant_mod(a, b, p):
    a = gtrim(a, p); b = gtrim(b, p)
    if a == [0] or b == [0]:
        return 0
    da, db = len(a) - 1, len(b) - 1
    if da == 0 and db == 0:
        return 1
    res = 1
    while db > 0:
        r = gdivmod(a, b, p)[1]
        dr = len(r) - 1
        if (da * db) % 2:
            res = (-res) % p
        res = res * pow(b[-1], da - dr, p) % p
        a, b = b, r
        da, db = db, dr
        if db < 0:
            return 0
    res = res * pow(b[0], da, p) % p
    return res % p

def derivative_z(a):
    return psub([(i) * a[i] for i in range(1, len(a))], []) if len(a) > 1 else [0]

def disc_mod(a, p):
    n = pdeg(a)
    r = resultant_mod(a, derivative_z(a), p)
    if (n * (n - 1) // 2) % 2:
        r = (-r) % p
    return r % p

# ---------- prime sieve ----------
def primes_upto(N):
    s = bytearray([1]) * (N + 1)
    s[0] = s[1] = 0
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(N + 1) if s[i]]

def is_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True

if __name__ == "__main__":
    D = dickson_polys(41)
    print("D_17 =", D[17])
    print("g17 == cert?", psub(D[17], [2])[1:] == [17, 0, 204, 0, 714, 0, 1122, 0, 935, 0, 442, 0, 119, 0, 17, 0])

# ---------- distinct factorization with multiplicities over F_p ----------
def _pth_root(f, p):
    """If f = w^p then return w (all exponents divisible by p)."""
    out = [0] * ((len(f) - 1) // p + 1)
    for k in range(0, len(f), p):
        out[k // p] = pow(f[k], pow(p, -1, p - 1) if p > 2 else 1, p) if False else _pinv_pow(f[k], p)
    return gtrim(out, p)

def _pinv_pow(a, p):
    # a^(1/p) in F_p ; for p=2 it is a itself; general: a^(p^{k}) ... use Fermat: a^(1/p)=a^(p^(f-1))
    # simplest: brute force for small p
    if p == 2:
        return a % 2
    for x in range(p):
        if pow(x, p, p) == a % p:
            return x
    raise ValueError("no p-th root")

def squarefree_part(f, p):
    """Product of the distinct monic irreducible factors of f over F_p."""
    f = gtrim(f, p)
    u = f
    rad = [1]
    while len(u) - 1 > 0:
        up = gderiv(u, p)
        if up == [0]:
            u = _pth_root(u, p)
            continue
        d = ggcd(u, up, p)
        w = gdivmod(u, d, p)[0]
        w = gtrim(w, p)
        rad = gmul(rad, w, p)
        while True:
            hh = ggcd(u, w, p)
            if len(gtrim(hh, p)) - 1 == 0:
                break
            u = gdivmod(u, hh, p)[0]
            u = gtrim(u, p)
    return gtrim(rad, p)

def factor_with_mult(f, p):
    """f over F_p; returns ([(irreducible h, multiplicity m)], rebuild_ok)."""
    f = gtrim(f, p)
    rad = squarefree_part(f, p)
    roots = factor_fp(rad, p)
    out = []
    for h in roots:
        h = gtrim(h, p)
        m = 0
        cur = f
        while True:
            q, r = gdivmod(cur, h, p)
            if r != [0] or len(cur) < len(h):
                break
            m += 1
            cur = q
        out.append((h, m))
    prod = [1]
    for (h, m) in out:
        prod = gmul(prod, _gpow(h, m, p), p)
    return out, gtrim(prod, p) == f

def dedekind_index_free(g, q):
    """(q does not divide [O_K:Z[theta]], detail=[(deg,mult)], rebuild_ok)."""
    gq = gtrim([c % q for c in g], q)
    fac, ok = factor_with_mult(gq, q)
    if all(m == 1 for (_h, m) in fac):
        # separable reduction: p does not divide disc(g), hence not the index
        return True, sorted([(len(h) - 1, m) for (h, m) in fac]), ok
    Qbar = [1]; Ubar = [1]
    for (h, m) in fac:
        Qbar = gmul(Qbar, h, q)
        Ubar = gmul(Ubar, _gpow(h, m - 1, q), q)
    assert gtrim(Qbar, q) == gtrim([c for c in Qbar], q)
    Q = trim(list(Qbar)); U = trim(list(Ubar))
    num = psub(g, pmul(Q, U))
    assert all(c % q == 0 for c in num), "lift failure"
    H = trim([c // q for c in num])
    d = ggcd(gtrim(list(Qbar), q), gtrim([c % q for c in H], q), q)
    return (len(d) - 1 == 0), sorted([(len(h) - 1, m) for (h, m) in fac]), ok

def _gpow(h, m, p):
    r = [1]
    for _ in range(m):
        r = gmul(r, h, p)
    return r
