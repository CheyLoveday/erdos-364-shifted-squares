from exact import *
G17_CERT = [-2, 17, 0, 204, 0, 714, 0, 1122, 0, 935, 0, 442, 0, 119, 0, 17, 0, 1]
U17_CERT = [-3, -2, -20, -4, -13, -1, 70, 0, 102, 0, 53, 0, 12, 0, 1]
A41 = [-1, -15, 2, 4, 8, 7, -8, -10, -3, 6, 7, 3, -1, -9,
       3, 7, 2, 3, -9, -6, 1, 8, 4, 1, -4, -6, 3, 7, 0, 2,
       -7, -4, 1, 6, -1, 0, -2, -5, 4, 5, -5]

D = dickson_polys(41)
g17 = g_poly(17)
g41 = g_poly(41)
print("g17 == certificate polynomial:", g17 == trim(G17_CERT))
print("len(A41) =", len(A41), " (need 41 for n=0..40)")
u41 = [0]
for k, c in enumerate(A41):
    u41 = padd(u41, pscale(D[k], c))
u41 = trim(u41)
print("u41 degree:", pdeg(u41), " (certificate expects 40)")
open("g41.txt", "w").write(repr(g41))
open("u41.txt", "w").write(repr(u41))
open("u17.txt", "w").write(repr(U17_CERT))

# Lucas bridge: D_p(2A) = 2 f_p(A) as polynomials in A
for p in (17, 41):
    f = lucas_real_polys(p)
    lhs = [peval([0], 0)]  # placeholder
    gp = g_poly(p)
    # substitute x -> 2A in g_p = D_p(x) - 2 (without the -2), compare with 2*f_p
    sub = [0]
    for k, c in enumerate(gp):
        sub = padd(sub, pscale([0, 2] , 0) if False else pscale(pshift([1], 0), 0))
    # cleaner: build D_p scaled: coefficient of A^k in D_p(2A) is (coefficient of x^k) * 2^k
    sub = [c * (2 ** k) for k, c in enumerate(gp)]
    rhs = pscale(f[p], 2)
    print(f"D_{p}(2A) == 2 f_{p}(A):", trim(sub) == trim(rhs), " deg", pdeg(f[p]))

# g_p(0) = -2, and evenness of the shape
print("g17 leading/const:", g17[-1], g17[0], " g41:", g41[-1], g41[0])
