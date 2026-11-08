from sympy import symbols, Poly, ZZ, Rational, factorint, isprime, resultant, discriminant, GF, factor_list, jacobi_symbol as J

T, A = symbols('T A')

def D(n):
    a, b = 2, T
    if n == 0: return Poly(2, T)
    if n == 1: return Poly(T, T)
    for _ in range(n-1):
        a, b = b, Poly(T,T)*b + a
    return Poly(b, T)

def F(n):
    # 2F_n = D_n(2A)
    return D(n).as_expr().subs(T, 2*A).expand()/2

def g(p):
    return Poly(D(p).as_expr() - 2, T)

def U17():
    expr = (-1 - D(2).as_expr() + D(3).as_expr() + D(4).as_expr()
            - D(5).as_expr() - 2*D(12).as_expr() + D(14).as_expr())
    return Poly(expr, T)

c41 = [-1,-15,2,4,8,7,-8,-10,-3,6,7,3,-1,-9,3,7,2,3,-9,-6,1,8,4,1,-4,-6,3,7,0,2,-7,-4,1,6,-1,0,-2,-5,4,5,-5]
def U41():
    expr = c41[0]
    for k in range(1,41):
        expr += c41[k]*D(k).as_expr()
    return Poly(expr, T)
