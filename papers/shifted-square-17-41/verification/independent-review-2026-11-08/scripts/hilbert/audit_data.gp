\\ Independent audit data for the shifted-square Hilbert chain (p=17,41).
\\ Run: gp -q audit_data.gp
Dp(n) = { my(d0=2, d1=T, d2); if(n==0, return(2)); for(k=2, n, d2 = T*d1 + d0; d0 = d1; d1 = d2); d1; }

g17 = Dp(17) - 2;
g41 = Dp(41) - 2;
print("g17(4)      = ", subst(g17, T, 4));
print("g41(4)      = ", subst(g41, T, 4));
print("g17(2)      = ", subst(g17, T, 2));
print("g41(2)      = ", subst(g41, T, 2));
print("poldisc g17 = ", factor(poldisc(g17)));
print("poldisc g41 = ", factor(poldisc(g41)));
print("H17 = g17(4)/2 factored: ", factor(subst(g17, T, 4)/2));
print("H41 = g41(4)/2 factored: ", factor(subst(g41, T, 4)/2));

U17 = -1 - Dp(2) + Dp(3) + Dp(4) - Dp(5) - 2*Dp(12) + Dp(14);
print("deg U17     = ", poldegree(U17));
print("Res(g17,U17)= ", polresultant(g17, U17));
print("U17(4)      = ", subst(U17, T, 4));

C = [-1,-15,2,4,8,7,-8, -10,-3,6,7,3,-1,-9, 3,7,2,3,-9,-6,1, 8,4,1,-4,-6,3,7, 0,2,-7,-4,1,6,-1, 0,-2,-5,4,5,-5];
U41 = C[1] + sum(k=1, 40, C[k+1]*Dp(k));
print("deg U41     = ", poldegree(U41));
print("Res(g41,U41)= ", polresultant(g41, U41));
print("U41(4)      = ", subst(U41, T, 4));
print("U41(2)      = ", subst(U41, T, 2));

H17 = subst(g17, T, 4)/2;
H41 = subst(g41, T, 4)/2;
f17 = factor(H17); f41 = factor(H41);
print("H17 primes: ", f17~);
print("H41 primes: ", f41~);
print("Legendre chars at reference, p=17:");
for(i=1, matsize(f17)[1], ell = f17[i,1]; print("  ell=", ell, "  isprime=", isprime(ell), "  exp=", f17[i,2], "  (4U17(4)/ell)=", kronecker(4*subst(U17,T,4), ell)));
print("Legendre chars at reference, p=41:");
for(i=1, matsize(f41)[1], ell = f41[i,1]; print("  ell=", ell, "  isprime=", isprime(ell), "  exp=", f41[i,2], "  (4U41(4)/ell)=", kronecker(4*subst(U41,T,4), ell)));
print("J(4U17(4),H17) = ", prod(i=1, matsize(f17)[1], kronecker(4*subst(U17,T,4), f17[i,1])^f17[i,2]));
print("J(4U41(4),H41) = ", prod(i=1, matsize(f41)[1], kronecker(4*subst(U41,T,4), f41[i,1])^f41[i,2]));
