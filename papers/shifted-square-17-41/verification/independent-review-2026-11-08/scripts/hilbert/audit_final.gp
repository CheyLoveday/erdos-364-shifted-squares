\\ Final pass: mod-2 factorisation, Prop 2.1 scan, phase-2 reference characters.
Dp(n) = { my(d0=2, d1=T, d2); if(n==0, return(2)); for(k=2, n, d2 = T*d1 + d0; d0 = d1; d1 = d2); d1; }
C41 = [-1,-15,2,4,8,7,-8, -10,-3,6,7,3,-1,-9, 3,7,2,3,-9,-6,1, 8,4,1,-4,-6,3,7, 0,2,-7,-4,1,6,-1, 0,-2,-5,4,5,-5];
U17p = -1 - Dp(2) + Dp(3) + Dp(4) - Dp(5) - 2*Dp(12) + Dp(14);
U41p = C41[1] + sum(k=1, 40, C41[k+1]*Dp(k));
Uof(p) = if(p == 17, U17p, U41p);
F(A, n) = { my(f0=1, f1=A, f2); if(n==0, return(1)); for(k=2, n, f2 = 2*A*f1 + f0; f0 = f1; f1 = f2); f1; }

mod2fac() = { my(g, fm); for(i = 1, 2, my(q = if(i==1, 17, 41)); g = Dp(q) - 2; fm = factormod(g, 2);
  print("  p=", q, "  [deg, mult] = ", [[poldegree(fm[j,1]), fm[j,2]] | j <- [1..matsize(fm)[1]]]); ); }

prop21scan() = { my(ok = 1, cnt = 0, bad = 0, A, n, Q, sq);
  for(A = 2, 34, if(A % 4 == 2, forstep(n = 1, 19, 2, Q = F(A,n) - 1; cnt++;
      sq = ((A % 8 == 2 && n % 4 == 1) || (A % 8 == 6 && n % 4 == 3));
      if((Q % 8 == 1) != sq, bad++; print("  MISMATCH A=", A, " n=", n, "  Q mod 8 = ", Q % 8)); )));
  print("  ", cnt, " cases scanned, mismatches = ", bad); }

phase2() = { my(g, Q12, f, W, q);
  for(i = 1, 2, q = if(i==1, 17, 41); g = Dp(q) - 2; Q12 = subst(g, T, 12)/2; f = factor(Q12); W = 12*subst(Uof(q), T, 12);
    print("  p=", q, "  Q12 = ", Q12);
    for(j = 1, matsize(f)[1],
      print("    ell=", f[j,1], "  isprime=", isprime(f[j,1]), "  exp=", f[j,2], "  (12*U_p(12)/ell)=", kronecker(W, f[j,1])); );
    print("    J(12*U_p(12),Q12) = ", kronecker(W, Q12), "   J(U_p(12),Q12) = ", kronecker(subst(Uof(q),T,12), Q12)); ); }

print("=== mod-2 factorisation (Dedekind-Kummer input) ==="); mod2fac();
print("=== Proposition 2.1 mod-8 scan (A = 2 mod 4, n odd) ==="); prop21scan();
print("  2-adic square spot checks: issquare(5+O(2^20))=", issquare(5 + O(2^20)),
      " issquare(17+O(2^20))=", issquare(17 + O(2^20)), " issquare(9+O(2^20))=", issquare(9 + O(2^20)));
print("  F_3(2)-1=", F(2,3)-1, " 2-adic square? ", issquare(F(2,3)-1 + O(2^20)),
      "   F_5(2)-1=", F(2,5)-1, " 2-adic square? ", issquare(F(2,5)-1 + O(2^20)));
print("=== phase-2 reference characters at x = 12 (A = 6) ==="); phase2();
