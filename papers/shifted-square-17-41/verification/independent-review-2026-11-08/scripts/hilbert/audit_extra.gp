\\ Extra checks: phase-2 rigorous-support data, huge-x identities, Theorem 1.3 valuation.
Dp(n) = { my(d0=2, d1=T, d2); if(n==0, return(2)); for(k=2, n, d2 = T*d1 + d0; d0 = d1; d1 = d2); d1; }
C41 = [-1,-15,2,4,8,7,-8, -10,-3,6,7,3,-1,-9, 3,7,2,3,-9,-6,1, 8,4,1,-4,-6,3,7, 0,2,-7,-4,1,6,-1, 0,-2,-5,4,5,-5];
U17p = -1 - Dp(2) + Dp(3) + Dp(4) - Dp(5) - 2*Dp(12) + Dp(14);
U41p = C41[1] + sum(k=1, 40, C41[k+1]*Dp(k));
Uof(p) = if(p == 17, U17p, U41p);
F(A, n) = { my(f0=1, f1=A, f2); if(n==0, return(1)); for(k=2, n, f2 = 2*A*f1 + f0; f0 = f1; f1 = f2); f1; }
vprod(v) = { my(s=1); for(i=1, #v, s *= v[i]); s; }

phase2support() = { my(g, nf, t, b, u, prs, refs, A, x, dx, sg, Q, J);
  for(i = 1, 2, my(p = if(i==1, 17, 41)); g = Dp(p) - 2; nf = nfinit(g, 1); t = Mod(T, g); u = subst(Uof(p), T, t); b = t*u;
    prs = idealprimedec(nf, 2);
    print("  p=", p, ": (v_P(12-theta), 4e-d, 2e) = ", [[idealval(nf, 12-t, prs[j]), 4*prs[j].e - idealval(nf,12-t,prs[j]), 2*prs[j].e] | j <- [1..#prs]]);
    refs = [nfhilbert(nf, (12-t)/t, b, prs[j]) | j <- [1..#prs]];
    print("    reference products: x=4 -> ", vprod([nfhilbert(nf, (4-t)/t, b, prs[j]) | j <- [1..#prs]]), "   x=12 -> ", vprod(refs));
    A = 8*10^6 + 6; x = 2*A;
    sg = [nfhilbert(nf, (x-t)/t, b, prs[j]) | j <- [1..#prs]];
    Q = F(A,p) - 1;
    J = kronecker(subst(Uof(p), T, x), Q);
    print("    A=", A, " (x mod 16 = ", x % 16, "): dyadic symbols ", sg, " = x=12 reference? ", sg == refs,
          "  J(U_p(2A),Q) = ", J, "  J(x,Q) = ", kronecker(x, Q), "  digits(Q) = ", #digits(Q));
    A = 8*10^6 + 2; x = 2*A;
    sg = [nfhilbert(nf, (x-t)/t, b, prs[j]) | j <- [1..#prs]];
    Q = F(A,p) - 1;
    print("    A=", A, " (x mod 16 = ", x % 16, "): dyadic symbols ", sg, " = x=4 reference? ",
          sg == [nfhilbert(nf, (4-t)/t, b, prs[j]) | j <- [1..#prs]],
          "  J(U_p(2A),Q) = ", kronecker(subst(Uof(p), T, x), Q)); ); }

thm13() = { my(bad = 0, cnt = 0, A, N, v, w);
  for(A = 2, 34, if(A % 4 == 2, for(N = 2, 40, if(N % 2 == 0, cnt++;
      v = valuation(F(A,N) - 1, 2); w = 2*valuation(N,2) + 1;
      if(v != w, bad++; print("  MISMATCH A=", A, " N=", N, " v_2 = ", v, " formula = ", w)); ))));
  print("  Theorem 1.3 scan: ", cnt, " (A,N) pairs checked, mismatches = ", bad); }

print("=== phase-2 support data and huge-x identities ==="); phase2support();
print("=== Theorem 1.3 (even-index 2-adic valuation) scan ==="); thm13();
