\\ Phase-2 reference data (x = 12, i.e. A = 6) and the two-phase Jacobi identity.
\\ Run: gp -q audit_phase2.gp
Dp(n) = { my(d0=2, d1=T, d2); if(n==0, return(2)); for(k=2, n, d2 = T*d1 + d0; d0 = d1; d1 = d2); d1; }
C41 = [-1,-15,2,4,8,7,-8, -10,-3,6,7,3,-1,-9, 3,7,2,3,-9,-6,1, 8,4,1,-4,-6,3,7, 0,2,-7,-4,1,6,-1, 0,-2,-5,4,5,-5];
U17p = -1 - Dp(2) + Dp(3) + Dp(4) - Dp(5) - 2*Dp(12) + Dp(14);
U41p = C41[1] + sum(k=1, 40, C41[k+1]*Dp(k));
Uof(p) = if(p == 17, U17p, U41p);
F(A, n) = { my(f0=1, f1=A, f2); if(n==0, return(1)); for(k=2, n, f2 = 2*A*f1 + f0; f0 = f1; f1 = f2); f1; }
vprod(v) = { my(s=1); for(i=1, #v, s *= v[i]); s; }

audit(p) =
{
  my(g, nf, t, u, b, prs, d12, sg12, Q12, J12, Q4, J4, x, dx, tot, k, sg);
  g = Dp(p) - 2; nf = nfinit(g, 1);
  t = Mod(T, g); u = subst(Uof(p), T, t); b = t*u; d12 = (12 - t)/t;
  prs = idealprimedec(nf, 2);
  sg12 = [nfhilbert(nf, d12, b, prs[i]) | i <- [1..#prs]];
  print("=== p = ", p, " ===");
  print("  x=12 (A=6) dyadic symbols = ", sg12, "  product = ", vprod(sg12));
  Q12 = subst(g, T, 12)/2;
  print("  Q12 = g_p(12)/2 = F_p(6)-1 = ", Q12, "   odd? ", Q12 % 2 == 1, "   mod 8 = ", Q12 % 8);
  J12 = kronecker(12*subst(Uof(p),T,12), Q12);
  print("  J(12*U_p(12), Q12) = ", J12, "   J(U_p(12), Q12) = ", kronecker(subst(Uof(p),T,12), Q12), "   J(12,Q12) = ", kronecker(12, Q12));
  print("  total product at x=12 (odd*dyadic*real) = ", J12 * vprod(sg12), "   (reciprocity demands +1)");
  Q4 = subst(g, T, 4)/2;
  J4 = kronecker(4*subst(Uof(p),T,4), Q4);
  print("  total product at x=4  (odd*dyadic*real) = ", J4 * vprod([nfhilbert(nf, (4-t)/t, b, prs[i]) | i <- [1..#prs]]));
  \\ stability with reference x0 = 12 for x = 12 mod 16
  for(k = 0, 4, x = 12 + 16*k; dx = (x-t)/t;
    sg = [nfhilbert(nf, dx, b, prs[i]) | i <- [1..#prs]];
    print("    x=", x, ": ", sg, "  agree with x=12? ", sg == sg12));
  \\ large-x check of stability with reference 4
  x = 4 + 16*10^6; dx = (x-t)/t;
  sg = [nfhilbert(nf, dx, b, prs[i]) | i <- [1..#prs]];
  print("    x=16000004: ", sg, "  agree with x=4? ", sg == [nfhilbert(nf, (4-t)/t, b, prs[i]) | i <- [1..#prs]]);
  print("  Q12 factored: ", factor(Q12));
}
audit(17);
audit(41);

\\ (Proposition 2.1 mod-8 scan lives in audit_final.gp)
