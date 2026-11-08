\\ Second-pass audit: signature, ramified prime, Prop 4.1, direct Q_2 symbol,
\\ Hensel transfer/sharpness at parameter points, stress test of Prop 7.1.
\\ Run: gp -q audit_chain.gp
Dp(n) = { my(d0=2, d1=T, d2); if(n==0, return(2)); for(k=2, n, d2 = T*d1 + d0; d0 = d1; d1 = d2); d1; }
C41 = [-1,-15,2,4,8,7,-8, -10,-3,6,7,3,-1,-9, 3,7,2,3,-9,-6,1, 8,4,1,-4,-6,3,7, 0,2,-7,-4,1,6,-1, 0,-2,-5,4,5,-5];
U17p = -1 - Dp(2) + Dp(3) + Dp(4) - Dp(5) - 2*Dp(12) + Dp(14);
U41p = C41[1] + sum(k=1, 40, C41[k+1]*Dp(k));
Uof(p) = if(p == 17, U17p, U41p);
F(A, n) = { my(f0=1, f1=A, f2); if(n==0, return(1)); for(k=2, n, f2 = 2*A*f1 + f0; f0 = f1; f1 = f2); f1; }
vprod(v) = { my(s=1); for(i=1, #v, s *= v[i]); s; }

\\ Newton lift of the root of g in Z_2 with v_2(root)=1, to precision 2^N.
liftq2(g, N) = {
  my(r = 2, k = 6, dg, gg, m, i);
  while(k < N,
    m = 2^(2*k);
    dg = subst(g, T, r);
    gg = subst(deriv(g, T), T, r);
    r = (r - subst(g, T, r) * lift(Mod(gg, m)^(-1))) % m;
    k = 2*k;
  );
  r % 2^N;
}

audit(p) =
{
  my(g, nf, t, u, b, d4, prs, ref, H, fH, ell, aux, sig, prp, prodtheta, tau, a8, c8, aint, cint, symq2, cnt, bad, sq, Amax, x, dx, sg, nfail, nfail6, fm);
  g = Dp(p) - 2;
  print("=== p = ", p, " ===");
  nf = nfinit(g, 1);
  sig = nf.sign; print("  signature (r1,r2) = ", sig);
  aux = if(p == 17, 67, 163);
  my(fm = factormod(g, aux));
  print("  factormod(g,", aux, "): [degree, mult] = ", [[poldegree(fm[i,1]), fm[i,2]] | i <- [1..matsize(fm)[1]]], "  irreducible over Q? ", polisirreducible(g));
  prp = idealprimedec(nf, p);
  print("  #P|p = ", #prp, "  (e,f) = ", [[prp[i].e, prp[i].f] | i <- [1..#prp]], "  P = (p, theta-2)? ",
        idealhnf(nf, p, Mod(T-2, g)) == idealhnf(nf, prp[1]));
  print("  g_p(2)/p mod p = ", subst(g,T,2)/p % p);
  t = Mod(T, g); u = subst(Uof(p), T, t); b = t*u; d4 = (4 - t)/t;
  prs = idealprimedec(nf, 2);
  ref = [nfhilbert(nf, d4, b, prs[i]) | i <- [1..#prs]];
  print("  dyadic product with b = theta*u : ", ref, " -> ", vprod(ref));
  prodtheta = [nfhilbert(nf, d4, t, prs[i]) | i <- [1..#prs]];
  print("  dyadic product with b = theta   : ", prodtheta, " -> ", vprod(prodtheta), "   (Prop 4.1 predicts +1)");
  \\ direct Q_2 computation at the (1,1) prime
  tau = liftq2(g, 64);
  print("  v_2(tau) = ", valuation(tau, 2), "  g(tau) mod 2^32 == 0 ? ", subst(g, T, tau) % 2^32 == 0);
  a8 = ((2 - tau/2) * lift(Mod((tau/2), 8)^(-1))) % 8;   \\ a = (4-tau)/tau = (2-sigma)/sigma, sigma = tau/2
  c8 = ((tau/2) * subst(Uof(p), T, tau)) % 8;             \\ c/2 = sigma*U(tau)
  aint = if(a8 % 2 == 0, a8+8, a8); if(aint < 0, aint += 8*ceil(-aint/8));
  cint = 2*if(c8 % 2 == 0, c8+8, c8); if(cint < 0, cint += 16*ceil(-cint/16));
  symq2 = hilbert(aint, cint, 2);
  print("  direct Q_2 symbol ((4-theta)/theta, b) at the degree-1 dyadic prime = ", symq2,
        "   [nfhilbert at P1 = ", ref[1], "; a mod 8 = ", a8, ", (c/2) mod 8 = ", c8, "]");
  \\ Hensel transfer and sharpness at concrete parameter points
  for(k = 0, 6,
    x = 4 + 16*k; dx = (x - t)/t;
    sg = [nfhilbert(nf, dx, b, prs[i]) | i <- [1..#prs]];
    print("    x=", x, ": dyadic symbols ", sg, "  agree with reference? ", sg == ref);
  );
  for(k = 1, 3,
    x = 12 + 16*k; dx = (x - t)/t;
    sg = [nfhilbert(nf, dx, b, prs[i]) | i <- [1..#prs]];
    print("    x=", x, " (12 mod 16): dyadic symbols ", sg, "  agree with reference? ", sg == ref);
  );
  \\ stress test of Proposition 7.1 (A = 2 mod 8) and of the phase restriction (A = 6 mod 8)
  nfail = 0; nfail6 = 0; Amax = 4002;
  forstep(A = 2, Amax, 8,
    my(Q = F(A, p) - 1, W = subst(Uof(p), T, 2*A));
    if(gcd(W, Q) != 1, print("    !!! common factor at A=", A));
    if(kronecker(W, Q) != -1, nfail++; print("    !!! Prop 7.1 fails at A=", A));
  );
  forstep(A = 6, Amax, 8,
    my(Q = F(A, p) - 1, W = subst(Uof(p), T, 2*A));
    if(kronecker(W, Q) != -1, nfail6++);
  );
  print("  Prop 7.1 stress: A=2..", Amax, " step 8: failures = ", nfail, " (of ", (Amax-2)/8+1, ")");
  print("  phase-restriction contrast: A=6..", Amax, " step 8: J = -1 holds for ", (Amax-6)/8+1 - nfail6, " of ", (Amax-6)/8+1);
  sq = 0;
  forstep(A = 2, Amax, 8, if(issquare(F(A,p)-1), sq++; print("    !!! shifted square at A=", A)));
  print("  shifted squares F_p(A)-1 for A=2..", Amax, ", A=2 mod 8: ", sq);
  \\ Section 7.2 reference remarks
  print("  F_41(2)-1 mod 23 = ", (F(2,41)-1) % 23, "   kronecker(20,23) = ", kronecker(20,23));
  print("  F_17(2)-1 mod 13 = ", (F(2,17)-1) % 13);
}
audit(17);
audit(41);
