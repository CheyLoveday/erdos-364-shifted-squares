\\ Independent PARI verification of dyadic and odd reference Hilbert data (p=17,41).
\\ Run: gp -q audit_hilbert.gp
Dp(n) = { my(d0=2, d1=T, d2); if(n==0, return(2)); for(k=2, n, d2 = T*d1 + d0; d0 = d1; d1 = d2); d1; }
C41 = [-1,-15,2,4,8,7,-8, -10,-3,6,7,3,-1,-9, 3,7,2,3,-9,-6,1, 8,4,1,-4,-6,3,7, 0,2,-7,-4,1,6,-1, 0,-2,-5,4,5,-5];
U17p(T) = -1 - Dp(2) + Dp(3) + Dp(4) - Dp(5) - 2*Dp(12) + Dp(14);
U41p(T) = C41[1] + sum(k=1, 40, C41[k+1]*Dp(k));
vprod(v) = { my(s=1); for(i=1, #v, s *= v[i]); s; }

audit(p, Uexpr) =
{
  my(g, nf, t, u, b, d4, prs, sg, H, fH, ell, prl, supp, sgl, x, dx, ref);
  g = Dp(p) - 2;
  print("=== p = ", p, " ===");
  gettime();
  nf = nfinit(g, 1);
  print("  nfinit ms = ", gettime());
  print("  poldisc == nfdisc ? ", poldisc(g) == nfdisc(g), "   nfdisc = ", factor(nfdisc(g)));
  t = Mod(T, g); u = subst(Uexpr, T, t); b = t*u; d4 = (4 - t)/t;
  print("  N(theta)=", nfeltnorm(nf,t), "  N(U)=", nfeltnorm(nf,u), "  N(b)=", nfeltnorm(nf,b));
  prs = idealprimedec(nf, 2);
  print("  #P|2 = ", #prs, "  (e,f) = ", [[prs[i].e, prs[i].f] | i <- [1..#prs]]);
  print("  (v_P(theta), v_P(4-theta), v_P(b)) = ", [[idealval(nf,t,prs[i]), idealval(nf,4-t,prs[i]), idealval(nf,b,prs[i])] | i <- [1..#prs]]);
  print("  (4e-d > 2e) ? ", [4*prs[i].e - idealval(nf,4-t,prs[i]) > 2*prs[i].e | i <- [1..#prs]]);
  ref = [nfhilbert(nf, d4, b, prs[i]) | i <- [1..#prs]];
  print("  dyadic symbols (delta4,b)_P = ", ref, "   product = ", vprod(ref));
  for(k=0, 3,
    x = 4 + 16*k; dx = (x - t)/t;
    sg = [nfhilbert(nf, dx, b, prs[i]) | i <- [1..#prs]];
    print("    x=", x, " (x-4=", 16*k, "): dyadic symbols ", sg, "  agree with x=4? ", sg == ref);
  );
  x = 12; dx = (x - t)/t;
  sg = [nfhilbert(nf, dx, b, prs[i]) | i <- [1..#prs]];
  print("    x=12 (x-4=8): dyadic symbols ", sg, "  agree with x=4? ", sg == ref);
  x = 4 + 16*100; dx = (x - t)/t;
  sg = [nfhilbert(nf, dx, b, prs[i]) | i <- [1..#prs]];
  print("    x=1604: dyadic symbols ", sg, "  agree with x=4? ", sg == ref);
  H = subst(g, T, 4)/2; fH = factor(H);
  print("  odd reference: ell, v_ell, #P|ell, f-vector, v_P(delta4)-vector, symbol at support, Legendre:");
  for(i = 1, matsize(fH)[1],
    ell = fH[i,1]; prl = idealprimedec(nf, ell);
    supp = [j | j <- [1..#prl], idealval(nf, d4, prl[j]) != 0];
    sgl = if(#supp == 1, nfhilbert(nf, d4, b, prl[supp[1]]), -99);
    print("    ", ell, " ", fH[i,2], " ", #prl, " ", [prl[j].f | j <- [1..#prl]], " ",
          [idealval(nf,d4,prl[j]) | j <- [1..#prl]], " ", supp, " ", sgl, " ", kronecker(4*subst(Uexpr,T,4), ell));
  );
}
audit(17, U17p(T));
audit(41, U41p(T));
