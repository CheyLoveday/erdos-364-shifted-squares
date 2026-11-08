\\ Direct check of the odd local formula (3.7) at non-reference points, with r = v_ell(Q) arbitrary.
\\ For each ell | Q we verify: exactly one prime above ell divides delta_x, with f=1;
\\ its Hilbert symbol equals the ell-th power of the Legendre symbol of the residue x*U_p(x).
Dp(n) = { my(d0=2, d1=T, d2); if(n==0, return(2)); for(k=2, n, d2 = T*d1 + d0; d0 = d1; d1 = d2); d1; }
C41 = [-1,-15,2,4,8,7,-8, -10,-3,6,7,3,-1,-9, 3,7,2,3,-9,-6,1, 8,4,1,-4,-6,3,7, 0,2,-7,-4,1,6,-1, 0,-2,-5,4,5,-5];
U17p = -1 - Dp(2) + Dp(3) + Dp(4) - Dp(5) - 2*Dp(12) + Dp(14);
U41p = C41[1] + sum(k=1, 40, C41[k+1]*Dp(k));
Uof(p) = if(p == 17, U17p, U41p);
vprod(v) = { my(s=1); for(i=1, #v, s *= v[i]); s; }

bridge(p, x, tmax) =
{
  my(g, nf, t, u, b, dx, Q, f, prod = 1, ok = 1, ell, prl, supp, vP, sym, leg, ex);
  g = Dp(p) - 2; nf = nfinit(g, 1); t = Mod(T, g); u = subst(Uof(p), T, t); b = t*u;
  dx = (x - t)/t; Q = subst(g, T, x)/2; f = factor(Q);
  print("  p=", p, " x=", x, "  Q=", Q, "  #prime factors=", matsize(f)[1], "  factor ms=", gettime());
  for(i = 1, matsize(f)[1],
    ell = f[i,1]; ex = f[i,2];
    prl = idealprimedec(nf, ell);
    supp = [j | j <- [1..#prl], idealval(nf, dx, prl[j]) != 0];
    if(#supp != 1, ok = 0; print("    !! ell=", ell, " support size ", #supp));
    vP = idealval(nf, dx, prl[supp[1]]);
    sym = nfhilbert(nf, dx, b, prl[supp[1]]);
    leg = kronecker(x*subst(Uof(p), T, x), ell);
    if(prl[supp[1]].f != 1 || vP != ex, ok = 0; print("    !! ell=", ell, " f=", prl[supp[1]].f, " v_P=", vP, " v_ell=", ex));
    if(sym != leg^ex, ok = 0; print("    !! ell=", ell, " symbol=", sym, " Legendre^exp=", leg^ex));
    prod *= sym;
  );
  print("    product of odd symbols = ", prod, "   J(x*U_p(x),Q) = ", kronecker(x*subst(Uof(p),T,x), Q), "   all local checks ok = ", ok);
}

print("=== odd local formula (3.7) at non-reference points ===");
bridge(17, 20, 60);
bridge(17, 28, 60);
bridge(17, 36, 60);
bridge(41, 20, 60);
bridge(41, 12, 60);   \\ exponent-3 case (5^3) and the phase-2 reference
bridge(41, 28, 300);
