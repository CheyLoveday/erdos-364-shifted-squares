D(n) = {my(a=2,b=x,c); if(n==0,return(2)); if(n==1,return(x)); for(k=2,n,c=x*b+a;a=b;b=c); b;}
g17 = D(17)-2;
U17 = -1 - D(2) + D(3) + D(4) - D(5) - 2*D(12) + D(14);
nf = nfinit(g17);
bridge(A0) = {
  my(Q = subst(D(17),x,2*A0)/2 - 1, f = factor(Q), prod = 1, prodJ = 1);
  print("A = ", A0, "  Q = ", Q, "  factor = ", f~);
  for(j=1,#f~,
    my(ell = f[j,1], ee = f[j,2]);
    my(prs = idealprimedec(nf, ell));
    my(supp = 0);
    for(k=1,#prs,
      if(idealval(nf, Mod(2*A0 - x, g17), prs[k]) > 0, supp = k));
    if(supp == 0, print("  no supporting prime for ", ell); next);
    my(pr = prs[supp]);
    my(s = nfhilbert(nf, Mod(2*A0-x,g17)/Mod(x,g17), Mod(x*U17,g17), pr));
    my(leg = 1);
    my(res = lift(Mod((2*A0)*subst(U17,x,2*A0), ell)));
    my(ls = lift(Mod(res,ell)^((ell-1)/2)));
    if(ls == ell-1, leg = -1, if(ls == 0, leg = 0, leg = 1));
    print("   ell=", ell, " e=", ee, " f=", pr.f, " e(pr)=", pr.e, " local symbol=", s, "^", ee, "   (xU(x)/ell)=", leg);
    prod *= s^ee; prodJ *= leg^ee;
  );
  print("  product of odd local symbols = ", prod, "     Jacobi J(xU(x),Q) = ", prodJ, "    J(U(2A),Q) = ", kronecker(subst(U17,x,2*A0), Q));
};
bridge(2);
bridge(10);
bridge(14);
