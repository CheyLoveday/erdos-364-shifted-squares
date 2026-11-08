D(n) = {my(a=2,b=x,c); if(n==0,return(2)); if(n==1,return(x)); for(k=2,n,c=x*b+a;a=b;b=c); b;}
g17 = D(17)-2;
U17 = -1 - D(2) + D(3) + D(4) - D(5) - 2*D(12) + D(14);
nf = nfinit(g17);
check(A0, ell) = {
  my(prs = idealprimedec(nf, ell), supp=0);
  for(k=1,#prs, if(idealval(nf, Mod(2*A0 - x, g17), prs[k]) > 0, supp = k));
  my(pr = prs[supp]);
  my(s = nfhilbert(nf, Mod(2*A0-x,g17)/Mod(x,g17), Mod(x*U17,g17), pr));
  my(ee = idealval(nf, 2*A0-x, pr));
  my(res = lift(Mod((2*A0)*subst(U17,x,2*A0), ell)));
  my(ls = lift(Mod(res,ell)^((ell-1)/2)));
  my(leg = if(ls==ell-1,-1, if(ls==0,0,1)));
  print("  A=",A0," ell=",ell," e(pr)=",pr.e," f(pr)=",pr.f," nprimes=",#prs,
        " v_pr(x-theta)=",ee," local symbol=",s," local^v=",s^ee,"  Legendre(xU/ell)^v=",leg^ee);
};
check(18,17);
check(18,499);
check(2,13);
check(2,1751444197);
