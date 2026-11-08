\\ Direct dyadic certificate check for p = 17 (PARI/GP).
\\ Computes the three primes above 2, their (e,f) and (t,d,s) data, and the
\\ individual local Hilbert symbols (delta_4, b_17)_P with delta_4=(4-x)/x,
\\ b_17 = x*U_17(x) in the maximal order of Q[x]/(g_17).
D(n) = {my(a=2,b=x,c); if(n==0,return(2)); if(n==1,return(x)); for(k=2,n,c=x*b+a;a=b;b=c); b;}
g17 = D(17)-2;
U17 = -1 - D(2) + D(3) + D(4) - D(5) - 2*D(12) + D(14);
print("deg g = ", poldegree(g17), "  g(0) = ", subst(g17,x,0));
print("disc(g) = ", factor(poldisc(g17)));
print("Res(g,U) = ", polresultant(g17,U17));
nf = nfinit(g17);
print("nf.disc = ", factor(nf.disc));
prs = idealprimedec(nf,2);
print("number of dyadic primes: ", #prs);
show(pr, i) = {
  my(a = (4-x)/Mod(x,g17), b = Mod(x*U17,g17));
  my(vt = idealval(nf,x,pr), vd = idealval(nf,4-x,pr), vb = idealval(nf,x*U17,pr));
  print("P",i,": e=",pr.e," f=",pr.f," (t,d,s)=(",vt,",",vd,",",vb,")",
        "  4e-d=",4*pr.e-vd,"  2e=",2*pr.e,
        "  (delta4,b)=", nfhilbert(nf, a, b, pr));
};
for(i=1,#prs, show(prs[i], i));
print("product of dyadic signs = ", prod(i=1,#prs, nfhilbert(nf, (4-x)/Mod(x,g17), Mod(x*U17,g17), prs[i])));
print("total degree check sum ef = ", sum(i=1,#prs, prs[i].e*prs[i].f));
print("bare-theta reference product (b replaced by theta) = ", prod(i=1,#prs, nfhilbert(nf, (4-x)/Mod(x,g17), Mod(x,g17), prs[i])));
