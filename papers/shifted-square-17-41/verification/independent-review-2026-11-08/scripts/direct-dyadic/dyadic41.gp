D(n) = {my(a=2,b=x,c); if(n==0,return(2)); if(n==1,return(x)); for(k=2,n,c=x*b+a;a=b;b=c); b;}
g41 = D(41)-2;
c = [-1,-15,2,4,8,7,-8,-10,-3,6,7,3,-1,-9,3,7,2,3,-9,-6,1,8,4,1,-4,-6,3,7,0,2,-7,-4,1,6,-1,0,-2,-5,4,5,-5];
U41 = c[1]; for(k=1,40, U41 += c[k+1]*D(k));
print("deg g = ", poldegree(g41), " Res = ", polresultant(g41,U41));
print("disc(g) = ", factor(poldisc(g41)));
nf = nfinit(g41);
print("nf.disc = ", factor(nf.disc));
prs = idealprimedec(nf,2);
print("number of dyadic primes = ", #prs);
show(pr, i) = {
  my(a = (4-x)/Mod(x,g41), b = Mod(x*U41,g41));
  my(vt = idealval(nf,x,pr), vd = idealval(nf,4-x,pr), vb = idealval(nf,x*U41,pr));
  print("P",i,": e=",pr.e," f=",pr.f," (t,d,s)=(",vt,",",vd,",",vb,")  4e-d=",4*pr.e-vd,"  2e=",2*pr.e,"  (delta4,b)=", nfhilbert(nf, a, b, pr));
};
for(i=1,#prs, show(prs[i], i));
print("product = ", prod(i=1,#prs, nfhilbert(nf, (4-x)/Mod(x,g41), Mod(x*U41,g41), prs[i])));
