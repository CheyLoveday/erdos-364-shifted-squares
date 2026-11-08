D(n) = {my(a=2,b=x,c); if(n==0,return(2)); if(n==1,return(x)); for(k=2,n,c=x*b+a;a=b;b=c); b;}
g17 = D(17)-2;
U17 = -1 - D(2) + D(3) + D(4) - D(5) - 2*D(12) + D(14);
nf = nfinit(g17);
prs = idealprimedec(nf,2);
dyad(A0) = {
  my(prod=1);
  for(i=1,#prs,
    my(pr=prs[i]);
    my(s = nfhilbert(nf, Mod(2*A0-x,g17)/Mod(x,g17), Mod(x*U17,g17), pr));
    my(st = nfhilbert(nf, Mod(4-x,g17)/Mod(x,g17), Mod(x*U17,g17), pr));
    my(ratio_sq = 0);
    my(r = Mod(2*A0-x,g17)/Mod(4-x,g17));
    print("  P",i," e=",pr.e," f=",pr.f,"  (delta_x,b)=",s,"  (delta_4,b)=",st,
          "  vP(x-4)=",idealval(nf,2*A0-x,pr), " vP(4-x)=",idealval(nf,4-x,pr));
    prod *= s);
  print("  A=",A0," dyadic product = ", prod);
};
print("A=2 (2 mod 8):"); dyad(2);
print("A=10 (2 mod 8):"); dyad(10);
print("A=14 (6 mod 8):"); dyad(14);
print("A=22 (6 mod 8):"); dyad(22);
print("A=6 (6 mod 8):"); dyad(6);
