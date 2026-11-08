D(n) = {my(a=2,b=x,c); if(n==0,return(2)); if(n==1,return(x)); for(k=2,n,c=x*b+a;a=b;b=c); b;}
g17 = D(17)-2;
nf = nfinit(g17);
prs = idealprimedec(nf,2);
P1 = prs[1];
test(a,b) = {print("  a=",a," b=",b,": nfhilbert=",nfhilbert(nf,a,b,P1),"  hilbert(a,b,2)=",hilbert(a,b,2));};
print("validate nfhilbert against Q_2 hilbert() at the e=f=1 dyadic prime:");
test(5,2); test(3,-1); test(-1,-1); test(2,2); test(5,10); test(3,5); test(-2,3);
print("dyadic (e,f) rows: ", [[pr.e,pr.f] | pr <- prs]);
