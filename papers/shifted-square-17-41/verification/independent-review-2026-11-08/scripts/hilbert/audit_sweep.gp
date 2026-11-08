\\ Sweep: no shifted square in the whole fixed-index family for small A (both phases).
Dp(n) = { my(d0=2, d1=T, d2); if(n==0, return(2)); for(k=2, n, d2 = T*d1 + d0; d0 = d1; d1 = d2); d1; }
F(A, n) = { my(f0=1, f1=A, f2); if(n==0, return(1)); for(k=2, n, f2 = 2*A*f1 + f0; f0 = f1; f1 = f2); f1; }
sweep() = { my(Amax = 4002, sq = 0, cnt = 0, A);
  for(A = 2, Amax, if(A % 4 == 2, cnt++;
     if(issquare(F(A,17)-1), sq++; print("  SQUARE p=17 at A=", A));
     if(issquare(F(A,41)-1), sq++; print("  SQUARE p=41 at A=", A));  ));
  print("  A=2..", Amax, " with A=2 mod 4: ", cnt, " parameters, shifted squares found: ", sq); }
sweep();
