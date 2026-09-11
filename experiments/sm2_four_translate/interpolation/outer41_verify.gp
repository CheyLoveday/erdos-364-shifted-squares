\\ Fixed-41 shifted-square exact certificate verifier.
\\ Run with:
\\   gp -q -f experiments/sm2_four_translate/interpolation/outer41_verify.gp
\\
\\ Success emits exactly one line. Any mismatch exits nonzero.

cert_assert(c, msg) =
{
  if (!c,
    print(Str("OUTER41_CERTIFICATE_FAIL: ", msg));
    quit(1)
  );
};

default(factor_proven, 1);
setrand(1);

outer41_main() =
{
  my(
    x = 'x,
    A = 'A,
    a41,
    g, u,
    d0, d1, d2,
    f0, f1, f2,
    nf, th, uu, bb, delta4,
    p2, p41, d2desc, d41desc,
    g4, u4, b4, H, Hfac,
    fd, fddesc
  );

  cert_assert(version() == [2, 17, 3], "PARI version is not 2.17.3");

  \\ Dickson-basis coordinates of the detecting unit u_41.
  a41 = [
    -1, -15, 2, 4, 8, 7, -8, -10, -3, 6, 7, 3, -1, -9,
    3, 7, 2, 3, -9, -6, 1, 8, 4, 1, -4, -6, 3, 7, 0, 2,
    -7, -4, 1, 6, -1, 0, -2, -5, 4, 5, -5
  ];

  \\ Build D_0=2, D_1=x, D_(n+2)=x*D_(n+1)+D_n,
  \\ while reconstructing u_41=sum_(n=0)^40 a_n D_n.
  d0 = 2;
  d1 = x;
  u = a41[1] + a41[2]*d1;
  for (k = 2, 41,
    d2 = x*d1 + d0;
    if (k <= 40, u += a41[k + 1]*d2);
    d0 = d1;
    d1 = d2;
  );
  g = d1 - 2;

  cert_assert(poldegree(g) == 41, "Dickson degree");
  cert_assert(poldegree(u) == 40, "unit degree");

  \\ g(2*A)=2*(sm2LucasReal(A,41)-1).
  f0 = 1;
  f1 = A;
  for (k = 2, 41,
    f2 = 2*A*f1 + f0;
    f0 = f1;
    f1 = f2;
  );
  cert_assert(
    subst(g, x, 2*A) == 2*(f1 - 1),
    "Lucas bridge mismatch"
  );

  \\ Irreducibility and field structure.
  cert_assert(isprime(163) == 1, "163 primality");
  cert_assert(
    polisirreducible(Mod(1, 163)*g) == 1,
    "g reducible modulo 163"
  );
  cert_assert(polisirreducible(g) == 1, "g reducible over Q");
  cert_assert(
    poldisc(g) == 2^60 * 41^41,
    "polynomial discriminant"
  );

  nf = nfinit(g);

  cert_assert(nf.index == 1, "power order not maximal");
  cert_assert(
    nf.disc == 2^60 * 41^41,
    "field discriminant"
  );
  cert_assert(nf.sign == [1, 20], "signature");

  th = Mod(x, g);
  uu = Mod(u, g);
  bb = th*uu;
  delta4 = (4-th)/th;

  \\ Unit, norm and principal-ideal checks.
  cert_assert(polresultant(g, u) == -1, "resultant(g,u)");
  cert_assert(nfeltnorm(nf, th) == 2, "N(theta)");
  cert_assert(nfeltnorm(nf, uu) == -1, "N(u)");
  cert_assert(nfeltnorm(nf, bb) == -2, "N(b)");
  cert_assert(
    matsize(idealfactor(nf, uu))[1] == 0,
    "u not a unit"
  );
  cert_assert(
    idealhnf(nf, bb) == idealhnf(nf, th),
    "(b)!=(theta)"
  );

  \\ Dyadic decomposition, valuations and local Hilbert symbols.
  p2 = idealprimedec(nf, 2);
  cert_assert(#p2 == 3, "number of dyadic primes");

  d2desc = vector(
    #p2,
    i,
    my(P = p2[i]);
    [
      P.e,
      P.f,
      idealval(nf, th, P),
      idealval(nf, 4-th, P),
      idealval(nf, bb, P),
      nfhilbert(nf, delta4, bb, P)
    ]
  );

  cert_assert(
    vecsort(d2desc) ==
      [
        [1,  1, 1, 1, 1,  1],
        [2, 10, 0, 0, 0, -1],
        [2, 10, 0, 0, 0,  1]
      ],
    "dyadic descriptor"
  );
  cert_assert(
    prod(i = 1, #d2desc, d2desc[i][6]) == -1,
    "dyadic Hilbert product"
  );

  \\ Unique totally ramified prime above 41.
  p41 = idealprimedec(nf, 41);
  cert_assert(#p41 == 1, "41-prime count");

  d41desc = vector(
    #p41,
    i,
    my(P = p41[i]);
    [
      P.e,
      P.f,
      idealval(nf, th, P),
      idealval(nf, 4-th, P),
      idealval(nf, bb, P),
      nfhilbert(nf, delta4, bb, P)
    ]
  );

  cert_assert(
    d41desc == [[41, 1, 0, 0, 0, 1]],
    "41 descriptor"
  );
  cert_assert(
    Mod(1, 41)*g == Mod(1, 41)*(x-2)^41,
    "mod-41 ramification identity"
  );

  \\ Reference specialization x=4.
  g4 = subst(g, x, 4);
  u4 = subst(u, x, 4);
  b4 = 4*u4;
  H = g4/2;

  cert_assert(
    g4 == 50755107359004694554823202,
    "g(4)"
  );
  cert_assert(
    H == 25377553679502347277411601,
    "H41"
  );
  cert_assert(
    u4 == -43956715453803235217163523,
    "u(4)"
  );
  cert_assert(
    b4 == -175826861815212940868654092,
    "b(4)"
  );
  cert_assert(H % 8 == 1, "H phase");
  cert_assert(gcd(H, u4) == 1, "reference gcd");
  cert_assert(kronecker(u4, H) == -1, "reference character");
  cert_assert(kronecker(b4, H) == -1, "reference b character");

  Hfac = factor(H);
  cert_assert(
    Hfac ==
      [79, 1;
       1373, 1;
       115471, 1;
       1506563, 1;
       1344905911, 1],
    "H factorization"
  );
  for (i = 1, matsize(Hfac)[1],
    cert_assert(isprime(Hfac[i, 1]) == 1, "H factor primality")
  );

  \\ Exact finite support of the reference element delta_4.
  fd = idealfactor(nf, delta4);
  cert_assert(matsize(fd)[1] == 5, "delta4 support size");

  fddesc = vector(
    matsize(fd)[1],
    i,
    my(P = fd[i, 1]);
    [
      P.p,
      P.e,
      P.f,
      fd[i, 2],
      idealval(nf, bb, P),
      nfhilbert(nf, delta4, bb, P)
    ]
  );

  cert_assert(
    vecsort(fddesc) ==
      [
        [79,         1, 1, 1, 0,  1],
        [1373,       1, 1, 1, 0, -1],
        [115471,     1, 1, 1, 0, -1],
        [1506563,    1, 1, 1, 0, -1],
        [1344905911, 1, 1, 1, 0,  1]
      ],
    "delta4 support"
  );
  cert_assert(
    prod(i = 1, #fddesc, fddesc[i][6]) == -1,
    "odd Hilbert product"
  );

  \\ With signature (1,20), these signs bracket the unique real root
  \\ strictly between 0 and 4.
  cert_assert(
    subst(g, x, 0) == -2 && g4 > 0,
    "real root bracket"
  );

  print(
    "OUTER41_CERTIFICATE_OK ",
    "pari=2.17.3 ",
    "target=no_sm2LucasReal_forty_one_square_of_mod_eight_two"
  );
};

iferr(outer41_main(), E, print("OUTER41_CERTIFICATE_FAIL: unexpected PARI/GP error"); quit(1));
