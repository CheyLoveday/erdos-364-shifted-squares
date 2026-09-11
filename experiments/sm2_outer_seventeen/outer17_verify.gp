\\ Outer-17 exact certificate verifier.
\\ Run with:
\\   gp -q -f experiments/sm2_outer_seventeen/outer17_verify.gp
\\
\\ Success emits exactly one line. Any mismatch exits nonzero.

cert_assert(c, msg) =
{
  if (!c,
    print(Str("OUTER17_CERTIFICATE_FAIL: ", msg));
    quit(1)
  );
};

default(factor_proven, 1);
setrand(1);

outer17_main() =
{
  my(
    x = 'x,
    A = 'A,
    g, u,
    d0, d1, d2,
    f0, f1, f2,
    nf, th, uu, bb, delta4,
    p2, p17, d2desc, d17desc,
    g4, u4, b4, H, N,
    fd, fdrows, fddesc, oddhilb
  );

  cert_assert(version() == [2, 17, 3], "PARI version is not 2.17.3");

  g =
    x^17
    + 17*x^15
    + 119*x^13
    + 442*x^11
    + 935*x^9
    + 1122*x^7
    + 714*x^5
    + 204*x^3
    + 17*x
    - 2;

  u =
    x^14
    + 12*x^12
    + 53*x^10
    + 102*x^8
    + 70*x^6
    - x^5
    - 13*x^4
    - 4*x^3
    - 20*x^2
    - 2*x
    - 3;

  \\ D_17(x,-1)-2 = g(x).
  d0 = 2;
  d1 = x;
  for (k = 2, 17,
    d2 = x*d1 + d0;
    d0 = d1;
    d1 = d2;
  );
  cert_assert(d1 - 2 == g, "Dickson polynomial mismatch");

  \\ g(2*A) = 2*(sm2LucasReal(A,17)-1).
  f0 = 1;
  f1 = A;
  for (k = 2, 17,
    f2 = 2*A*f1 + f0;
    f0 = f1;
    f1 = f2;
  );
  cert_assert(
    subst(g, x, 2*A) == 2*(f1 - 1),
    "Lucas bridge mismatch"
  );

  \\ Irreducibility and field structure.
  cert_assert(isprime(67) == 1, "67 primality");
  cert_assert(
    polisirreducible(Mod(1, 67)*g) == 1,
    "g reducible modulo 67"
  );
  cert_assert(
    polisirreducible(g) == 1,
    "g reducible over Q"
  );
  cert_assert(
    poldisc(g) == 2^24 * 17^17,
    "polynomial discriminant"
  );

  nf = nfinit(g);

  cert_assert(nf.index == 1, "power order not maximal");
  cert_assert(
    nf.disc == 2^24 * 17^17,
    "field discriminant"
  );
  cert_assert(nf.sign == [1, 8], "signature");

  th = Mod(x, g);
  uu = Mod(u, g);
  bb = th * uu;
  delta4 = (4 - th) / th;

  \\ Explicit unit and norm checks.
  cert_assert(
    polresultant(g, u) == -1,
    "resultant(g,u)"
  );
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

  \\ Dyadic decomposition and local Hilbert symbols.
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
      idealval(nf, 4 - th, P),
      idealval(nf, bb, P),
      nfhilbert(nf, delta4, bb, P)
    ]
  );

  cert_assert(
    vecsort(d2desc) ==
      [
        [1, 1, 1, 1, 1,  1],
        [2, 4, 0, 0, 0, -1],
        [2, 4, 0, 0, 0,  1]
      ],
    "dyadic descriptor"
  );

  cert_assert(
    prod(i = 1, #d2desc, d2desc[i][6]) == -1,
    "dyadic Hilbert product"
  );

  \\ Unique totally ramified prime above 17.
  p17 = idealprimedec(nf, 17);
  cert_assert(#p17 == 1, "17 not unique");

  d17desc = vector(
    #p17,
    i,
    my(P = p17[i]);
    [
      P.e,
      P.f,
      idealval(nf, th, P),
      idealval(nf, 4 - th, P),
      idealval(nf, bb, P),
      nfhilbert(nf, delta4, bb, P)
    ]
  );

  cert_assert(
    d17desc == [[17, 1, 0, 0, 0, 1]],
    "17 descriptor"
  );

  \\ Reference specialization x=4.
  g4 = subst(g, x, 4);
  u4 = subst(u, x, 4);
  b4 = 4*u4;
  H = 1751444197;
  N = g4/2;

  cert_assert(g4 == 45537549122, "g(4)");
  cert_assert(u4 == 532303029, "u(4)");
  cert_assert(b4 == 2129212116, "b(4)");

  \\ isprime(), not ispseudoprime(): these are proven primality tests.
  cert_assert(isprime(13) == 1, "13 primality");
  cert_assert(isprime(H) == 1, "H primality");

  cert_assert(
    g4 == 2*13*H,
    "reference factorization"
  );
  cert_assert(
    N == 22768774561,
    "reference half norm"
  );

  \\ Odd-place residue-symbol cross-check.
  cert_assert(b4 % 13 == 5, "b4 mod 13");
  cert_assert(
    kronecker(b4, 13) == -1,
    "Legendre at 13"
  );

  cert_assert(
    b4 % H == 377767919,
    "b4 mod H"
  );
  cert_assert(
    Mod(74878818, H)^2 == Mod(377767919, H),
    "square witness at H"
  );
  cert_assert(
    kronecker(b4, H) == 1,
    "Legendre at H"
  );
  cert_assert(
    kronecker(b4, N) == -1,
    "reference Jacobi"
  );

  \\ Exact odd ideal support of delta_4.
  fd = idealfactor(nf, delta4);
  fdrows = matsize(fd)[1];

  cert_assert(
    fdrows == 2,
    "delta4 ideal support size"
  );

  fddesc = vector(
    fdrows,
    i,
    my(P = fd[i, 1]);
    [
      P.p,
      P.e,
      P.f,
      fd[i, 2],
      idealval(nf, bb, P)
    ]
  );

  cert_assert(
    vecsort(fddesc) ==
      [
        [13,         1, 1, 1, 0],
        [1751444197, 1, 1, 1, 0]
      ],
    "delta4 odd ideal factorization"
  );

  oddhilb = vecsort(
    vector(
      fdrows,
      i,
      nfhilbert(nf, delta4, bb, fd[i, 1])
    )
  );

  cert_assert(
    oddhilb == [-1, 1],
    "odd Hilbert symbols"
  );

  \\ With signature (1,8), these signs bracket the unique real root
  \\ strictly between 0 and 4.
  cert_assert(
    subst(g, x, 0) == -2 && g4 > 0,
    "real root bracket"
  );

  print(
    "OUTER17_CERTIFICATE_OK ",
    "pari=2.17.3 ",
    "target=no_sm2LucasReal_seventeen_square_of_mod_eight_two"
  );
};

iferr(outer17_main(), E, print("OUTER17_CERTIFICATE_FAIL: unexpected PARI/GP error"); quit(1));
