\\ Independent Paper I fixed-field replay.
\\
\\ This is deliberately separate from the two certificate producers.  It
\\ reconstructs both source and detector polynomials in the Dickson basis,
\\ then recomputes the fixed-field, local and reference rows with PARI/GP.
\\ Run only as:
\\   gp -q -f papers/shifted-square-17-41/evidence/replay/independent_fixed_fields.gp

e122_assert(c, msg) =
{
  if (!c,
    print(Str("PAPER1_FIXED_FIELD_REPLAY_FAIL: ", msg));
    quit(1)
  );
};

default(factor_proven, 1);
setrand(1);

e122_pair(p, detector) =
{
  my(x = 'x, d0 = 2, d1 = x, d2, u = detector[1] + detector[2]*x);
  for (k = 2, p,
    d2 = x*d1 + d0;
    if (k + 1 <= #detector, u += detector[k + 1]*d2);
    d0 = d1;
    d1 = d2;
  );
  [d1 - 2, u]
};

\\ The fixed p=41 detector uses a_0 as a scalar, not a_0*D_0.
\\ This deliberately reconstructs the rejected alternative with D_0=2.
e122_pair_wrong_d0(p, detector) =
{
  my(x = 'x, d0 = 2, d1 = x, d2, u = detector[1]*d0 + detector[2]*x);
  for (k = 2, p,
    d2 = x*d1 + d0;
    if (k + 1 <= #detector, u += detector[k + 1]*d2);
    d0 = d1;
    d1 = d2;
  );
  [d1 - 2, u]
};

e122_descriptor(nf, th, bb, delta4, P) =
{
  [
    P.e,
    P.f,
    idealval(nf, th, P),
    idealval(nf, 4 - th, P),
    idealval(nf, bb, P),
    nfhilbert(nf, delta4, bb, P)
  ]
};

e122_verify_outer17_prs() =
{
  my(
    A = 'A,
    R0 = 65536*A^17 + 278528*A^15 + 487424*A^13 +
      452608*A^11 + 239360*A^9 + 71808*A^7 + 11424*A^5 +
      816*A^3 + 17*A - 1,
    R1 = 16384*A^14 + 49152*A^12 + 54272*A^10 + 26112*A^8 +
      4480*A^6 - 32*A^5 - 208*A^4 - 32*A^3 - 80*A^2 - 4*A - 3,
    R2 = 24576*A^13 + 76800*A^11 + 90880*A^9 + 128*A^8 +
      50240*A^7 + 288*A^6 + 12784*A^5 + 176*A^4 + 1228*A^3 +
      20*A^2 + 32*A - 1,
    R3 = 6144*A^12 + 18944*A^10 + 256*A^9 + 22144*A^8 +
      576*A^7 + 12128*A^6 + 448*A^5 + 3080*A^4 + 136*A^3 +
      304*A^2 + 10*A + 9,
    R4 = 1024*A^11 - 1024*A^10 + 2304*A^9 - 2176*A^8 +
      1728*A^7 - 1504*A^6 + 464*A^5 - 368*A^4 + 12*A^3 -
      20*A^2 - 4*A - 1,
    R5 = 11264*A^10 - 512*A^9 + 24832*A^8 - 768*A^7 +
      18368*A^6 - 128*A^5 + 5216*A^4 + 184*A^3 + 448*A^2 +
      40*A + 15,
    R6 = 512*A^9 + 11776*A^8 - 2048*A^7 + 24576*A^6 -
      5152*A^5 + 16432*A^4 - 3088*A^3 + 3688*A^2 - 458*A + 73,
    R7 = 8320*A^8 - 2176*A^7 + 17344*A^6 - 4096*A^5 +
      11576*A^4 - 2268*A^3 + 2590*A^2 - 322*A + 51,
    R8 = 1792*A^7 - 2048*A^6 + 4352*A^5 - 3232*A^4 +
      3336*A^3 - 1200*A^2 + 854*A + 23,
    R9 = 128*A^6 - 160*A^5 + 216*A^4 - 240*A^3 + 82*A^2 - 91*A - 1,
    R10 = 64*A^5 - 8*A^4 + 104*A^3 - 2*A^2 + 41*A + 1,
    R11 = 40*A^4 + 8*A^3 + 18*A^2 + 3*A - 5,
    R12 = 248*A^3 + 8*A^2 + 158*A - 5,
    R13 = 296*A^2 + 18*A + 187,
    R14 = 10*A - 3
  );

  e122_assert(R0 == (4*A^3 + 5*A)*R1 + R2, "17 PRS row 00");
  e122_assert(3*R1 == 2*A*R2 - R3, "17 PRS row 01");
  e122_assert(R2 == 4*A*R3 + R4, "17 PRS row 02");
  e122_assert(R3 == (6*A + 6)*R4 + R5, "17 PRS row 03");
  e122_assert(242*R4 == (22*A - 21)*R5 + R6, "17 PRS row 04");
  e122_assert(R5 == (22*A - 507)*R6 + 726*R7, "17 PRS row 05");
  e122_assert(4225*R6 == (260*A + 6048)*R7 - R8, "17 PRS row 06");
  e122_assert(98*R7 == (455*A + 401)*R8 + 4225*R9, "17 PRS row 07");
  e122_assert(2*R8 == (28*A + 3)*R9 + 49*R10, "17 PRS row 08");
  e122_assert(4*R9 == (8*A - 9)*R10 - R11, "17 PRS row 09");
  e122_assert(25*R10 == (40*A - 13)*R11 + 8*R12, "17 PRS row 10");
  e122_assert(961*R11 == (155*A + 26)*R12 - 25*R13, "17 PRS row 11");
  e122_assert(5476*R12 == (4588*A - 131)*R13 + 961*R14, "17 PRS row 12");
  e122_assert(25*R13 == (740*A + 267)*R14 + 5476, "17 PRS row 13");
};

e122_verify_17() =
{
  my(
    x = 'x,
    detector = [-1, 0, -1, 1, 1, -1, 0, 0, 0, 0, 0, 0, -2, 0, 1],
    pair = e122_pair(17, detector), g = pair[1], u = pair[2],
    nf, th, uu, bb, ell, delta4, p2, p17, rows2, row17,
    g4, u4, H = 1751444197, fd, fdrows, fdell, fdellrows
  );

  e122_assert(poldegree(g) == 17 && poldegree(u) == 14, "17 degrees");
  e122_assert(polisirreducible(Mod(1, 67)*g) == 1, "17 mod-67 irreducibility");
  e122_assert(polisirreducible(g) == 1, "17 irreducibility");
  e122_assert(poldisc(g) == 2^24*17^17, "17 polynomial discriminant");

  nf = nfinit(g);
  e122_assert(nf.index == 1, "17 maximal order");
  e122_assert(nf.disc == 2^24*17^17, "17 field discriminant");
  e122_assert(nf.sign == [1, 8], "17 signature");

  th = Mod(x, g); uu = Mod(u, g); bb = th*uu; ell = -bb/2; delta4 = (4-th)/th;
  e122_assert(polresultant(g, u) == -1, "17 detector resultant");
  e122_assert(nfeltnorm(nf, th) == 2, "17 theta norm");
  e122_assert(nfeltnorm(nf, uu) == -1, "17 detector norm");
  e122_assert(nfeltnorm(nf, bb) == -2, "17 b norm");
  e122_assert(nfeltnorm(nf, ell) == 1/2^16, "17 ell norm");
  e122_assert(matsize(idealfactor(nf, uu))[1] == 0, "17 detector unit");
  e122_assert(idealhnf(nf, bb) == idealhnf(nf, th), "17 detector ideal");
  e122_assert(idealhnf(nf, ell) == idealdiv(nf, idealhnf(nf, bb), idealhnf(nf, 2)), "17 ell ideal relation");
  e122_assert(idealnorm(nf, idealhnf(nf, ell)) == 1/2^16, "17 ell ideal norm");
  fdell = idealfactor(nf, ell); fdellrows = matsize(fdell)[1];
  e122_assert(
    vecsort(vector(fdellrows, i, my(P = fdell[i, 1]); [P.p, P.e, P.f, fdell[i, 2]]))
      == [[2, 2, 4, -2], [2, 2, 4, -2]],
    "17 ell ideal factorisation"
  );

  p2 = idealprimedec(nf, 2);
  rows2 = vector(#p2, i, e122_descriptor(nf, th, bb, delta4, p2[i]));
  e122_assert(
    vecsort(rows2) == [
      [1, 1, 1, 1, 1, 1],
      [2, 4, 0, 0, 0, -1],
      [2, 4, 0, 0, 0, 1]
    ],
    "17 dyadic rows"
  );

  p17 = idealprimedec(nf, 17);
  e122_assert(#p17 == 1, "17 ramified-prime count");
  row17 = e122_descriptor(nf, th, bb, delta4, p17[1]);
  e122_assert(row17 == [17, 1, 0, 0, 0, 1], "17 ramified row");

  g4 = subst(g, x, 4); u4 = subst(u, x, 4);
  e122_assert(g4 == 45537549122, "17 reference norm");
  e122_assert(g4 != 0, "17 x=4 nonbranch");
  e122_assert(nfeltnorm(nf, delta4) == g4/2, "17 delta4 norm scalar");
  e122_assert((g4/2) % 8 == 1, "17 nonzero two-adic source control");
  e122_assert(u4 == 532303029, "17 detector reference");
  e122_assert(isprime(13) && isprime(H), "17 reference primality");
  e122_assert(g4 == 2*13*H, "17 reference factorization");
  e122_assert(kronecker(4*u4, 13) == -1, "17 symbol at 13");
  e122_assert(kronecker(4*u4, H) == 1, "17 symbol at H");

  fd = idealfactor(nf, delta4); fdrows = matsize(fd)[1];
  e122_assert(fdrows == 2, "17 reference support size");
  e122_assert(
    vecsort(vector(fdrows, i, my(P = fd[i, 1]);
      [P.p, P.e, P.f, fd[i, 2], idealval(nf, bb, P),
       nfhilbert(nf, delta4, bb, P)])) == [
      [13, 1, 1, 1, 0, -1],
      [1751444197, 1, 1, 1, 0, 1]
    ],
    "17 reference local rows"
  );
};

e122_verify_41() =
{
  my(
    x = 'x,
    detector = [
      -1, -15, 2, 4, 8, 7, -8, -10, -3, 6, 7, 3, -1, -9,
      3, 7, 2, 3, -9, -6, 1, 8, 4, 1, -4, -6, 3, 7, 0, 2,
      -7, -4, 1, 6, -1, 0, -2, -5, 4, 5, -5
    ],
    pair = e122_pair(41, detector), wrong_pair = e122_pair_wrong_d0(41, detector),
    g = pair[1], u = pair[2], wrong_u = wrong_pair[2],
    nf, th, uu, bb, ell, delta4, p2, p41, rows2, row41,
    g4, u4, H, factors, fd, fdrows, fdell, fdellrows
  );

  e122_assert(poldegree(g) == 41 && poldegree(u) == 40, "41 degrees");
  e122_assert(polisirreducible(Mod(1, 163)*g) == 1, "41 mod-163 irreducibility");
  e122_assert(polisirreducible(g) == 1, "41 irreducibility");
  e122_assert(poldisc(g) == 2^60*41^41, "41 polynomial discriminant");

  nf = nfinit(g);
  e122_assert(nf.index == 1, "41 maximal order");
  e122_assert(nf.disc == 2^60*41^41, "41 field discriminant");
  e122_assert(nf.sign == [1, 20], "41 signature");

  th = Mod(x, g); uu = Mod(u, g); bb = th*uu; ell = -bb/2; delta4 = (4-th)/th;
  e122_assert(polresultant(g, u) == -1, "41 detector resultant");
  e122_assert(nfeltnorm(nf, th) == 2, "41 theta norm");
  e122_assert(nfeltnorm(nf, uu) == -1, "41 detector norm");
  e122_assert(nfeltnorm(nf, bb) == -2, "41 b norm");
  e122_assert(nfeltnorm(nf, ell) == 1/2^40, "41 ell norm");
  e122_assert(matsize(idealfactor(nf, uu))[1] == 0, "41 detector unit");
  e122_assert(idealhnf(nf, bb) == idealhnf(nf, th), "41 detector ideal");
  e122_assert(idealhnf(nf, ell) == idealdiv(nf, idealhnf(nf, bb), idealhnf(nf, 2)), "41 ell ideal relation");
  e122_assert(idealnorm(nf, idealhnf(nf, ell)) == 1/2^40, "41 ell ideal norm");
  fdell = idealfactor(nf, ell); fdellrows = matsize(fdell)[1];
  e122_assert(
    vecsort(vector(fdellrows, i, my(P = fdell[i, 1]); [P.p, P.e, P.f, fdell[i, 2]]))
      == [[2, 2, 10, -2], [2, 2, 10, -2]],
    "41 ell ideal factorisation"
  );

  p2 = idealprimedec(nf, 2);
  rows2 = vector(#p2, i, e122_descriptor(nf, th, bb, delta4, p2[i]));
  e122_assert(
    vecsort(rows2) == [
      [1, 1, 1, 1, 1, 1],
      [2, 10, 0, 0, 0, -1],
      [2, 10, 0, 0, 0, 1]
    ],
    "41 dyadic rows"
  );

  p41 = idealprimedec(nf, 41);
  e122_assert(#p41 == 1, "41 ramified-prime count");
  row41 = e122_descriptor(nf, th, bb, delta4, p41[1]);
  e122_assert(row41 == [41, 1, 0, 0, 0, 1], "41 ramified row");
  e122_assert(Mod(1, 41)*g == Mod(1, 41)*(x-2)^41, "41 ramification polynomial");

  g4 = subst(g, x, 4); u4 = subst(u, x, 4); H = g4/2;
  e122_assert(g4 == 50755107359004694554823202, "41 reference norm");
  e122_assert(g4 != 0, "41 x=4 nonbranch");
  e122_assert(nfeltnorm(nf, delta4) == g4/2, "41 delta4 norm scalar");
  e122_assert((g4/2) % 8 == 1, "41 nonzero two-adic source control");
  e122_assert(u4 == -43956715453803235217163523, "41 detector reference");
  e122_assert(subst(wrong_u, x, 4) == u4 - 1, "41 D0 wrong normalisation value");
  e122_assert(wrong_u != u, "41 D0 wrong normalisation rejected");
  factors = [79, 1373, 115471, 1506563, 1344905911];
  e122_assert(prod(i = 1, #factors, factors[i]) == H, "41 reference factorization");
  for (i = 1, #factors, e122_assert(isprime(factors[i]), "41 factor primality"));

  fd = idealfactor(nf, delta4); fdrows = matsize(fd)[1];
  e122_assert(fdrows == 5, "41 reference support size");
  e122_assert(
    vecsort(vector(fdrows, i, my(P = fd[i, 1]);
      [P.p, P.e, P.f, fd[i, 2], idealval(nf, bb, P),
       nfhilbert(nf, delta4, bb, P)])) == [
      [79, 1, 1, 1, 0, 1],
      [1373, 1, 1, 1, 0, -1],
      [115471, 1, 1, 1, 0, -1],
      [1506563, 1, 1, 1, 0, -1],
      [1344905911, 1, 1, 1, 0, 1]
    ],
    "41 reference local rows"
  );
};

e122_main() =
{
  e122_assert(version() == [2, 17, 3], "PARI version is not 2.17.3");
  e122_verify_outer17_prs();
  e122_verify_17();
  e122_verify_41();
  print(
    "PAPER1_FIXED_FIELD_REPLAY_OK ",
    "pari=2.17.3 ",
    "fields=17,41 prs=outer17 ",
    "provenance=independent-dickson-basis-reconstruction ",
    "brauer_normalisation=ell-norm-ideal-and-local-x4"
  );
};

iferr(e122_main(), E, print("PAPER1_FIXED_FIELD_REPLAY_FAIL: unexpected PARI/GP error"); quit(1));
