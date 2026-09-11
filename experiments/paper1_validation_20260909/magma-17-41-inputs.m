// Archive of recovered original Magma inputs for issue #234.
// NO FURTHER EXECUTION IS REQUESTED. This is an archival container.
// Extract only the bytes between the matching BEGIN/END delimiter lines.
// Delimiters and this header are not part of any original input hash.
// Recovered: 01_17A.m (3732 UTF-8 bytes).
// NOT YET RECOVERED: 02_17B.m, 03_41A.m, 04_41B.m.
// Their reported hashes and complete outputs are in the companion files.
// Source: Define Maths Spine for JNT, assistant message
// 12bedff8-21d2-409b-93d8-8a922e1dc025, turn
// 01e98d2b-4f54-41f7-a820-adc4cfbbc516, original fenced source.
// No script has been reconstructed from a returned transcript.

// BEGIN ORIGINAL FILE 01_17A.m
// E364_17A_v1. Paste this WHOLE file into a fresh calculator box.
// Self-contained fixed-data check; no file input and no unit-group search.
SetAssertions(1);
SetQuitOnError(true);
SetColumns(0);
job := "E364_17A_v1";
vm, vn, vp := GetVersion();
cpu0 := Cputime();
wall0 := Realtime();
printf "START %o magma=V%o.%o-%o\n", job, vm, vn, vp;

ZZ := Integers();
R<x> := PolynomialRing(Rationals());
p := 17;
D := [ R!2, x ];                    // D[i+1] is D_i, with D_0=2.
for n in [2..p] do
    Append(~D, x*D[n] + D[n-1]);
end for;
g := D[p+1] - 2;
U := x^14 + 12*x^12 + 53*x^10 + 102*x^8 + 70*x^6
     - x^5 - 13*x^4 - 4*x^3 - 20*x^2 - 2*x - 3;
assert g eq x^17 + 17*x^15 + 119*x^13 + 442*x^11 + 935*x^9
             + 1122*x^7 + 714*x^5 + 204*x^3 + 17*x - 2;
expectedDisc := 2^24 * 17^17;

assert Degree(g) eq p;
assert Degree(U) eq 14;
assert &and [ Denominator(c) eq 1 : c in Coefficients(g) cat Coefficients(U) ];
print "G_COEFFICIENTS_CONSTANT_FIRST", Coefficients(g);
print "U_COEFFICIENTS_CONSTANT_FIRST", Coefficients(U);

// Exact polynomial bridge, not sampling in A.
f0 := R!1;
f1 := x;
for n in [2..p] do
    f2 := 2*x*f1 + f0;
    f0 := f1;
    f1 := f2;
end for;
assert Evaluate(g, 2*x) eq 2*(f1-1);
print "LUCAS_BRIDGE_OK";

Rq := PolynomialRing(GF(67));
assert IsIrreducible(Rq!g);
printf "IRREDUCIBLE_MOD_%o_OK\n", 67;
printf "START_DISCRIMINANT cpu=%o wall=%o\n", Cputime(cpu0), Realtime(wall0);
actualDisc := ZZ!Discriminant(g);
print "POLYNOMIAL_DISCRIMINANT", actualDisc;
assert actualDisc eq expectedDisc;
assert Resultant(g,U) eq -1;
print "POLYNOMIAL_DISCRIMINANT_AND_RESULTANT_OK";

printf "START_FIELD cpu=%o wall=%o\n", Cputime(cpu0), Realtime(wall0);
F<theta> := NumberField(g);         // Default irreducibility checking stays ON.
assert Degree(F) eq p;
r1, r2 := Signature(F);
assert r1 eq 1 and r2 eq (p-1) div 2;
printf "FIELD_OK signature=(%o,%o) cpu=%o wall=%o\n",
       r1, r2, Cputime(cpu0), Realtime(wall0);

printf "START_UNIT cpu=%o wall=%o\n", Cputime(cpu0), Realtime(wall0);
u := Evaluate(U, theta);
b := theta*u;
ui := u^-1;
assert u*ui eq 1;
// Integral coefficients in the power basis give an explicit integral inverse.
assert &and [ Denominator(c) eq 1 : c in Eltseq(u) ];
assert &and [ Denominator(c) eq 1 : c in Eltseq(ui) ];
Uinverse := R!Eltseq(ui);
assert (U*Uinverse) mod g eq R!1;
assert Norm(theta) eq 2;
assert Norm(u) eq -1;
assert Norm(b) eq -2;
printf "UNIT_OK norms=[2,-1,-2] cpu=%o wall=%o\n",
       Cputime(cpu0), Realtime(wall0);

print "U_INVERSE_COEFFICIENTS_CONSTANT_FIRST", Eltseq(ui);
print "IDEAL_RELATION_DERIVED: b=theta*u with u and u^(-1) integral";

// Reference arithmetic uses supplied prime factors, each checked for primality.
g4 := ZZ!Evaluate(g,4);
u4 := ZZ!Evaluate(U,4);
H := g4 div 2;
assert g4 mod 2 eq 0;
assert g4 eq 45537549122;
assert u4 eq 532303029;
assert H eq 22768774561;
referencePrimes := [13, 1751444197];
assert &and [ IsPrime(q) : q in referencePrimes ];
assert &*referencePrimes eq H;
assert GCD(H,u4) eq 1;
referenceSigns := [ LegendreSymbol(4*u4,q) : q in referencePrimes ];
assert referenceSigns eq [-1, 1];
assert &*referenceSigns eq -1;
assert JacobiSymbol(u4,H) eq -1;
assert JacobiSymbol(4*u4,H) eq -1;
print "REFERENCE_VALUES [g4,U4,b4,H]", [g4,u4,4*u4,H];
print "REFERENCE_PRIMES", referencePrimes;
print "REFERENCE_LEGENDRE_SIGNS", referenceSigns;
print "REFERENCE_JACOBI", JacobiSymbol(4*u4,H);

// Together with signature (1,(p-1)/2), this brackets the unique real root.
assert Evaluate(g,0) eq -2 and g4 gt 0;
print "UNIQUE_REAL_ROOT_IN_(0,4)_OK";
print "NOT_CHECKED_IN_A: maximal order, ideal decomposition, local field Hilbert symbols";
printf "PASS %o cpu=%o wall=%o\n", job, Cputime(cpu0), Realtime(wall0);
quit;
// END ORIGINAL FILE 01_17A.m
