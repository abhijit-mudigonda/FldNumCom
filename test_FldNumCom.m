AttachSpec("spec");

CC_THRESHOLD := 10^-10;

procedure test(a, K1, K2)
  // a::FldElt
  // K1::FldNumCom
  // K2::FldNumCom

  able, b := IsCoercible(K2, a, K1); 
  a_eval := EvaluateMarkedEmbedding(a, K1);
  b_eval := EvaluateMarkedEmbedding(b, K2);
  assert Abs(a_eval - b_eval) lt CC_THRESHOLD;
  _, c := IsCoercible(K1, b, K2);
  assert c eq a;
end procedure;

// These are all Galois fields
Q := Rationals();
Q_emb := cFldNumCom(Q);
F := QuadraticField(5);
F_emb := cFldNumCom(F);
R<x> := PolynomialRing(Rationals());
K := NumberField(x^3 - x^2 - 2*x + 1);
K_emb := cFldNumCom(K);
L := CyclotomicField(5);
L_emb := cFldNumCom(L);
FL_emb := Compositum(F_emb, L_emb);
KL_emb := Compositum(K_emb, L_emb);

// FldRat <-> FldRat
test(163/1729, Q_emb, Q_emb);

// FldRat <-> FldQuad
test(163/1729, Q_emb, F_emb);

// FldRat <-> FldCyc
test(163/1729, Q_emb, L_emb);

// FldQuad <-> FldNum
test(163 + 1729*F.1, F_emb, FL_emb);

// FldQuad <-> FldCyc
// TODO abhijitm we omit this test for now because if x is in K
// and L is a cyclotomic field containing K, then
// L!x will succeed but K!(L!x) will fail

// FldCyc <-> FldNum
test(16 + 3*L.1 + 17*L.1^2 + 2*L.1^3 + 9*L.1^4, L_emb, KL_emb);

// FldNum <-> FldNum
test(163 + 17*K.1 + 29*K.1^2, K_emb, KL_emb);

// non-Galois <-> Galois
R<x> := PolynomialRing(Rationals());
K := NumberField(x^3-2);
L := SplittingField(K);
L_emb := cFldNumCom(L);
vs := InfinitePlaces(K);
w := DefaultMarkedEmbedding(L);
for v in vs do
  for c_conj in [true, false] do
    K_emb := cFldNumCom(K : v:=v, c_conj:=c_conj);
    test(K.1 - 3, K_emb, L_emb);
  end for;
end for;

// Galois <-> non-Galois
F := QuadraticField(5);
F_emb := cFldNumCom(F);
R<x> := PolynomialRing(F);
K_rel := ext<F | x^2 + 1/22*(3*F.1 + 23)>;
K := AbsoluteField(K_rel);
for v in InfinitePlaces(K) do
  for c_conj in [true, false] do
    K_emb := cFldNumCom(K : v:=v); 
    test(F.1, F_emb, K_emb);
  end for;
end for;

// non-Galois <-> non-Galois
R<x> := PolynomialRing(Rationals());
K := NumberField(x^3-2);
S<y> := PolynomialRing(K);
L_rel := ext<K | y^3 - (3+K.1-K.1^2)>;
L := AbsoluteField(L_rel);
assert not IsGalois(L);

_, phi := IsSubfield(K, L);

for v in InfinitePlaces(K) do
  for w_e in Decomposition(phi, v) do
    for c_conj in [true, false] do
      w := w_e[1];
      K_emb := cFldNumCom(K : v:=v, c_conj:=c_conj);
      L_emb := cFldNumCom(L : v:=w, c_conj:=c_conj);
      test(K.1, K_emb, L_emb);
    end for;
  end for;
end for;

// compositum of Q(cbrt(2)) with a different Q(cbrt(2))
K := NumberField(x^3-2);
vs := InfinitePlaces(K);
assert IsReal(vs[1]);
K_emb := cFldNumCom(K : v:=vs[1]);
L_emb := cFldNumCom(K : v:=vs[2]);
M_emb := cFldNumCom(K : v:=vs[2], c_conj:=true);
KK_emb := Compositum(K_emb, K_emb);
LL_emb := Compositum(L_emb, L_emb);
KL_emb := Compositum(K_emb, L_emb);
KM_emb := Compositum(K_emb, M_emb);
KK := KK_emb`UnembeddedFld;
LL := LL_emb`UnembeddedFld;
KL := KL_emb`UnembeddedFld;
KM := KM_emb`UnembeddedFld;

assert IsIsomorphic(K, KK);
assert IsIsomorphic(K, LL);
assert IsIsomorphic(KL, NormalClosure(K));
assert IsIsomorphic(KM, KL);

print "Success!";
