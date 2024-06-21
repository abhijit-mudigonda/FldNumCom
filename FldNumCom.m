declare type FldNumCom;
declare attributes FldNumCom:
  UnembeddedFld,
  MagmaEmbedding, // One of the outputs of InfinitePlaces(F)
  CConj, // true if the embedding we actually want is the conjugate of the chosen
         // MagmaEmbedding
  Embeds, // This should probably be subsumed by the existing Embeds logic
          // for number fields upon integration into the Magma kernel
  HashableLabel; // This attribute will probably be unnecessary upon
                 // integration into the Magma kernel because they have
                 // their own Embeds logic that's probably better.  

/********************** CONSTRUCTION *************************/

intrinsic cFldNumCom(
  F::Fld : 
  v:=DefaultMarkedEmbedding(F),
  c_conj:=false
  ) -> FldNumCom
  {}
  require Type(F) in [FldRat, FldQuad, FldCyc, FldNum] : "The type of F must be one of\
    FldRat, FldQuad, FldCyc, or FldNum";
  require Type(v) in [Infty, PlcNumElt] : "v must be a place of the rationals\
    or of a number field (Infty or a PlcNumElt).";
  K := New(FldNumCom);
  K`UnembeddedFld := F;
  K`MagmaEmbedding := v;
  K`CConj := c_conj;
  K`Embeds := AssociativeArray();
  K`HashableLabel := <DefiningPolyCoeffs(F), EmbedLabel(v), K`CConj>;
  return K;
end intrinsic;

/********************** MARKED EMBEDDINGS *************************/

intrinsic EvaluateMarkedEmbedding(
    x::FldElt,
    K::FldNumCom :
    Precision:=100
    ) -> FldComElt
  {
    input:
      x - an element of a field
      K - a FldNumCom wrapping the parent field of x
      Precision - precision
    returns:
      the evaluation of x under the marked embedding of K to 
      the precision Precision.
  }
  if K`UnembeddedFld eq Rationals() then
    return ComplexField(Precision)!x;
  end if;

  Precision := Max(Precision, (-1)*Floor(Log(MinDistBtwnRoots(Parent(x)))) + 2);

  if K`CConj then
    return ComplexConjugate(Evaluate(x, K`MagmaEmbedding : Precision:=Precision));
  else
    return Evaluate(x, K`MagmaEmbedding : Precision:=Precision);
  end if;
end intrinsic;

intrinsic DefaultMarkedEmbedding(K::Fld) -> PlcNumElt
  {
    input:
      K: a number field or the rationals
    returns:
      A distinguished infinite place of K.
      By default, this is the first infinite place.

    This function is here so that whenever
    we choose a distinguished place of K,
    we make the same choice. 
  }
  return InfinitePlaces(K)[1];
end intrinsic;

/********************** MAIN OPERATIONS *************************/

intrinsic IsSubfield(K::FldNumCom, L::FldNumCom) -> BoolElt, Map
  {
    input: 
      K - A FldNumCom wrapping the unembedded field K_u
      L - A FldNumCom wrapping the unembedded field L_u
    returns:
      (true, phi) if there is a field embedding phi: K_u -> L_u
        which commutes with the marked embeddings of K_u and L_u
        into the complex numbers given by K and L.
      (false, _) otherwise.
  }
  if IsDefined(K`Embeds, L`HashableLabel) then
    return true, K`Embeds[L`HashableLabel];
  end if;

  b, phi := IsSubfield(K`UnembeddedFld, L`UnembeddedFld);
  if not b then
    return false, _;
  end if;

  K_u := K`UnembeddedFld;
  L_u := L`UnembeddedFld;
  a := PrimitiveElement(K_u);
  test_map := func<
    psi | 
    Abs(EvaluateMarkedEmbedding(a @ psi, L) - EvaluateMarkedEmbedding(a, K)) 
    lt 0.5 * MinDistBtwnRoots(K_u)>;

  if IsGalois(K_u) then
    for aut in Automorphisms(K_u) do
      psi := aut * phi;
      if test_map(psi) then
        K`Embeds[L`HashableLabel] := psi;
        return true, psi;
      end if;
    end for;
    require 0 eq 1 : "Something's gone wrong, one of the automorphisms should've worked.";
  else
    for aut_L in Automorphisms(L_u) do
      psi := phi * aut_L;
      if test_map(psi) then
        K`Embeds[L`HashableLabel] := psi;
        return true, psi;
      end if;
    end for;
  end if;

  return false, _;
end intrinsic;

intrinsic IsCoercible(L::FldNumCom, x::., K::FldNumCom) -> BoolElt, FldElt 
  {
    inputs:
      L - FldNumCom into which x should be coerced
      x - Element to coerce into L, should be one of
            FldNumElt, FldRatElt, FldQuadelt, FldCycElt
      K - FldNumCom which should be viewed as the parent of x
    returns:
      y in L such that the evaluation of y under the marked embedding of L
      is equal to the evaluation of x under the marked embedding of K.

      This is somewhat awkward as written (there shouldn't be a need for an argument
      K, as it should really just be "Parent(x)") because the Parent of a FldNumElt
      is a FldNum (not a FldNumCom) and I didn't want to create a new element type 
      just for the sake of this function. 
  }

  if not Type(x) in [FldNumElt, FldRatElt, FldQuadElt, FldCycElt] then
    return false, _;
  end if;

  if K`UnembeddedFld eq Rationals() then
    return true, (L`UnembeddedFld)!x;
  end if;

  // If L = QQ then all restrictions are the same.
  if L`UnembeddedFld eq Rationals() then
    return true, (L`UnembeddedFld)!x;
  end if;

  b, psi := IsSubfield(K, L);
  if b then
    return true, psi(x);
  end if;

  b1, psi := IsSubfield(L, K);
  if b1 then
    b2, y := HasPreimage(x, psi);
    if b2 then
      return true, y;
    else
      return false, _;
    end if;
  end if;

  // K is neither contained in nor contains L
  return false, _;
end intrinsic;

intrinsic Compositum(K::FldNumCom, L::FldNumCom) -> FldNumCom
  {
    Given two FldNumComs, returns a FldNumCom M whose image under
    its marked embedding contains the images of K and L under their
    respective embeddings.
  }
  composite_flds := CompositeFields(K`UnembeddedFld, L`UnembeddedFld);
  if #composite_flds eq 1 then
    return cFldNumCom(composite_flds[1]);
  else
    // TODO abhijitm this is probably inefficient
    for F in composite_flds do
      for w in InfinitePlaces(F) do
        M := cFldNumCom(F : v:=w);
        if IsSubfield(K, M) and IsSubfield(L, M) then
          return M;
        end if;
      end for;
    end for;
  end if;
end intrinsic;

/********************** MISCELLANY *************************/

intrinsic IsGalois(F::FldAlg) -> BoolElt
  {
    IsNormal fails if the defining polynomial of F has non-integral coefficients.
  }
  coeffs := DefiningPolyCoeffs(F);
  if &and[IsIntegral(a) : a in coeffs] and coeffs[#coeffs] eq 1 then
    return IsNormal(F);
  else
    return #GaloisGroup(F) eq Degree(F);
  end if;
end intrinsic;

intrinsic DefiningPolyCoeffs(K::Fld) -> SeqEnum
  {}
  if K eq Rationals() then
    K := RationalsAsNumberField();
  end if;
  return Coefficients(DefiningPolynomial(K));
end intrinsic;

intrinsic EmbedLabel(v::Any) -> FldComElt 
  {
    Given a number field K and a place v, returns a Gaussian integer 
    key specifying the place by specifying the evaluation of the 
    primitive element under v
  }
  
  require Type(v) in [Infty, PlcNumElt] : "v must be an infinite \
    place of the rationals or of a number field";
  
  // deal with v being the infinite place of the rationals
  if Type(v) eq Infty then
    return ComplexField()!1;
  end if;

  K := NumberField(v);
   
  a := PrimitiveElement(K);
  a_eval := ComplexField()!Evaluate(a, v);
  N := -Floor(Log(MinDistBtwnRoots(K)));
  return Round(10^N * a_eval);
end intrinsic;

intrinsic MinDistBtwnRoots(K::FldNum) -> FldReElt
  {
    Returns the minimum absolute value distance between 
    two roots of the defining polynomial of K.
  }
  f := DefiningPolynomial(K);
  roots := [tup[1] : tup in Roots(ChangeRing(f, ComplexField()))];
  require #roots eq Degree(K) : "Something is wrong,\
    the multiplicity of every root should be one";
  require #roots gt 1 : "This shouldn't get called on the rationals";

  min_dist := Abs(roots[1] - roots[2]);
  for i in [1 .. #roots] do
    for j in [i+1 .. #roots] do
      min_dist := Min(Abs(roots[i] - roots[j]), min_dist);
    end for;
  end for;
  return min_dist;
end intrinsic;
