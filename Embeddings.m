/////////////////////// Embeddings ///////////////////////
// This is basically just a mild extension of the 
// PlcNumElt class, to keep track of the individual 
// embeddings rather than just one per equivalence class.
// 
// To avoid confusion, note that while in standard usage 
// a place is an equivalence class of embeddings, for Magma
// a place is a representative of an equivalence class
// of embeddings. We will use the standard usage in our 
// comments and function names.
//////////////////////////////////////////////////////////

declare type EmbedNumElt;
declare attributes EmbedNumElt:
  Place, // PlcNumElt, an embedding of a number field
  Conj; // Bool, true if the desired embedding is the conjugate
       // of the embedding given by Place.
       
/////////////////////// Constructor ///////////////////////

intrinsic cEmbedNumElt(v::PlcNumElt : conj:=false) -> EmbedNumElt
  {}
  f := New(EmbedNumElt);
  f`Place := v;
  f`Conj := conj;
  // if v is a real place then conj should be false
  assert not IsReal(v) or not conj;
  return f;
end intrinsic;

/////////////////////// Fundamental Intrinsics ///////////////////////

intrinsic Print(f::EmbedNumElt)
  {}
  print f`Place;
  print f`Conj;
end intrinsic;

intrinsic '@'(x::FldNumElt, f::EmbedNumElt) -> FldComElt
  {}
  z := ComplexField()!Evaluate(x, f`Place);
  return (f`Conj) select Conjugate(z) else z;
end intrinsic;

intrinsic 'eq'(f::EmbedNumElt, g::EmbedNumElt) -> BoolElt
  {}
  return (f`Place eq g`Place) and (f`Conj eq g`Conj);
end intrinsic;

/////////////////////// Everything Else ///////////////////////

intrinsic IsReal(f::EmbedNumElt) -> BoolElt
  {}
  return IsReal(f`Place);
end intrinsic;

intrinsic NumberField(f::EmbedNumElt) -> FldNum
  {}
  return NumberField(f`Place);
end intrinsic;

intrinsic Extends(g::EmbedNumElt, f::EmbedNumElt) -> BoolElt
  {
    We don't just use Extends(g`Place, f`Place) because that doesn't keep track of 
    conjugate complex places, Also, it seems to use the embedding given by the ! operator,
    which is not always the same as the embedding provided by the IsSubfield operator
    (e.g. QuadraticField(5) into CyclotomicField(5) exhibits this issue)
    Because the strong coercion logic uses the latter embedding, this function has been 
    written to do so as well.
  }
  L := NumberField(g);
  K := NumberField(f);
  a := PrimitiveElement(K);
  b, phi := IsSubfield(K, L);
  require b : "The number field of f is not a subfield of the number field of g";
  if Abs(g(phi(a)) - f(a)) lt 0.5 * MinDistBtwnRoots(K) then
    return true;
  else 
    return false;
  end if;
end intrinsic;

intrinsic EmbeddingsCC(K::Fld) -> SeqEnum[EmbedNumElt]
  {}
  if not assigned K`Embeddings then
    K`Embeddings := [];
    for v in InfinitePlaces(K) do
      if IsReal(v) then
        Append(~K`Embeddings, cEmbedNumElt(v));
      else
        Append(~K`Embeddings, cEmbedNumElt(v));
        Append(~K`Embeddings, cEmbedNumElt(v : conj:=true));
      end if;
    end for;
  end if;
  return K`Embeddings;
end intrinsic;

intrinsic IsConjugate(f::EmbedNumElt, g::EmbedNumElt) -> BoolElt
  {}
  if IsReal(f) then
    return f`Place eq g`Place;
  else
    return ((f`Place eq g`Place) and (f`Conj ne g`Conj));
  end if;
end intrinsic;

intrinsic Conjugate(f::EmbedNumElt) -> EmbedNumElt
  {}
  if IsReal(f) then
    return f;
  else
    for g in EmbeddingsCC(NumberField(f)) do
      if IsConjugate(f, g) then
        return g;
      end if;
    end for;
    require 0 eq 1 : "Something's gone wrong!";
  end if;
end intrinsic;
