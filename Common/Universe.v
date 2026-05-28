Module Type UniverseSig.
  Parameter U : Set.
  Parameter U_leb : U -> U -> bool.

  Axiom U_leb_total :
    forall a b, U_leb a b = true \/ U_leb b a = true.
  Axiom U_leb_antisymmetric :
    forall a b, U_leb a b = true -> U_leb b a = true -> a = b.
  Axiom U_eq_dec :
    forall a a' : U, { a = a' } + { a <> a'}.
End UniverseSig.
