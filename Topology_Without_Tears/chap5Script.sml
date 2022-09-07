open HolKernel Parse boolLib bossLib;

open chap4Theory

val _ = new_theory "chap5";

Theorem lemma5_1_2:
  (∀x. x ∈ topspace τ ⇒ f x ∈ topspace τ') ⇒
  ((∀U. open_in τ' U ⇒ open_in τ (PREIMAGE f U ∩ topspace τ)) ⇔
   ∀a U. a ∈ topspace τ ∧ open_in τ' U ∧ f a ∈ U ⇒
         ∃V. open_in τ V ∧ a ∈ V ∧ IMAGE f V ⊆ U)
Proof
  cheat
QED



val _ = export_theory();
