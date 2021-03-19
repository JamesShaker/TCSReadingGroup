open HolKernel Parse boolLib bossLib;

val _ = new_theory "chap2_2";

(* definition 2.2.2 *)
Definition basis_def:
  basis B t ⇔
    (∀s. s ∈ B ⇒ open_in t s) ∧
    (∀s. open_in t s ⇒ ∃u. u ⊆ B ∧ s = BIGUNION u)
End

Theorem example2_2_4:
  basis { {x} | x ∈ X } (discrete_topology X)
Proof
  simp[basis_def, PULL_EXISTS] >> rpt strip_tac >>
  (* could supposedly appeal to prop1_1_9 here *)
  qexists_tac ‘{{x} | x ∈ s}’ >> gs[SUBSET_DEF, PULL_EXISTS] >>
  simp[Once EXTENSION, PULL_EXISTS]
QED

Theorem remark2_2_6:
  basis B t ∧ B ⊆ B1 ∧ (∀s. s ∈ B1 ⇒ open_in t s) ⇒
  basis B1 t
Proof
  simp[basis_def] >> rpt strip_tac >>
  metis_tac[SUBSET_TRANS]
QED

val _ = export_theory();
