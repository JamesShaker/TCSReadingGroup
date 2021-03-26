open HolKernel Parse boolLib bossLib;

open chap1Theory pred_setTheory topologyTheory;
     
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


Theorem prop_2_2_8:
  (∃t. topspace t = X ∧ basis B t) ⇔
    BIGUNION B = X ∧
    ∀b1 b2. b1 ∈ B ∧ b2 ∈ B ⇒
            ∃bs. bs ⊆ B ∧ b1 ∩ b2 = BIGUNION bs
Proof
simp[basis_def] >> rw[EQ_IMP_THM] (* 4 *)
>- (first_assum (qspec_then ‘topspace t’ mp_tac) >>
    impl_tac >- simp[] >>
    simp[PULL_EXISTS] >> rpt strip_tac >>
   reverse (rw[SET_EQ_SUBSET])(* 2 *)
    >- (simp[SUBSET_DEF] >> metis_tac[SUBSET_DEF])
    >- (pop_assum (SUBST_ALL_TAC o GSYM) >>
        simp[SUBSET_DEF,PULL_EXISTS] >> rw[] >>
        metis_tac[SUBSET_DEF,OPEN_IN_SUBSET]))
>- metis_tac[OPEN_IN_INTER]
>- 

        
val _ = export_theory();
