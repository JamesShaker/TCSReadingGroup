open HolKernel Parse boolLib bossLib;
open topologyTheory pred_setTheory
open chap1Theory chap2_2Theory;

val _ = new_theory "chap3";

(* 3.1.1 Definition *)
Theorem limpt_thm:
  ∀t x A.
    limpt t x A ⇔
      x ∈ topspace t ∧
      ∀U. open_in t U ∧ x ∈ U ⇒ ∃y. y ∈ U ∧ y ∈ A ∧ y ≠ x
Proof
  rw[limpt, neigh, PULL_EXISTS] >> EQ_TAC >>
  rw[] >> fs[IN_DEF]
  >- metis_tac[SUBSET_REFL]
  >> metis_tac[SUBSET_DEF, IN_DEF]
QED

Theorem example_3_1_3:
  ∀A X.
    A ⊆ X ⇒ ∀x. x ∈ X ⇒ ¬limpt (discrete_topology X) x A
Proof
  rw[limpt_thm] >> qexists_tac `{x}` >> rw[]
QED

(* skipped example 3.1.4: it talks about real numbers *)

Theorem example_3_1_5:
  A ⊆ X ∧ u ∈ A ∧ A ≠ {u} ⇒
  ∀x. x ∈ X ⇒ limpt (indiscrete_topology X) x A
Proof
  rw[limpt_thm] >> fs[] >>
  Cases_on `u = x` >> rw[]
  >- (`∃y. y ∈ A ∧ y ≠ u`
         suffices_by metis_tac[SUBSET_DEF] >>
        CCONTR_TAC >> fs[] >>
        qpat_x_assum `A ≠ {u}` mp_tac >> simp[] >>
        rw[EXTENSION] >> metis_tac[])
  >> metis_tac[SUBSET_DEF]
QED

Theorem prop_3_1_6:
 closed_in t A ⇔ A ⊆ topspace t ∧ ∀x. limpt t x A ⇒ x ∈ A
Proof
  rw[closed_in, limpt_thm] >> EQ_TAC >> rw[]
  >- (CCONTR_TAC >>
      first_x_assum drule >> rw[] >>
      metis_tac[])
  >> ‘∀x. x ∉ A ∧ x ∈ topspace t ⇒
          ∃U. open_in t U ∧ x ∈ U ∧ (∀y. y ∈ U ∧ y ≠ x ⇒ y ∉ A)’
    by metis_tac[] >>
  gs[SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
  ‘topspace t DIFF A = BIGUNION {f x | x ∉ A ∧ x ∈ topspace t}’
    by (rw[Once EXTENSION, PULL_EXISTS] >> EQ_TAC
        >- metis_tac[]
        >> rw[]
        >- (first_x_assum drule_all >> rw[] >>
            metis_tac[OPEN_IN_SUBSET, SUBSET_DEF])
        >> metis_tac[]) >>
  simp[] >> irule OPEN_IN_BIGUNION >>
  rw[] >> metis_tac[]
QED

Theorem not_limpt_inter:
  ¬limpt t x A ⇔ x ∉ topspace t ∨ ∃U. open_in t U ∧ (U ∩ A = {x} ∨ U ∩ A = {}) ∧ x ∈ U  
Proof
  simp [limpt_thm, EXTENSION] >> metis_tac[]
QED
        
Theorem prop_3_1_8:
  A ⊆ topspace t ⇒ closed_in t (A ∪ {a | limpt t a A})
Proof
  rpt strip_tac >> irule (iffRL prop_3_1_6) >> reverse CONJ_TAC
  >- gs[SUBSET_DEF, limpt_thm] >> 
  CCONTR_TAC >> gs[] >> ‘x ∈ topspace t’ by metis_tac[limpt_thm] >> 
  gs[not_limpt_inter]
  >- (gs [EXTENSION] >> metis_tac[]) >>
  qabbrev_tac ‘A' = {a | limpt t a A}’ >> 
  ‘U ∩ A' = {}’ by
    (simp[EXTENSION, Abbr ‘A'’] >> simp[not_limpt_inter] >> 
         metis_tac[]) >>
  ‘U ∩ (A ∪ A') = {}’ by simp[UNION_OVER_INTER] >>
  metis_tac[not_limpt_inter]                
QED

Definition closure_def:
  closure t A = A ∪ {a | limpt t a A}
End

Theorem remark_3_1_10_i:
  A ⊆ topspace t ⇒ closed_in t $ closure t A 
Proof
  simp[closure_def, prop_3_1_8]
QED

Definition dense_def:
 dense t A ⇔ closure t A = topspace t
End

Theorem excercise_3_1_5i:
 s ⊆ t ∧ t ⊆ topspace τ ∧ limpt τ p s ⇒ limpt τ p t
Proof
 simp[limpt_thm] >> metis_tac[SUBSET_DEF]
QED

Theorem closure_of_closed:
 closed_in τ A ⇒ closure τ A = A
Proof
 simp[prop_3_1_6,closure_def] >> rpt strip_tac >>
 simp[EXTENSION,EQ_IMP_THM,DISJ_IMP_THM]
QED

Theorem example_3_1_14:
  dense (discrete_topology X) A ⇔ A = X
Proof  
 simp[dense_def] >> eq_tac (* 2 *) >-
 (strip_tac >> Cases_on ‘A ⊆ X’ (* 2 *)
  >- (‘closed_in (discrete_topology X) A’
        by simp[] >>
      metis_tac[closure_of_closed]) >>
  gs[closure_def,SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
 simp[closure_of_closed]
QED
                  
val _ = export_theory();
