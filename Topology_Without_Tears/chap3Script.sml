open HolKernel Parse boolLib bossLib;
open topologyTheory pred_setTheory
open chap1Theory chap2_2Theory;

val _ = new_theory "chap3";

(* ===============================
     3.1 Limit Points and Closure
   =============================== *)

(* 3.1.1 Definition *)
Theorem limpt_thm:
  ∀t x A.
    limpt t x A ⇔
      x ∈ topspace t ∧
      ∀U. open_in t U ∧ x ∈ U ⇒ ∃y. y ∈ U ∧ y ∈ A ∧ y ≠ x
Proof
  rw[limpt, neigh, PULL_EXISTS] >> EQ_TAC >>
  rw[] >> fs[IN_DEF]
  >- metis_tac[SUBSET_REFL, OPEN_IN_SUBSET]
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

Theorem closed_include_all_limits = prop_3_1_6

Theorem not_limpt_inter:
  ¬limpt t x A ⇔
    x ∉ topspace t ∨ ∃U. x ∈ U ∧ open_in t U ∧ (U ∩ A = {x} ∨ U ∩ A = {})
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

Theorem closure_EMPTY[simp]:
  closure τ ∅ = ∅
Proof
  simp[closure_def, EXTENSION, limpt_thm] >>
  qx_gen_tac ‘a’ >> Cases_on ‘a ∈ topspace τ’ >> simp[] >>
  first_x_assum $ irule_at Any >> simp[OPEN_IN_TOPSPACE]
QED

Theorem closure_EQ_EMPTY[simp]:
  (closure τ A = ∅ ⇔ A = ∅) ∧ (∅ = closure τ A ⇔ A = ∅)
Proof
  simp[EQ_IMP_THM] >> simp[closure_def]
QED

Theorem remark_3_1_10_i:
  A ⊆ topspace t ⇒ closed_in t $ closure t A
Proof
  simp[closure_def, prop_3_1_8]
QED

Definition dense_def:
 dense t A ⇔ closure t A = topspace t
End

Theorem exercise_3_1_5i:
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

Theorem closure_topspace[simp]:
  closure t (topspace t) = topspace t
Proof
  simp [closure_def, EXTENSION, limpt_thm, DISJ_IMP_THM, EQ_IMP_THM]
QED

Theorem prop_3_1_15:
  A ⊆ topspace t ⇒ (dense t A ⇔ ∀ U. open_in t U ∧ U ≠ {} ⇒ U ∩ A ≠ {})
Proof
  rpt strip_tac >> EQ_TAC >> rpt strip_tac
  >- (‘∃x. x ∈ U’ by simp[MEMBER_NOT_EMPTY] >>
      ‘x ∉ A’ by (gs[EXTENSION] >> metis_tac[]) >>
      ‘¬ limpt t x A’ by metis_tac[not_limpt_inter] >>
      gs[dense_def, closure_def] >>
      ‘x ∈ topspace t’ by metis_tac[OPEN_IN_SUBSET,SUBSET_DEF]>>
      gs[EXTENSION] >> metis_tac[])
  >- (Cases_on ‘A = topspace t’
      >- simp[dense_def]
      >- (‘∀x. x ∉ A ∧ x ∈ topspace t ⇒ limpt t x A’ by (
           rpt strip_tac >>
           ‘∀U. x ∈ U ∧ open_in t U ⇒ U ∩ A ≠ {}’ by metis_tac[MEMBER_NOT_EMPTY] >>
           simp[limpt_thm] >> gs[EXTENSION] >> metis_tac[]) >>
          simp [dense_def, closure_def, EXTENSION] >>
          metis_tac[SUBSET_DEF, limpt_thm]))
QED

Theorem dense_nontrivial_inters = prop_3_1_15

Theorem exercise_3_1_5ii:
  s ⊆ t ∧ t ⊆ topspace τ ⇒ closure τ s ⊆ closure τ t
Proof
  simp[closure_def] >> rw[]
  >- gs[SUBSET_DEF]
  >> rw[SUBSET_DEF] >> metis_tac[exercise_3_1_5i]
QED

Theorem closure_monotone = exercise_3_1_5ii

Theorem closure_subset_topspace:
  a ⊆ topspace t ⇒ closure t a ⊆ topspace t
Proof
  rw[closure_def] >> rw[SUBSET_DEF, limpt_thm]
QED

Theorem exercise_3_1_5iii:
  s ⊆ t ∧ t ⊆ topspace τ ∧ dense τ s ⇒ dense τ t
Proof
  rw[dense_def] >>
  drule_all exercise_3_1_5ii >> rw[] >>
  metis_tac[closure_subset_topspace, SUBSET_ANTISYM]
QED

Theorem remark_3_1_10_ii:
  closed_in t B ∧ A ⊆ B ⇒ closure t A ⊆ B
Proof
  rw[prop_3_1_6] >> rw[closure_def, SUBSET_DEF]
  >- gs[SUBSET_DEF]
  >> metis_tac[exercise_3_1_5i]
QED

Theorem remark_3_1_10_iii:
  A ⊆ topspace t ⇒ closure t A = BIGINTER {B | closed_in t B ∧ A ⊆ B}
Proof
  rw[EXTENSION] >> EQ_TAC >> rw[]
  >- (drule_all remark_3_1_10_ii >> rw[] >> gs[SUBSET_DEF])
  >> first_x_assum irule  >> rw[]
  >- rw[closure_def]
  >> metis_tac[remark_3_1_10_i]
QED

(* ====================
    3.2 Neighbourhoods
   ==================== *)

Theorem prop_3_2_6 = limpt

Theorem corollary_3_2_7:
  A ⊆ topspace t ⇒
  (closedSets t A ⇔
     ∀x. x ∈ topspace t ∧ x ∉ A ⇒
         ∃N. neigh t (N,x) ∧ N ⊆ topspace t DIFF A)
Proof
  rw[] >> EQ_TAC >> rw[]
  >- (fs[prop_3_1_6, limpt] >> first_x_assum drule >> rw[] >>
      qexists_tac `N` >> simp[SUBSET_DEF] >> rw[]
      >- gs[neigh, SUBSET_DEF] >>
      gs[IN_DEF] >> metis_tac[]) >>
  simp[prop_3_1_6, limpt] >> rpt strip_tac >>
  rename [‘a ∈ topspace τ’, ‘A ⊆ topspace τ’] >>
  CCONTR_TAC >> first_x_assum $ drule_all_then strip_assume_tac >>
  first_x_assum $ drule_all_then strip_assume_tac >>
  qpat_x_assum ‘N ⊆ topspace τ DIFF A’ mp_tac >>
  simp[SUBSET_DEF, IN_DEF] >> metis_tac[]
QED

Theorem corollary_3_2_8:
  U ⊆ topspace τ ⇒
  (open_in τ U ⇔ ∀x. x ∈ U ⇒ ∃N. neigh τ (N,x) ∧ N ⊆ U)
Proof
  strip_tac >>
  ‘topspace τ DIFF U ⊆ topspace τ’
    by gs[SUBSET_DEF] >>
  drule corollary_3_2_7 >>
  simp[closed_in, DIFF_DIFF_SUBSET] >> strip_tac >>
  simp[SF CONJ_ss] >> gs[SUBSET_DEF] >> simp[SF CONJ_ss]
QED

Theorem corollary_3_2_9:
  U ⊆ topspace τ ⇒
  (open_in τ U ⇔ ∀x. x ∈ U ⇒ ∃V. open_in τ V ∧ x ∈ V ∧ V ⊆ U)
Proof
  strip_tac >> simp[corollary_3_2_8, neigh] >>
  simp[PULL_EXISTS] >> drule_at_then (Pos last) assume_tac SUBSET_TRANS >>
  simp[SF CONJ_ss] >> simp[IN_DEF] >> metis_tac[SUBSET_REFL, SUBSET_TRANS]
QED

Theorem exercise_3_2_2i:
  A ⊆ topspace τ ∧ B ⊆ topspace τ ⇒
  closure τ (A ∩ B) ⊆ closure τ A ∩ closure τ B
Proof
  strip_tac >>
  simp[closure_def, SUBSET_DEF] >> rw[] >> simp[] >> (* 2 *)
  metis_tac[INTER_SUBSET, exercise_3_1_5i]
QED

Theorem exercise_3_2_2ii:
  let τ = indiscrete_topology {T;F};
      A = {T} ;
      B = {F}
  in
    A ⊆ topspace τ ∧ B ⊆ topspace τ ∧
    closure τ (A ∩ B) ≠ closure τ A ∩ closure τ B
Proof
  srw_tac[][]
  >- simp[Abbr‘A’, Abbr‘B’, Abbr‘τ’]
  >- simp[Abbr‘A’, Abbr‘B’, Abbr‘τ’] >>
  ‘A ∩ B = ∅’ by simp[Abbr‘B’, Abbr‘A’, EXTENSION] >>
  ‘closure τ A = {T;F} ∧ closure τ B = {T;F}’
    suffices_by simp[] >>
  ‘A ⊆ topspace τ ∧ B ⊆ topspace τ’ by simp[Abbr‘τ’, Abbr‘A’, Abbr‘B’] >>
  ‘closed_in τ (closure τ A) ∧ closed_in τ (closure τ B)’
    by metis_tac[remark_3_1_10_i] >>
  gs[Abbr‘τ’] >> gs[Abbr‘A’, Abbr‘B’]
QED



val _ = export_theory();
