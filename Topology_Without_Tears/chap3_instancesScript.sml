open HolKernel Parse boolLib bossLib;
open pred_setTheory topologyTheory;
open chap3Theory chap2Theory;

     
     
val _ = new_theory "chap3_instances";
val _ = augment_srw_ss [realSimps.REAL_ARITH_ss]

Theorem example3_1_12:
  closure euclidean {r| rational r} = UNIV
Proof
 qabbrev_tac ‘Qbar = closure euclidean {r | rational r}’ >>
 CCONTR_TAC >> gs[EXTENSION] >>
 ‘closedSets euclidean Qbar’
   by simp[remark_3_1_10_i,Abbr‘Qbar’] >>
 gs[closed_in] >>
 ‘x ∈ UNIV DIFF Qbar’
  by simp[] >>
 drule_all_then strip_assume_tac $ iffLR open_in_euclidean >>
 gs[ival_def,SUBSET_DEF] >>
 ‘∃q. rational q ∧ a < q ∧ q < b’ by gs[rationals_dense] >>
 ‘q ∉ Qbar’ by simp[] >>
 gs[Abbr‘Qbar’,closure_def]
QED

Theorem exercise_3_2_2ii:
  let A = { x | 0 ≤ x ∧ x < 1 } ;
      B = { x | 1 < x ∧ x ≤ 2 }
  in
    A ⊆ topspace euclidean ∧
    B ⊆ topspace euclidean ∧
    closure euclidean (A ∩ B) ≠ closure euclidean A ∩ closure euclidean B
Proof
  srw_tac[][] >>
  ‘A ∩ B = ∅’ by simp[Abbr‘A’, Abbr‘B’, EXTENSION] >>
  simp[] >>
  ‘1 ∈ closure euclidean A ∧ 1 ∈ closure euclidean B’
    suffices_by (simp[EXTENSION] >> metis_tac[]) >>
  ‘1 ∉ A ∧ 1 ∉ B’ by simp[Abbr‘A’, Abbr‘B’] >>
  simp[closure_def, limpt_thm, open_in_euclidean] >> conj_tac
  >- (qx_gen_tac ‘U’ >> simp[ival_def] >> strip_tac >>
      first_x_assum $ dxrule_then strip_assume_tac >>
      ‘0 ≤ max 0 a ∧ max 0 a < 1’ by (simp[realTheory.max_def] >> rw[]) >>
      dxrule_then strip_assume_tac rationals_dense >>
      rename [‘rational r’] >>
      ‘r ∈ A’  by simp[Abbr‘A’] >>
      ‘r ∈ U’ by (gs[SUBSET_DEF] >> first_x_assum irule >> simp[] >>
                  gs[realTheory.REAL_MAX_LT]) >>
      qexists_tac ‘r’ >> simp[])
  >- (qx_gen_tac ‘U’ >> simp[ival_def] >> strip_tac >>
      first_x_assum $ dxrule_then strip_assume_tac >>
      ‘1 < min 2 b ∧ min 2 b ≤ 2’ by (simp[realTheory.min_def] >> rw[]) >>
      dxrule_then strip_assume_tac rationals_dense >>
      rename [‘rational r’] >>
      ‘r ∈ B’  by simp[Abbr‘B’] >>
      ‘r ∈ U’ by (gs[SUBSET_DEF] >> first_x_assum irule >> simp[] >>
                  gs[realTheory.REAL_LT_MIN]) >>
      qexists_tac ‘r’ >> simp[])
QED



val _ = export_theory();

