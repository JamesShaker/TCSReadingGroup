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

val _ = export_theory();

