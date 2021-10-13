open HolKernel Parse boolLib bossLib;
open pred_setTheory topologyTheory;
open realTheory chap1Theory chap3Theory chap2Theory;

     
     
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


Theorem lemma_3_3_2:
  ∀A. A ≠ ∅ ∧ (∃b. ∀r. r ∈ A ⇒ r < b) ∧ closed_in euclidean A ==> sup A ∈ A
Proof
  CCONTR_TAC >> gs[closed_in,open_in_euclidean] >>
  last_x_assum (drule_then strip_assume_tac) >>
  gs[SUBSET_DEF] >> rename1 ‘ival u v’ >>
  ‘u < sup A’ by gs[ival_def] >>
  gs[GSYM MEMBER_NOT_EMPTY,IN_DEF] >>
  drule_at (Pos last) (iffRL realTheory.REAL_SUP) >>
  impl_tac >- metis_tac[] >>
  strip_tac >>
  rename[‘A w’, ‘u < sup A’, ‘u < w’, ‘ival u v (sup A)’] >>
  gs[ival_def] >>
  ‘w < v’ suffices_by (strip_tac >> gs[]) >>
  irule realTheory.REAL_LET_TRANS >> qexists_tac ‘sup A’ >> rw[] >>
  irule realTheory.REAL_SUP_UBOUND >> metis_tac[]
QED
        
Theorem open_in_euclidean_UNIV[simp]:
        open_in euclidean UNIV
Proof
rw[open_in_euclidean] >>
qexistsl_tac [‘x - 1’,‘x + 1’] >> simp[ival_def]
QED
        
Theorem prop_3_3_3:
  ∀t. clopen euclidean t ⇔ t = {} ∨ t = UNIV
Proof
  simp[clopen_def,EQ_IMP_THM,OPEN_IN_EMPTY,CLOSED_IN_EMPTY,
       closed_in,DISJ_IMP_THM] >> 
  rpt strip_tac >> CCONTR_TAC >> gs[] >>
  fs[GSYM MEMBER_NOT_EMPTY] >>
  ‘∃z. z IN (UNIV DIFF t)’
    by simp[MEMBER_NOT_EMPTY] >>
  wlog_tac ‘x < z’ [‘x’,‘z’,‘t’] (* 2 *) >-
   (gs[REAL_NOT_LT,REAL_LE_LT] >>
    first_x_assum (qspecl_then [‘z’,‘x’,‘UNIV DIFF t’] mp_tac)>>
    simp[X_DIFF_EQ_X,DIFF_DIFF_SUBSET,DISJOINT_DEF] >>
    strip_tac >> gs[]) >>
  qabbrev_tac ‘s = t INTER {a | x ≤ a ∧ a ≤ z}’ >>
  ‘closed_in euclidean s’
    by (simp[Abbr‘s’] >> irule CLOSED_IN_INTER >>
        simp[closed_is_closed] >> simp[closed_in]) >>
  ‘∀r. r ∈ s ⇒ r < z + 1’
    by simp[Abbr‘s’] >>
  ‘s ≠ {}’ by (simp[GSYM MEMBER_NOT_EMPTY,Abbr‘s’] >>
               qexists_tac ‘x’ >> simp[]) >>
  ‘sup s ∈ s’  
    by metis_tac[lemma_3_3_2] >>
  ‘∀r. r ∈ s ⇒ r ≤ z’
    by simp[Abbr‘s’] >>
  ‘sup s < z’
    by (first_x_assum drule >>
        simp[REAL_LE_LT,DISJ_IMP_THM] >>
        strip_tac >> gs[Abbr‘s’]) >>
  ‘sup s ∈ t’ by gs[Abbr‘s’] >>
  ‘∃a b. sup s ∈ ival a b ∧ ival a b ⊆ t’
    by metis_tac[open_in_euclidean] >>
  ‘∃t0. sup s < t0 ∧ t0 < min b z’
    by (irule REAL_MEAN >> simp[REAL_LT_MIN] >>
        gs[ival_def]) >>
  ‘t0 ∈ t’
    by (gs[SUBSET_DEF] >> first_x_assum irule >>
        gs[ival_def,REAL_LT_MIN]) >>
  ‘t0 ∈ {c | sup s ≤ c ∧ c ≤ z}’
    by gs[REAL_LT_MIN] >>
  ‘x ≤ t0 ∧ t0 ≤ z’
    by (gs[] >> irule REAL_LE_TRANS >>
        qexists_tac ‘sup s’ >> simp[] >>
        irule REAL_SUP_UBOUND >>
        reverse $ rpt conj_tac (* 3 *) >-
        (gs[IN_DEF] >> metis_tac[]) >>
        simp[Abbr‘s’] >> qexists_tac ‘x’ >> simp[])  >>
  ‘t0 ∈ s’
  by simp[Abbr‘s’] >>
  ‘t0 ≤ sup s’
  by (irule REAL_SUP_UBOUND >>
      reverse $ rpt conj_tac (* 3 *) >-
       (gs[IN_DEF] >> metis_tac[]) >-
       (simp[Abbr‘s’] >> qexists_tac ‘x’ >> simp[]) >>
      gs[IN_DEF]) >>
  gs[]
QED
      
 
val _ = export_theory();

