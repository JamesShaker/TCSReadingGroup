open HolKernel Parse boolLib bossLib;
open pred_setTheory topologyTheory;
open realTheory chap1Theory chap3Theory chap2_instancesTheory;



val _ = new_theory "chap3_instances";
val _ = augment_srw_ss [realSimps.REAL_ARITH_ss]

Theorem example3_1_12:
  closure euclidean rational = UNIV
Proof
 qabbrev_tac ‘Qbar = closure euclidean rational’ >>
 CCONTR_TAC >> gs[EXTENSION] >>
 ‘closed_in euclidean Qbar’
   by simp[remark_3_1_10_i,Abbr‘Qbar’] >>
 gs[closed_in] >>
 ‘x ∈ UNIV DIFF Qbar’
  by simp[] >>
 drule_all_then strip_assume_tac $ iffLR open_in_euclidean >>
 gs[ival_def,SUBSET_DEF] >>
 ‘∃q. rational q ∧ a < q ∧ q < b’ by gs[rationals_dense] >>
 ‘q ∉ Qbar’ by simp[] >>
 gs[Abbr‘Qbar’,closure_def,IN_DEF]
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



(* definition 4.3.3 *)
Definition interval_def:
  interval (A:real set) ⇔
    ∀x y z. x ∈ A ∧ z ∈ A ∧ x < y ∧ y < z ⇒ y ∈ A
End

Theorem remark_4_3_4i[simp]:
  interval {x}
Proof
  simp[interval_def]
QED

(*
Theorem helpful_lemma:
  ∀A. (∀a. a ∈ A ⇒ ∃b. b ∈ A ∧ a < b) ∨
      sup A ∈ A ∨ sup A ∉ A
Proof
  cheat
QED
*)

Theorem REAL_UBOUND_CASES:
    ∀P. (∀y. ∃x. P x ∧ y < x) ∨
        (¬P (sup P) ∧ ∀x. P x ⇒ x < sup P) ∨
        (P (sup P) ∧ ∀x. P x ⇒ x ≤ sup P)
Proof
    rw[] >> Cases_on ‘∀y. ∃x. P x ∧ y < x’ >> simp[] >> gs[] >>
    ‘∀x. P x ⇒ x ≤ sup P’ by (gs[REAL_NOT_LT,GSYM IMP_DISJ_THM] >>
        rw[] >> metis_tac[REAL_SUP_UBOUND_LE]) >>
    last_x_assum kall_tac >> simp[] >> Cases_on ‘P (sup P)’ >> simp[] >>
    rw[] >> first_x_assum drule >> metis_tac[REAL_LE_LT]
QED

Theorem REAL_LBOUND_CASES:
    ∀P. (∀y. ∃x. P x ∧ x < y) ∨
        (¬P (inf P) ∧ ∀x. P x ⇒ inf P < x) ∨
        (P (inf P) ∧ ∀x. P x ⇒ inf P ≤ x)
Proof
    rw[inf_def] >> qspec_then ‘λr. P (-r)’ assume_tac REAL_UBOUND_CASES >> gs[]
    >| let fun tac_fn (dsj,tm) = dsj >> rw[] >> first_x_assum $ qspec_then tm strip_assume_tac >> gs[]
        in map tac_fn [(DISJ1_TAC,‘-y’),(DISJ2_TAC,‘-x’),(DISJ2_TAC,‘-x’)] end >>
    qexists_tac ‘-x’ >> simp[]
QED

Theorem REAL_LT_SUP:
(∃x. p x) ∧ z < sup p  ⇒ ∃x. p x ∧ z < x
Proof
Cases_on ‘∃z. ∀x. p x ⇒ x ≤ z’ (* 2 *)
>- metis_tac[REAL_SUP_LE] >>
gs[REAL_NOT_LE]
QED

Theorem remark_4_3_4ii:
  interval A ⇔
    (∃a. A = {a}) ∨
    (∃a b. A = { x | a ≤ x ∧ x ≤ b }) ∨
    (∃a b. A = { x | a < x ∧ x < b }) ∨
    (∃a b. A = { x | a ≤ x ∧ x < b }) ∨
    (∃a b. A = { x | a < x ∧ x ≤ b }) ∨
    (∃a.   A = { x | x < a }) ∨
    (∃a.   A = { x | a < x }) ∨
    (∃a.   A = { x | x ≤ a }) ∨
    (∃a.   A = { x | a ≤ x }) ∨
    A = UNIV
Proof
    rw[interval_def, EQ_IMP_THM] >> gvs[] >>
    Cases_on ‘A = ∅’ >- (‘A = {x | 0 < x ∧ x < 0}’ suffices_by metis_tac[] >> gs[EXTENSION]) >>
    gs[GSYM MEMBER_NOT_EMPTY] >> rename [‘a ∈ A’] >>
    map_every (qspec_then ‘A’ assume_tac) [REAL_UBOUND_CASES,REAL_LBOUND_CASES] >> gs[]
    >| let fun tac_fn tm = tm suffices_by simp[SF SFY_ss] in map tac_fn
        [‘A = 𝕌(:real)’,‘A = {x | inf A < x}’,‘A = {x | inf A ≤ x}’,‘A = {x | x < sup A}’,
            ‘A = {x | inf A < x ∧ x < sup A}’,‘A = {x | inf A ≤ x ∧ x < sup A}’,‘A = {x | x ≤ sup A}’,
            ‘A = {x | inf A < x ∧ x ≤ sup A}’,‘A = {x | inf A ≤ x ∧ x ≤ sup A}’] end >>
    rw[EXTENSION] >> gs[IN_APP] >> TRY eq_tac >> rw[] (* 9 *) >>
    metis_tac[REAL_LT_SUP,REAL_INF_LT,REAL_LE_LT]
QED

Theorem better_remark_4_3_4ii:
  interval A ⇔
    (∃a. A = {a}) ∨
    (∃a b. a < b ∧ A = { x | a ≤ x ∧ x ≤ b }) ∨
    (∃a b. a < b ∧ A = { x | a < x ∧ x < b }) ∨
    (∃a b. a < b ∧ A = { x | a ≤ x ∧ x < b }) ∨
    (∃a b. a < b ∧ A = { x | a < x ∧ x ≤ b }) ∨
    (∃a.           A = { x | x < a }) ∨
    (∃a.           A = { x | a < x }) ∨
    (∃a.           A = { x | x ≤ a }) ∨
    (∃a.           A = { x | a ≤ x }) ∨
    A = UNIV ∨ A = ∅
Proof
  simp[remark_4_3_4ii] >> Cases_on ‘A = ∅’ >> simp[]
  >- (disj1_tac >> qexistsl_tac [‘1’, ‘0’] >> simp[EXTENSION]) >>
  Cases_on ‘A = UNIV’ >> simp[] >>
  Q.ASM_CASES_TAC ‘∃a. A = {a}’  >> simp[] >>
  Q.ASM_CASES_TAC ‘∃a. A = {x | x < a}’  >> simp[] >>
  Q.ASM_CASES_TAC ‘∃a. A = {x | x ≤ a}’  >> simp[] >>
  Q.ASM_CASES_TAC ‘∃a. A = {x | a < x}’  >> simp[] >>
  Q.ASM_CASES_TAC ‘∃a. A = {x | a ≤ x}’  >> simp[] >>
  eq_tac >> rw[] >> simp[SF SFY_ss]
  >- (Cases_on ‘a < b’ >- metis_tac[] >>
      gs[] >> Cases_on ‘a = b’
      >- (last_x_assum $ qspec_then ‘a’ mp_tac >>
          simp[EXTENSION]) >>
      gs[EXTENSION])
  >- (Cases_on ‘a < b’ >- metis_tac[] >>
      gs[EXTENSION])
  >- (Cases_on ‘a < b’ >- metis_tac[] >>
      gs[EXTENSION])
  >- (Cases_on ‘a < b’ >- metis_tac[] >>
      gs[EXTENSION]) >>
  metis_tac[]
QED

Theorem open_members_grow_towards_bound:
    open_in euclidean s ∧ a ∈ s ∧ a < b ⇒ ∃c. c ∈ s ∧ a < c ∧ c < b
Proof
    rw[open_in_euclidean] >> last_x_assum drule >> rw[] >> rename [‘ival x y’] >>
    ‘a < min b y’ by (gs[REAL_LT_MIN,ival_def]) >>
    dxrule_then (qx_choose_then ‘r’ strip_assume_tac) REAL_MEAN >> qexists_tac ‘r’ >>
    gs[REAL_LT_MIN,ival_def,SUBSET_DEF]
QED

Theorem interval_thm:
  ∀A. interval A ⇔ ∀x y z. x ∈ A ∧ z ∈ A ∧ x ≤ y ∧ y ≤ z ⇒ y ∈ A
Proof
  metis_tac[interval_def, REAL_LE_LT]
QED

Theorem interval_connected:
  interval xy ⇒ connected (subtopology euclidean xy)
Proof
  CCONTR_TAC >> gs[remark_3_3_9,TOPSPACE_SUBTOPOLOGY,OPEN_IN_SUBTOPOLOGY] >>
  rename [‘t1 ∩ xy ∪ t2 ∩ _’] >>
  ‘(t1 ∪ t2) ∩ xy = xy’
    by (gs[EXTENSION] >> metis_tac[]) >>
  gs[INTER_SUBSET_EQN] >>
  ‘xy ≠ {}’ by (strip_tac >> gvs[]) >>
  ‘∃a b. a ∈ A ∧ b ∈ B’ by metis_tac[MEMBER_NOT_EMPTY] >>
  wlog_tac ‘a < b’ [‘a’,‘b’,‘A’,‘B’,‘t1’,‘t2’]
  >- (‘b ≠ a’ by (strip_tac >> gvs[] >>
                  gs[EXTENSION] >> metis_tac[]) >>
      ‘b < a’ by simp[] >> metis_tac[UNION_COMM,INTER_COMM]) >>
  qabbrev_tac ‘c = sup {x | x ∈ A ∧ x < b}’ >>
  ‘∀y. y ∈ A ∧ y < b ⇒ y ≤ c’
    by (simp[Abbr‘c’] >> rpt strip_tac >> irule REAL_SUP_UBOUND >>
        simp[] >> metis_tac[IN_INTER]) >>
  ‘∀x. (∀y. y ∈ A ∧ y < b ⇒ y ≤ x) ⇒ c ≤ x’
    by (rpt strip_tac >> simp[Abbr‘c’] >>
        irule REAL_IMP_SUP_LE >> simp[] >> metis_tac[IN_INTER]) >>
  ‘a ≤ c’ by simp[] >>
  ‘c ∈ xy’
    by (gs[interval_thm] >> first_x_assum irule >> rw[]
        >- (qexists_tac `a` >> simp[])
        >> qexists_tac `b` >> simp[]) >>
  ‘c ∉ A’
    by (Cases_on ‘c = b’
        >- (gvs[] >> strip_tac >> gvs[EXTENSION] >> metis_tac[])
        >> ‘c < b’
              by (‘c ≤ b’ suffices_by (strip_tac >> simp[]) >> simp[]) >>
        strip_tac >>
        ‘∃d. d ∈ t1 ∧ c < d ∧ d < b’
          by metis_tac[open_members_grow_towards_bound,IN_INTER] >>
        ‘d ∈ xy ∧ d ∈ A’ by metis_tac[interval_def, IN_INTER] >>
        qpat_x_assum ‘c < d’ mp_tac >>
        simp[REAL_NOT_LT]) >>
  ‘c ∈ B’ by (gvs[] >> metis_tac[SUBSET_DEF,IN_UNION]) >>
  ‘c ≤ b’ by simp[] >>
  ‘c ∈ t2’ by metis_tac[IN_INTER] >>
  ‘∃cn cx. c ∈ ival cn cx ∧ ival cn cx ⊆ t2’ by metis_tac[open_in_euclidean] >>
  ‘cn < c ∧ c < cx ∧ ∀x. cn < x ∧ x < cx ⇒ x ∈ t2’
    by gs[ival_def, SUBSET_DEF] >>
  ‘c ≤ cn’ suffices_by simp[] >>
  first_assum irule >>
  qx_gen_tac ‘e’ >> rpt strip_tac >>
  ‘e ≤ c’ by simp[] >>
  CCONTR_TAC >> ‘e ∈ t2’ by simp[] >> metis_tac[NOT_IN_EMPTY, IN_INTER]
QED

Theorem prop_4_3_5:
    connected (subtopology euclidean xy) ⇔ interval xy
Proof
    eq_tac >> simp[interval_connected] >>
    rw[interval_def] >> CCONTR_TAC >>
    qpat_x_assum ‘connected _’ mp_tac >>
    simp[remark_3_3_9,OPEN_IN_SUBTOPOLOGY,TOPSPACE_SUBTOPOLOGY,PULL_EXISTS] >>
    qexistsl_tac [‘{w | w < y}’,‘{w | y < w}’] >>
    rw[EXTENSION]
    >- (simp[REAL_NOT_LT] >> metis_tac[REAL_LE_TOTAL])
    >- (metis_tac[REAL_LT_TOTAL]) >>
    metis_tac[]
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

Theorem connected_euclidean[simp]:
  connected euclidean
Proof
  metis_tac[connected_def, prop_3_3_3, topspace_euclidean]
QED

Theorem dense_rational:
    dense euclidean rational
Proof
    simp[dense_def,example3_1_12]
QED

Theorem separable_euclidean[simp]:
    separable euclidean
Proof
    simp[separable_def] >>
    qexists_tac ‘rational’ >>
    simp[countable_rational,dense_rational]
QED


val _ = export_theory();
