open HolKernel Parse boolLib bossLib;

open pred_setTheory topologyTheory
open chap1Theory chap2Theory chap4Theory chap3Theory chap3_instancesTheory
open realTheory RealArith;
val _ = new_theory "chap4_instances";

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss]

Theorem open_in_euclidean_UNIV[simp]:
  open_in euclidean UNIV
Proof
  ‘UNIV = topspace euclidean’
    suffices_by simp[OPEN_IN_TOPSPACE, Excl "topspace_euclidean"] >>
  simp[]
QED

Definition ints_def:
  ints = { real_of_int i | T }
End

Theorem ints_NEQ_EMPTY[simp]:
  ints ≠ ∅
Proof
  simp[EXTENSION, ints_def]
QED

Theorem ints_NEQ_singleton[simp]:
  ints ≠ {i}
Proof
  simp[EXTENSION, ints_def, EQ_IMP_THM, PULL_EXISTS, SF DNF_ss] >>
  rw[] >> rename [‘_ = i’] >> qexists_tac ‘i + 1’ >> simp[]
QED

Theorem example_4_1_6:
  subtopology euclidean ints = discrete_topology ints
Proof
  irule chap1Theory.prop1_1_9' >>
  simp[TOPSPACE_SUBTOPOLOGY, OPEN_IN_SUBTOPOLOGY] >> rpt strip_tac >>
  rename [‘i ∈ ints’] >> qexists_tac ‘ival (i-1) (i+1)’ >>
  simp[open_in_euclidean] >>
  simp[EXTENSION, ival_def, EQ_IMP_THM] >>
  gvs[ints_def, PULL_EXISTS, real_of_int_subN, Excl "real_of_int_sub",
      real_of_int_addN, Excl "real_of_int_add"] >>
  intLib.ARITH_TAC
QED

Theorem PREIMAGE_BIJ_LINV:
  BIJ f s t ⇒ t ⊆ PREIMAGE (LINV f s) s
Proof
 rw[SUBSET_DEF] >>
 drule (BIJ_DEF |> iffLR |> cj 1) >> rw[] >>
 drule_then strip_assume_tac LINV_DEF >>
 metis_tac[BIJ_DEF, SURJ_DEF]
QED

Theorem exercise_4_1_9:
  ∃τ A. connected τ ∧ ¬connected (subtopology τ (A:real set))
Proof
  qexistsl_tac [‘euclidean’, ‘ints’] >>
  simp[example_4_1_6, example_3_3_6]
QED

Theorem inverses_monotone:
  BIJ f s t ∧
  (∀x:real y. x ∈ s ∧ y ∈ s ∧ x < y ⇒ f x:real < f y) ⇒
  (∀u v. u ∈ t ∧ v ∈ t ∧ u < v ⇒ LINV f s u < LINV f s v)
Proof
  rw[] >> CCONTR_TAC >>
  drule_then strip_assume_tac (BIJ_DEF |> iffLR |> cj 1) >>
  drule_then assume_tac LINV_DEF >>
  gs[REAL_NOT_LT] >>
  ‘SURJ f s t’ by gs[BIJ_DEF] >>
  ‘∃v0 u0. u0 ∈ s ∧ v0 ∈ s ∧ f u0 = u ∧ f v0 = v’
    by metis_tac[SURJ_DEF] >> gvs[] >>
  gvs[REAL_LE_LT] >> metis_tac[REAL_LT_TRANS, REAL_LT_REFL]
QED

Theorem prop2_2_1_euclidean_ival_subtop:
  open_in euclidean (t ∩ ival a b) ⇒
  ∃OIS. t ∩ ival a b = BIGUNION { ival x y | a < x ∧ x < y ∧ y < b ∧ OIS x y}
Proof
  strip_tac >>
  Cases_on ‘t ∩ ival a b = ∅’ >- (qexists_tac ‘λx y. F’ >> simp[]) >>
  ‘a < b’ by (CCONTR_TAC >> gs[ival_def]) >>
  drule_then (qx_choose_then ‘P’ assume_tac) (iffLR prop2_2_1) >>
  ‘∃P0. BIGUNION {ival a b | P a b} =
        BIGUNION {ival a b | (a,b) ∈ P0} ∧ (∀a b. (a,b) ∈ P0 ⇒ a < b ∧ P a b)’
    by (qexists_tac ‘{(a,b) | a < b ∧ P a b}’ >>
        simp[Once EXTENSION, ival_def, PULL_EXISTS, EQ_IMP_THM,
             FORALL_AND_THM] >> rpt strip_tac >>
        rpt $ first_assum $ irule_at Any >> simp[]) >>
  gs[] >>
  qabbrev_tac ‘ivals = {ival a b | (a,b) ∈ P0}’ >>
  ‘∃LB MID UB.
     (∀x. x ∈ LB ⇒ x ≤ b) ∧
     (∀y. y ∈ UB ⇒ a < y) ∧
     (∀x y. (x,y) ∈ MID ⇒ a < x ∧ x < y ∧ y < b) ∧
     ∀c d.
       (c,d) ∈ P0 ⇔ c = a ∧ d ∈ LB ∨
                    (c,d) ∈ MID ∨
                    c ∈ UB ∧ d = b’
    by (qexistsl_tac [‘{ d | (a,d) ∈ P0}’,
                      ‘{(c,d) | a < c ∧ d < b ∧ (c,d) ∈ P0}’,
                      ‘{ c | (c, b) ∈ P0 ∧ c ≠ a }’] >> simp[] >>
        rpt strip_tac
        >- (rename [‘(a,x) ∈ P0’] >>
            ‘ival a x ∈ ivals’ by (simp[Abbr‘ivals’] >> irule_at Any EQ_REFL >>
                                   simp[]) >>
            ‘ival a x ⊆ ival a b’
              by metis_tac[SUBSET_BIGUNION_I, SUBSET_INTER] >> gs[])
        >- (rename [‘(y,b) ∈ P0’] >>
            ‘ival y b ∈ ivals’ by (simp[Abbr‘ivals’] >> irule_at Any EQ_REFL >>
                                   simp[]) >>
            ‘ival y b ⊆ ival a b’
              by metis_tac[SUBSET_BIGUNION_I, SUBSET_INTER] >> gs[]) >>
        rename [‘(c,d) ∈ P0’] >> eq_tac >> strip_tac >> simp[] >>
        Cases_on ‘c = a’ >> gs[] >>
        Cases_on ‘d = b’ >> gs[] >> simp[SF CONJ_ss] >>
        ‘ival c d ∈ ivals’ by (simp[Abbr‘ivals’] >> irule_at Any EQ_REFL >>
                               simp[]) >>
        ‘ival c d ⊆ ival a b’ by metis_tac[SUBSET_INTER, SUBSET_BIGUNION_I] >>
        gs[] >> first_x_assum drule >> simp[]) >>
  Cases_on ‘b ∈ LB’
  >- (qexists_tac ‘λa0 b0. a < a0 ∧ a0 < b0 ∧ b0 < b’ >>
      simp[SF CONJ_ss] >> simp[Once EXTENSION, PULL_EXISTS, Abbr‘ivals’] >>
      rw[EQ_IMP_THM]
      >- (rename [‘x ∈ ival a c’] >>
          qexistsl_tac [‘(a + x) / 2’, ‘(x + c) / 2’] >> gs[ival_def] >>
          irule (REAL_ARITH “x < c ∧ c ≤ b ⇒ x + c < 2r * b”) >> simp[])
      >- metis_tac[]
      >- (rename [‘x ∈ ival c d’, ‘c ∈ UB’] >>
          qexistsl_tac [‘(c + x) / 2’, ‘(x + d) / 2’] >> gs[ival_def] >>
          irule (REAL_ARITH “a < c ∧ c < x ⇒ 2r * a < c + x”) >> simp[]) >>
      rename [‘x ∈ ival c d’, ‘a < c’, ‘c < d’, ‘d < b’] >>
      qexistsl_tac [‘a’, ‘b’] >> gs[ival_def]) >>
  ‘ivals = {ival a x | x ∈ LB} ∪ {ival x y | (x,y) ∈ MID} ∪ {ival y b | y ∈ UB}’
    by (simp[Abbr‘ivals’, Once EXTENSION] >> rw[EQ_IMP_THM] >> metis_tac[]) >>
  simp[BIGUNION_UNION] >>
  ‘∃LB2. BIGUNION {ival a x | x ∈ LB} = BIGUNION {ival x y | (x,y) ∈ LB2 } ∧
         ∀x y. (x,y) ∈ LB2 ⇒ a < x ∧ x < y ∧ y < b’
    by (qexists_tac
          ‘BIGUNION (IMAGE (λx. { (a0, x) | a0 | a < a0 ∧ a0 < x }) LB)’ >>
        simp[PULL_EXISTS] >> reverse conj_tac >- metis_tac[REAL_LE_LT] >>
        simp[ival_def, Once EXTENSION, PULL_EXISTS] >> rw[EQ_IMP_THM]
        >- (first_assum $ irule_at (Pat ‘_ ∈ LB’) >> simp[SF CONJ_ss] >>
            metis_tac[REAL_MEAN]) >>
        metis_tac[REAL_LT_TRANS]) >>
  simp[] >>
  ‘∃UB2. BIGUNION {ival x b | x ∈ UB} = BIGUNION {ival x y | (x,y) ∈ UB2 } ∧
         ∀x y. (x,y) ∈ UB2 ⇒ a < x ∧ x < y ∧ y < b’
    by (qexists_tac
          ‘BIGUNION (IMAGE (λy. { (y,b0) | b0 | y < b0 ∧ b0 < b }) UB)’ >>
        simp[PULL_EXISTS] >>
        simp[ival_def, Once EXTENSION, PULL_EXISTS] >> rw[EQ_IMP_THM]
        >- (first_assum $ irule_at (Pat ‘_ ∈ UB’) >> simp[SF CONJ_ss] >>
            metis_tac[REAL_MEAN]) >>
        metis_tac[REAL_LT_TRANS]) >>
  simp[] >>
  qexists_tac ‘λa b. (a,b) ∈ LB2 ∪ MID ∪ UB2’ >>
  simp[Once EXTENSION, PULL_EXISTS] >> rw[EQ_IMP_THM] >> metis_tac[]
QED

Theorem example_4_2_4:
  a < b ∧ c < d ⇒
  ∃f g.  homeomorphism (subtopology euclidean (ival a b),
                        subtopology euclidean (ival c d)) (f,g)
Proof
  ‘∀a b. a < b ⇒
         ∃f g.homeomorphism(subtopology euclidean (ival a b),
                            subtopology euclidean (ival 0 1)) (f,g)’
    suffices_by
    (rpt strip_tac >> rpt $ first_assum dxrule >>
     metis_tac[homeomorphism_SYM,homeomorphism_TRANS]) >>
  rpt strip_tac >>
  qabbrev_tac ‘g = λx. a * (1 - x) + b * x’ >>
  ‘∀x1 x2. x1 < x2 ⇒ g x1 < g x2’
   by
    (rpt strip_tac >>
     rw[Abbr‘g’,REAL_SUB_LDISTRIB,
        REAL_ARITH “x - y + z < x - y'+ z' ⇔ z - y < z' - y':real”] >>
     rw[GSYM REAL_SUB_RDISTRIB]) >>
  qabbrev_tac ‘g' = λy. (y - a) / (b - a)’ >>
  ‘∀x. g (g' x) = x ∧ g' (g x) = x’
    by (rw[Abbr‘g’, Abbr‘g'’, REAL_SUB_LDISTRIB]
        >- (irule REAL_EQ_LMUL_IMP >> qexists_tac ‘b-a’ >>
            REWRITE_TAC[REAL_SUB_LDISTRIB, REAL_LDISTRIB, REAL_RDISTRIB] >>
            simp[] >> simp[REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB]) >>
        simp[real_div]) >>
  ‘g 0 = a ∧ g 1 = b ∧ g' a = 0 ∧ g' b = 1’
    by simp[Abbr‘g’, Abbr‘g'’, REAL_DIV_REFL] >>
  ‘∀x y. x < y ⇒ g' x < g' y’ by simp[Abbr‘g'’] >>
  ‘(∀x. 0 < x ∧ x < 1 ⇒ a < g x ∧ g x < b) ∧
   (∀y. a < y ∧ y < b ⇒ 0 < g' y ∧ g' y < 1)’
    by metis_tac[] >>
  qexistsl_tac [‘g'’,‘g’] >>
  ‘BIJ g (ival 0 1) (ival a b)’
    by (simp[BIJ_IFF_INV, ival_def] >> qexists_tac ‘g'’ >> simp[]) >>
  simp[homeomorphism, TOPSPACE_SUBTOPOLOGY] >> rpt strip_tac (* 3 *)
  >- (simp[BIJ_IFF_INV, ival_def] >> metis_tac[])
  >- (gs[OPEN_IN_SUBTOPOLOGY] >>
      qexists_tac ‘IMAGE g (t ∩ ival 0 1)’ >>
      reverse conj_tac
      >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> simp[INTER_SUBSET_EQN] >>
          simp[SUBSET_DEF, PULL_EXISTS, ival_def]) >>
      rename [‘tt = t ∩ ival 0 1’] >>
      ‘open_in euclidean tt’ by (simp[] >> irule OPEN_IN_INTER >> simp[]) >>
      rw[] >>
      drule_then strip_assume_tac prop2_2_1_euclidean_ival_subtop >>
      ‘∀c d. 0 < c ∧ c < d ∧ d < 1 ⇒
             IMAGE g (ival c d) = ival (g c) (g d)’
        by (simp[EXTENSION, PULL_EXISTS, EQ_IMP_THM, ival_def] >> metis_tac[])>>
      simp[IMAGE_BIGUNION] >> irule OPEN_IN_BIGUNION >>
      simp[PULL_EXISTS]) >>
  gs[OPEN_IN_SUBTOPOLOGY] >>
  qexists_tac ‘IMAGE g' (t ∩ ival a b)’ >>
  reverse conj_tac
  >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> simp[INTER_SUBSET_EQN] >>
      simp[SUBSET_DEF, PULL_EXISTS, ival_def]) >>
  rename [‘tt = t ∩ ival a b’] >>
  ‘open_in euclidean tt’ by (simp[] >> irule OPEN_IN_INTER >> simp[]) >>
  qpat_x_assum ‘tt = _’ SUBST_ALL_TAC >>
  drule_then strip_assume_tac prop2_2_1_euclidean_ival_subtop >>
  ‘∀c d. a < c ∧ c < d ∧ d < b ⇒
         IMAGE g' (ival c d) = ival (g' c) (g' d)’
    by (simp[EXTENSION, PULL_EXISTS, EQ_IMP_THM, ival_def] >> metis_tac[])>>
  simp[IMAGE_BIGUNION] >> irule OPEN_IN_BIGUNION >>
  simp[PULL_EXISTS]
QED

Theorem example_4_2_5:
  homeomorphism (euclidean, subtopology euclidean (ival (-1) 1))
    ((λx. x / (abs x + 1)), (λx. x / (1 - abs x)))
Proof
  qmatch_abbrev_tac ‘homeomorphism _ (f,g)’ >>
  ‘∀x. g (f x) = x’
    by (simp[Abbr‘g’, Abbr‘f’, real_div, ABS_MUL] >>
        qx_gen_tac ‘x’ >> Cases_on ‘x = 0’ >> simp[] >>
        ‘abs x + 1 ≠ 0’ by rw[abs] >>
        simp[ABS_INV] >>
        ‘abs (abs x + 1) = abs x + 1’ by rw[abs] >> simp[] >>
        ‘abs x * inv (abs x + 1) ≠ 1’ by simp[] >>
        ‘1 - abs x * inv (abs x + 1) ≠ 0’ by simp[] >>
        irule REAL_EQ_LMUL_IMP >> first_assum $ irule_at Any >>
        REWRITE_TAC [REAL_INV_nonzerop] >>
        simp[REAL_SUB_RDISTRIB]) >>
  ‘∀y. -1 < y ∧ y < 1 ⇒ f (g y) = y’
    by (simp[Abbr‘g’, Abbr‘f’, real_div, ABS_MUL] >> qx_gen_tac ‘y’ >>
        strip_tac >> Cases_on ‘y = 0’ >> simp[] >>
        ‘0 ≤ 1 - abs y’ by rw[abs] >> simp[iffRL ABS_REFL] >>
        ‘abs y * inv (1 - abs y) + 1 ≠ 0’
          by simp[REAL_ARITH “x + 1r = 0 ⇔ x = -1”] >>
        irule REAL_EQ_LMUL_IMP >> first_assum $ irule_at Any >>
        REWRITE_TAC [REAL_INV_nonzerop] >> simp[REAL_RDISTRIB]) >>
  ‘∀x y. -1 < x ∧ x < y ∧ y < 1 ⇒ g x < g y’
    by (simp[Abbr‘g’, REAL_SUB_LDISTRIB] >> rw[abs] >>
        gs[REAL_NOT_LE] >>
        simp[REAL_ARITH “x - y:real < z ⇔ x < z + y”, REAL_MUL_LNEG,
             REAL_SUB_RNEG] >>
        ‘x < y + 2 * x * y’ suffices_by simp[] >>
        ‘1 - 2 * y < 0 ∨ 1 - 2 * y = 0 ∨ 0 < 1 - 2 * y’ by simp[]
        >- (‘y / (1 - 2 * y) < x’ suffices_by simp[] >>
            irule REAL_LET_TRANS >> first_assum $ irule_at Any >>
            simp[])
        >- (‘2 * y = 1’ by simp[] >> ‘2 * x * y = x’ by simp[] >> simp[]) >>
        ‘x < y / (1 - 2 * y)’ suffices_by simp[] >>
        irule REAL_LTE_TRANS >> first_assum $ irule_at Any >> simp[]) >>
  ‘∀x. -1 < f x ∧ f x < 1’ by simp[Abbr‘f’] >>
  ‘∀x y. x < y ⇒ f x < f y’
    by (CCONTR_TAC >> gs[REAL_NOT_LT, REAL_LE_LT] >>
        metis_tac[REAL_LT_ANTISYM, REAL_LT_REFL]) >>
  ‘BIJ f UNIV (ival (-1) 1)’ by (simp[BIJ_IFF_INV, ival_def] >> metis_tac[]) >>
  ‘BIJ g (ival (-1) 1) UNIV’ by (simp[BIJ_IFF_INV, ival_def] >> metis_tac[]) >>
  simp[homeomorphism, TOPSPACE_SUBTOPOLOGY] >> rpt strip_tac
  >- gs[ival_def]
  >- (gs[OPEN_IN_SUBTOPOLOGY] >>
      rename [‘tt = t ∩ ival _ _’] >>
      ‘open_in euclidean tt’ by simp[OPEN_IN_INTER] >>
      rw[] >> drule_then strip_assume_tac prop2_2_1_euclidean_ival_subtop >>
      simp[IMAGE_BIGUNION] >> irule OPEN_IN_BIGUNION >>
      simp[PULL_EXISTS] >>
      ‘∀a b. -1 < a ∧ a < b ∧ b < 1 ⇒ IMAGE g (ival a b) = ival (g a) (g b)’
        by (simp[EXTENSION, EQ_IMP_THM, PULL_EXISTS, ival_def, FORALL_AND_THM]>>
            rw[] >> metis_tac[REAL_LT_TRANS]) >>
      simp[]) >>
  simp[OPEN_IN_SUBTOPOLOGY] >>
  rename [‘open_in euclidean U’] >>
  qexists_tac ‘IMAGE f U’ >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
  simp[INTER_SUBSET_EQN] >> reverse conj_tac
  >- simp[SUBSET_DEF, ival_def, PULL_EXISTS] >>
  drule_then strip_assume_tac (iffLR prop2_2_1) >>
  simp[IMAGE_BIGUNION] >> irule OPEN_IN_BIGUNION >>
  simp[PULL_EXISTS] >>
  ‘∀x y. IMAGE f (ival x y) = ival (f x) (f y)’
    by (simp[ival_def, EXTENSION] >> metis_tac[REAL_LT_TRANS]) >>
  simp[]
QED

Theorem example_4_2_6:
  a < b ⇒
  ∃f g. homeomorphism (subtopology euclidean (ival a b), euclidean) (f,g)
Proof
  strip_tac >> ONCE_REWRITE_TAC [homeomorphism_SYM] >>
  irule_at Any (INST_TYPE [beta |-> “:real”] homeomorphism_TRANS) >>
  irule_at Any example_4_2_5 >>
  metis_tac[example_4_2_4, REAL_ARITH “-1r < 1”]
QED

Theorem COUNTABLE_LEMMA:
    countable s ⇔ ∃f (t: num set). BIJ f t s
Proof
    simp[countable_def] >> reverse eq_tac >> rw[]
    >- metis_tac[BIJ_SYM,BIJ_DEF,INJ_SUBSET,SUBSET_REFL,SUBSET_UNIV] >>
    ‘∃f (t: num set). BIJ f s t’ suffices_by metis_tac[BIJ_SYM] >>
    qexistsl_tac [‘f’,‘IMAGE f s’] >> metis_tac[INJ_IMAGE_BIJ]
QED

Theorem INJ_real_of_num:
    INJ real_of_num s UNIV
Proof
    simp[INJ_DEF]
QED

(*
discrete_topology_def
openSets_discrete
homeomorphism
subtopology

countable_surj
COUNTABLE_ALT_BIJ
COUNTABLE_ALT

LINV_DEF
ival_def

separable_def
exercise_3_2_4_vi
exercise_4_2_7v
separable_euclidean
separability of subspaces

exercise_4_1_14
exercise_2_2_4_i
exercise_2_2_4_ii
*)
Theorem exercise_4_2_8:
    (∃f g B. homeomorphism (discrete_topology A,subtopology euclidean B) (f,g)) ⇔ countable A
Proof
    Cases_on ‘countable A’ >> simp[]
    >- (gs[COUNTABLE_LEMMA] >>
        ‘homeomorphism (discrete_topology A,discrete_topology t) (LINV f t,f)’ by (
            drule_then strip_assume_tac $ iffLR BIJ_DEF >>
            simp[homeomorphism,BIJ_LINV_BIJ,SUBSET_DEF,PULL_EXISTS,BIJ_LINV_INV,LINV_DEF,SF SFY_ss] >>
            metis_tac[INJ_DEF,SURJ_DEF,LINV_DEF]) >>
        ‘∃g h. homeomorphism (discrete_topology t,subtopology euclidean (IMAGE real_of_num t)) (g,h)’
            suffices_by metis_tac[homeomorphism_TRANS] >>
        qexistsl_tac [‘real_of_num’,‘LINV real_of_num t’] >>
        simp[homeomorphism,TOPSPACE_SUBTOPOLOGY,OPEN_IN_SUBTOPOLOGY,
            BIJ_LINV_BIJ,SUBSET_DEF,PULL_EXISTS,BIJ_LINV_INV,LINV_DEF,SF SFY_ss] >>
        ‘INJ $& t UNIV’ by simp[INJ_DEF] >> drule_then assume_tac LINV_DEF >> rw[] >>
        simp[BIJ_LINV_BIJ,INJ_IMAGE_BIJ,SF SFY_ss] >>
        qexists_tac ‘BIGUNION {ival (&x - 1) (&x + 1) | x ∈ U}’ >>
        simp[PULL_EXISTS,OPEN_IN_BIGUNION] >> rw[Once EXTENSION,PULL_EXISTS] >>
        simp[ival_def,EQ_IMP_THM] >> rw[]
        >- (rename [‘x ∈ U’] >> qexists_tac ‘x’ >> simp[])
        >- (rename [‘&a < &(b + 1)’] >> gs[REAL_SUB] >> Cases_on ‘b ≤ 1’ >> gs[] >>
            ‘a = b’ by simp[] >> simp[]))
    >- (cheat
    )
QED

Theorem example_4_3_1:
  ¬homeomorphism (subtopology euclidean {x|0 ≤ x ∧ x ≤ 2},
                  subtopology euclidean ({x | 0 ≤ x ∧ x ≤ 1}∪{x | 2 ≤ x ∧ x ≤ 3}))
  (f, g)
Proof
  qmatch_abbrev_tac ‘¬homeomorphism (top1, top2) _’ \\
  CCONTR_TAC \\
  gs[] \\
  ‘closed_in top2 {x | 0 ≤ x ∧ x ≤ 1}’
    by (simp[CLOSED_IN_SUBTOPOLOGY, Abbr ‘top2’] \\
        qexists_tac ‘{x | 0 ≤ x ∧ x ≤ 1}’ \\
        simp[INTER_UNION]) \\
  ‘open_in top2 {x | 0 ≤ x ∧ x ≤ 1}’
    by (simp[OPEN_IN_SUBTOPOLOGY, Abbr ‘top2’] \\
        qexists_tac ‘ival (-1) (3/2)’ \\
        simp[] \\
        simp[EXTENSION, ival_def]) \\
  ‘¬ connected top2’
    by (simp[connected_def] \\
        qexists_tac ‘{x | 0 ≤ x ∧ x ≤ 1}’ \\
        simp[clopen_def] \\
        conj_tac
        >- (simp[TOPSPACE_SUBTOPOLOGY, Abbr ‘top2’, EXTENSION] \\
            qexists_tac ‘2’ \\
            simp[])
        >- (simp[EXTENSION] \\
            qexists_tac ‘0’ \\
            simp[])
       ) \\
  ‘¬ connected top1’
    by (cheat) \\
  cheat
QED

val _ = export_theory();
