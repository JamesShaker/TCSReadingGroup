open HolKernel Parse boolLib bossLib;

open pred_setTheory topologyTheory
open chap1Theory chap2_instancesTheory chap4Theory chap3Theory
     chap3_instancesTheory transcTheory
open realTheory RealArith;
val _ = new_theory "chap4_instances";

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss]

Overload euclidean = “chap2_instances$euclidean”
Overload homeomorphism = “chap4$homeomorphism”
val _ = realLib.prefer_real()

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
  (∃f g B. homeomorphism (discrete_topology A,subtopology euclidean B) (f,g)) ⇔
    countable A
Proof
  Cases_on ‘countable A’ >> simp[]
  >- (gs[COUNTABLE_LEMMA] >>
      ‘homeomorphism (discrete_topology A,discrete_topology t) (LINV f t,f)’
        by (drule_then strip_assume_tac $ iffLR BIJ_DEF >>
            simp[homeomorphism,BIJ_LINV_BIJ,SUBSET_DEF,PULL_EXISTS,BIJ_LINV_INV,
                 LINV_DEF,SF SFY_ss] >>
            metis_tac[INJ_DEF,SURJ_DEF,LINV_DEF]) >>
      ‘∃g h. homeomorphism (discrete_topology t,
                            subtopology euclidean (IMAGE real_of_num t)) (g,h)’
        suffices_by metis_tac[homeomorphism_TRANS] >>
      qexistsl_tac [‘real_of_num’,‘LINV real_of_num t’] >>
      simp[homeomorphism,TOPSPACE_SUBTOPOLOGY,OPEN_IN_SUBTOPOLOGY,
           BIJ_LINV_BIJ,SUBSET_DEF,PULL_EXISTS,BIJ_LINV_INV,LINV_DEF,
           SF SFY_ss] >>
      ‘INJ $& t univ(:real)’ by simp[INJ_DEF] >>
      drule_then assume_tac LINV_DEF >>
      rw[] >>
      simp[BIJ_LINV_BIJ,INJ_IMAGE_BIJ,SF SFY_ss] >>
      qexists_tac ‘BIGUNION {ival (&x - 1) (&x + 1) | x ∈ U}’ >>
      simp[PULL_EXISTS,OPEN_IN_BIGUNION] >> rw[Once EXTENSION,PULL_EXISTS] >>
      simp[ival_def,EQ_IMP_THM] >> rw[]
      >- (rename [‘x ∈ U’] >> qexists_tac ‘x’ >> simp[])
      >- (rename [‘&a < &(b + 1)’] >> gs[REAL_SUB] >> Cases_on ‘b ≤ 1’ >>
          gs[] >> ‘a = b’ by simp[] >> simp[]))
  >- (rpt strip_tac >>
      metis_tac[exercise_2_2_4_i,exercise_4_1_14, chap2Theory.exercise_2_2_4_ii,
                exercise_4_2_7iv,homeomorphism_SYM])
QED

Theorem closed_euclidean_UNIV[simp]:
  closed_in euclidean UNIV
Proof
 rw[closed_in]
QED

 (*

https://math.stackexchange.com/questions/339401/closed-unit-interval-is-connected-proof
*)

Theorem closed_ival_connected:
    connected (subtopology euclidean {a| x ≤ a ∧ a ≤ y})
Proof
  CCONTR_TAC >> gs[remark_3_3_9,TOPSPACE_SUBTOPOLOGY,OPEN_IN_SUBTOPOLOGY] >>
  qabbrev_tac ‘xy = {a | x ≤ a ∧ a ≤ y}’ >>
  rename [‘t1 ∩ xy ∪ t2 ∩ _’] >>
  ‘(t1 ∪ t2) ∩ xy = xy’
    by (gs[EXTENSION] >> metis_tac[]) >>
  gs[INTER_SUBSET_EQN] >>
  ‘xy ≠ {}’ by (strip_tac >> gvs[]) >>
  ‘∃a b. a ∈ A ∧ b ∈ B’ by metis_tac[MEMBER_NOT_EMPTY] >>
  wlog_tac ‘a < b’ [‘a’,‘b’,‘A’,‘B’,‘t1’,‘t2’]
  >- (‘b ≠ a’ by (strip_tac >> gvs[] >> last_x_assum mp_tac >>
                  simp[EXTENSION] >> metis_tac[]) >>
      ‘b < a’ by simp[] >> metis_tac[UNION_COMM,INTER_COMM]) >>
  qabbrev_tac ‘c = sup {x | x ∈ A ∧ x < b}’ >>
  ‘∀y. y ∈ A ∧ y < b ⇒ y ≤ c’
    by (simp[Abbr‘c’] >> rpt strip_tac >> irule REAL_SUP_UBOUND >>
        simp[] >> metis_tac[IN_INTER]) >>
  ‘∀x. (∀y. y ∈ A ∧ y < b ⇒ y ≤ x) ⇒ c ≤ x’
    by (rpt strip_tac >> simp[Abbr‘c’] >>
        irule REAL_IMP_SUP_LE >> simp[] >> metis_tac[IN_INTER]) >>
  ‘a ≤ c’ by simp[] >>
  ‘c ∈ xy’ by (simp[Abbr‘xy’] >> ‘x ≤ a’ suffices_by simp[] >>
               gvs[]) >>
  ‘c ∉ A’ by (
    Cases_on ‘c = b’
    >- (gvs[] >> strip_tac >> last_x_assum mp_tac >>
        simp[EXTENSION] >> metis_tac[]) >>
    ‘c < b’ by (‘c ≤ b’ suffices_by (strip_tac >> simp[]) >> simp[]) >>
    strip_tac >>
    ‘∃d. d ∈ t1 ∧ c < d ∧ d < b’
      by metis_tac[open_members_grow_towards_bound,IN_INTER] >>
    ‘d ∈ xy ∧ d ∈ A’ by gvs[Abbr ‘xy’] >> qpat_x_assum ‘c < d’ mp_tac >>
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

Theorem example_4_3_1:
  ¬homeomorphism
    (subtopology euclidean {x | 0 ≤ x ∧ x ≤ 2},
     subtopology euclidean ({x | 0 ≤ x ∧ x ≤ 1} ∪ {x | 2 ≤ x ∧ x ≤ 3}))
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
  ‘connected top1’ suffices_by metis_tac[homeomorphism_connected] \\
  simp[Abbr‘top1’, closed_ival_connected]
QED

Overload EST = “subtopology euclidean”

(*
remark_4_3_6
interval_def
REAL_MEAN
*)
Theorem corollary_4_3_7:
  a < b ∧ c < d ⇒
  (∀f g.
     ¬homeomorphism (EST {x | a < x ∧ x < b},EST {x | c ≤ x ∧ x < d}) (f,g)) ∧
  (∀f g.
     ¬homeomorphism (EST {x | a < x ∧ x < b},EST {x | c ≤ x ∧ x ≤ d}) (f,g)) ∧
  (∀f g.
     ¬homeomorphism (EST {x | a ≤ x ∧ x < b},EST {x | c ≤ x ∧ x ≤ d}) (f,g))
Proof
  strip_tac >> rpt conj_asm1_tac >> rpt gen_tac
  >- (strip_tac >> dxrule_then assume_tac $ iffLR homeomorphism_SYM >>
      drule_then (qspec_then ‘c’ mp_tac) remark_4_3_6 >>
      simp[TOPSPACE_SUBTOPOLOGY,SUBTOPOLOGY_SUBTOPOLOGY,SUBSET_INTER2] >>
      ‘{x | c ≤ x ∧ x < d} DIFF {c} = {x | c < x ∧ x < d}’ by simp[EXTENSION] >>
      simp[] >> strip_tac >>
      drule homeomorphism_connected >> simp[prop_4_3_5] >>
      conj_tac >- metis_tac[remark4_3_4ii] >>
      simp[interval_def] >>
      ‘a < g c ∧ g c < b’
        by (gs[homeomorphism, TOPSPACE_SUBTOPOLOGY] >>
            gs[BIJ_IFF_INV]) >>
      ‘∃a' b'. a < a' ∧ a' < g c ∧ g c < b' ∧ b' < b’
        by metis_tac[REAL_MEAN] >>
      metis_tac[REAL_LT_REFL, REAL_LT_TRANS])
  >- (pop_assum kall_tac >>
      strip_tac >> dxrule_then assume_tac $ iffLR homeomorphism_SYM >>
      drule_then (qspec_then ‘c’ mp_tac) remark_4_3_6 >>
      simp[TOPSPACE_SUBTOPOLOGY,SUBTOPOLOGY_SUBTOPOLOGY,SUBSET_INTER2] >>
      ‘{x | c ≤ x ∧ x ≤ d} DIFF {c} = {x | c < x ∧ x ≤ d}’ by simp[EXTENSION] >>
      simp[] >> strip_tac >>
      drule homeomorphism_connected >> simp[prop_4_3_5] >>
      conj_tac >- metis_tac[remark4_3_4ii] >>
      simp[interval_def] >>
      ‘a < g c ∧ g c < b’
        by (gs[homeomorphism, TOPSPACE_SUBTOPOLOGY] >>
            gs[BIJ_IFF_INV]) >>
      ‘∃a' b'. a < a' ∧ a' < g c ∧ g c < b' ∧ b' < b’
        by metis_tac[REAL_MEAN] >>
      metis_tac[REAL_LT_REFL, REAL_LT_TRANS])
  >- (strip_tac >> dxrule_then assume_tac $ iffLR homeomorphism_SYM >>
      drule_then (qspec_then ‘d’ mp_tac) remark_4_3_6 >>
      simp[TOPSPACE_SUBTOPOLOGY,SUBTOPOLOGY_SUBTOPOLOGY,SUBSET_INTER2] >>
      ‘{x | c ≤ x ∧ x ≤ d} DIFF {d} = {x | c ≤ x ∧ x < d}’ by simp[EXTENSION] >>
      simp[] >> strip_tac >>
      Cases_on ‘g d = a’
      >- (‘{ x | a ≤ x ∧ x < b } DIFF { g d } = { x | a < x ∧ x < b }’
            by simp[EXTENSION] >> gs[] >>
          metis_tac[homeomorphism_SYM]) >>
      drule homeomorphism_connected >> simp[prop_4_3_5] >>
      conj_tac >- metis_tac[remark4_3_4ii] >>
      simp[interval_def] >>
      ‘a < g d ∧ g d < b’
        by (gs[homeomorphism, TOPSPACE_SUBTOPOLOGY] >>
            gs[BIJ_IFF_INV] >> metis_tac[REAL_LE_LT]) >>
      ‘∃a' b'. a < a' ∧ a' < g d ∧ g d < b' ∧ b' < b’
        by metis_tac[REAL_MEAN] >>
      metis_tac[REAL_LT_REFL, REAL_LT_TRANS, REAL_LE_LT])
QED


Theorem closed_ival_homeo_01:
  a < b ⇒
  homeomorphism (EST {x | a ≤ x ∧ x ≤ b}, EST {x | 0 ≤ x ∧ x ≤ 1})
                ((λy. (y - a) / (b - a)), (λy. y * (b - a) + a))
Proof
  strip_tac >> qmatch_abbrev_tac ‘homeomorphism _ (f,g)’ >>
  ‘(∀x. f (g x) = x) ∧ (∀x. g (f x) = x)’
    by (simp[Abbr‘f’, Abbr‘g’] >> simp[real_div]) >>
  ‘∀x. 0 ≤ x ∧ x ≤ 1 ⇒ a ≤ g x ∧ g x ≤ b’
    by (simp[Abbr‘g’, REAL_LE_MUL] >>
        simp[REAL_ARITH “x + y ≤ z ⇔ x ≤ z - y:real”]) >>
  ‘∀x. a ≤ x ∧ x ≤ b ⇒ 0 ≤ f x ∧ f x ≤ 1’
    by simp[Abbr‘f’, REAL_LE_MUL] >>
  ‘∀x y. g x < g y ⇔ x < y’ by simp[Abbr‘g’] >>
  ‘∀x y. f x < f y ⇔ x < y’ by simp[Abbr‘f’] >>
  simp[homeomorphism, OPEN_IN_SUBTOPOLOGY, TOPSPACE_SUBTOPOLOGY] >>
  rpt strip_tac
  >- (simp[BIJ_IFF_INV] >> metis_tac[])
  >- (simp[BIJ_IFF_INV] >> metis_tac[])
  >- (rename [‘V = OS ∩ _’] >>
      qexists ‘IMAGE g OS’ >>
      simp[EXTENSION] >> reverse conj_tac >- metis_tac[] >>
      simp[open_in_euclidean, PULL_EXISTS] >> qx_gen_tac ‘x’ >> rpt strip_tac >>
      ‘∃c d. x ∈ ival c d ∧ ival c d ⊆ OS’ by metis_tac[open_in_euclidean] >>
      qexistsl_tac [‘g c’, ‘g d’] >> gs[ival_def, SUBSET_DEF] >>
      rpt strip_tac >> metis_tac[])
  >- (rename [‘V = OS ∩ _’] >>
      qexists ‘IMAGE f OS’ >>
      simp[EXTENSION] >> reverse conj_tac >- metis_tac[] >>
      simp[open_in_euclidean, PULL_EXISTS] >> qx_gen_tac ‘x’ >> rpt strip_tac >>
      ‘∃c d. x ∈ ival c d ∧ ival c d ⊆ OS’ by metis_tac[open_in_euclidean] >>
      qexistsl_tac [‘f c’, ‘f d’] >> gs[ival_def, SUBSET_DEF] >>
      rpt strip_tac >> metis_tac[])
QED

Theorem homeo_flip_open_closed_ends:
  a < b ⇒
  homeomorphism (EST {x | a ≤ x ∧ x < b }, EST {x | -b < x ∧ x ≤ -a})
                (real_neg,real_neg)
Proof
  simp[homeomorphism,TOPSPACE_SUBTOPOLOGY,
       OPEN_IN_SUBTOPOLOGY,BIJ_DEF,INJ_DEF,SURJ_DEF] >>
  rw[] (* 4 *)
  >- (qexists_tac ‘-x’ >> rw[])
  >- (qexists_tac ‘-x’ >> rw[])
  >> (qexists_tac ‘IMAGE numeric_negate t’ >>
      simp[EXTENSION] >> conj_tac (* 2 *)
      >- (gs[open_in_euclidean,PULL_EXISTS] >> rw[] >>
          first_x_assum
          (drule_then
           (qx_choosel_then [‘m’,‘n’] strip_assume_tac)) >>
          qexistsl_tac [‘-n’,‘-m’] >> gs[SUBSET_DEF,ival_def]>>
          simp[REAL_ARITH “a:real = -b ⇔ -a = b”]) >>
      simp[REAL_ARITH “a:real = -b ⇔ -a = b”] >> gen_tac >>
      Cases_on ‘-x ∈ t’ >> simp[])
QED

Theorem closed_open_ival_homeo_01:
  a < b ⇒
  homeomorphism (EST {x | a ≤ x ∧ x < b}, EST {x | 0 ≤ x ∧ x < 1})
                ((λy. (y - a) / (b - a)), (λy. y * (b - a) + a))
Proof
  strip_tac >> qmatch_abbrev_tac ‘homeomorphism _ (f,g)’ >>
  ‘(∀x. f (g x) = x) ∧ (∀x. g (f x) = x)’
    by (simp[Abbr‘f’, Abbr‘g’] >> simp[real_div]) >>
  ‘∀x. 0 ≤ x ∧ x < 1 ⇒ a ≤ g x ∧ g x < b’
    by (simp[Abbr‘g’, REAL_LE_MUL] >>
        simp[REAL_ARITH “x + y < z ⇔ x < z - y:real”]) >>
  ‘∀x. a ≤ x ∧ x < b ⇒ 0 ≤ f x ∧ f x < 1’
    by simp[Abbr‘f’, REAL_LE_MUL] >>
  ‘∀x y. g x < g y ⇔ x < y’ by simp[Abbr‘g’] >>
  ‘∀x y. f x < f y ⇔ x < y’ by simp[Abbr‘f’] >>
  simp[homeomorphism, OPEN_IN_SUBTOPOLOGY, TOPSPACE_SUBTOPOLOGY] >>
  rpt strip_tac
  >- (simp[BIJ_IFF_INV] >> metis_tac[])
  >- (simp[BIJ_IFF_INV] >> metis_tac[])
  >- (rename [‘V = OS ∩ _’] >>
      qexists ‘IMAGE g OS’ >>
      simp[EXTENSION] >> reverse conj_tac >- metis_tac[] >>
      simp[open_in_euclidean, PULL_EXISTS] >> qx_gen_tac ‘x’ >> rpt strip_tac >>
      ‘∃c d. x ∈ ival c d ∧ ival c d ⊆ OS’ by metis_tac[open_in_euclidean] >>
      qexistsl_tac [‘g c’, ‘g d’] >> gs[ival_def, SUBSET_DEF] >>
      rpt strip_tac >> metis_tac[])
  >- (rename [‘V = OS ∩ _’] >>
      qexists ‘IMAGE f OS’ >>
      simp[EXTENSION] >> reverse conj_tac >- metis_tac[] >>
      simp[open_in_euclidean, PULL_EXISTS] >> qx_gen_tac ‘x’ >> rpt strip_tac >>
      ‘∃c d. x ∈ ival c d ∧ ival c d ⊆ OS’ by metis_tac[open_in_euclidean] >>
      qexistsl_tac [‘f c’, ‘f d’] >> gs[ival_def, SUBSET_DEF] >>
      rpt strip_tac >> metis_tac[])
QED

Theorem INJ_IMAGE_INTER:
    (∀x y. f x = f y ⇔ x = y) ⇒ IMAGE f (A ∩ B) = IMAGE f A ∩ IMAGE f B
Proof
    rw[EXTENSION,PULL_EXISTS] >> metis_tac[]
QED

Theorem homeo_negate:
  B = IMAGE (real_neg) A ⇒ homeomorphism (EST A,EST B) (real_neg,real_neg)
Proof
    simp[homeomorphism,TOPSPACE_SUBTOPOLOGY,OPEN_IN_SUBTOPOLOGY,
       BIJ_DEF,INJ_DEF,SURJ_DEF,PULL_EXISTS,INJ_IMAGE_INTER,IMAGE_IMAGE,
       combinTheory.o_DEF] >>
    rw[] >> irule_at Any EQ_REFL >> gs[open_in_euclidean,PULL_EXISTS] >>
    rw[] >> first_x_assum $ dxrule_then strip_assume_tac >>
    gs[ival_def,SUBSET_DEF,REAL_ARITH “x = -y ⇔ -x = y:real”] >>
    rpt $ irule_at Any $ iffRL REAL_LT_NEG >>
    rpt $ first_assum $ irule_at Any >> simp[]
QED

Theorem homeo_shift:
  B = IMAGE ((+) d) A ⇒
  homeomorphism (EST A,EST B) ((+) d,flip (-) d)
Proof
    simp[homeomorphism,TOPSPACE_SUBTOPOLOGY,
       OPEN_IN_SUBTOPOLOGY,BIJ_DEF,INJ_DEF,SURJ_DEF,PULL_EXISTS,REAL_ADD_SUB] >>
    rw[]
    >- (simp[INJ_IMAGE_INTER,IMAGE_IMAGE,combinTheory.o_DEF,REAL_ADD_SUB] >>
        irule_at Any EQ_REFL >> gs[open_in_euclidean,PULL_EXISTS] >>
        rw[] >> first_x_assum $ dxrule_then strip_assume_tac >>
        gs[ival_def,SUBSET_DEF,REAL_EQ_SUB_LADD] >>
        rpt $ irule_at Any $ REAL_ARITH “x < (y:real) ⇒ x - z < y - z” >>
        rpt $ first_assum $ irule_at Any >> simp[])
    >- (simp[INJ_IMAGE_INTER,IMAGE_IMAGE,combinTheory.o_DEF,REAL_ADD_SUB] >>
        irule_at Any EQ_REFL >> gs[open_in_euclidean,PULL_EXISTS] >>
        rw[] >> first_x_assum $ dxrule_then strip_assume_tac >>
        gs[ival_def,SUBSET_DEF,REAL_ARITH “y = x + z ⇔ z = y - x: real”] >>
        rpt $ irule_at Any $ REAL_ARITH “x < (y:real) ⇒ z + x < z + y” >>
        rpt $ first_assum $ irule_at Any >> simp[])
QED

Theorem htrans =
        homeomorphism_TRANS
          |> INST_TYPE [“:α” |-> “:real”,“:β” |-> “:real”,“:γ” |-> “:real”]

Theorem open_in_IMAGE_realinv:
    0 ∉ t ∧ open_in euclidean t ⇒ open_in euclidean (IMAGE realinv t)
Proof
    simp[open_in_euclidean, PULL_EXISTS, ival_def, SUBSET_DEF] >> rw[] >>
    first_x_assum $ drule_then strip_assume_tac >>
    rename [‘x ∈ t’, ‘a < x’, ‘x < b’] >>
    ‘x < 0 ∨ x = 0 ∨ 0 < x’ by simp[] >> gvs[]
    >- (‘∃c. x < c ∧ c < min b 0’ by (irule REAL_MEAN >> simp[REAL_LT_MIN]) >>
        gvs[REAL_LT_MIN] >> qexistsl_tac [‘inv c’,‘inv a’] >> rw[] >>
        rename [‘_ * y’] >> qexists_tac ‘inv y’ >> simp[REAL_INV_INV] >>
        first_assum irule >> Cases_on ‘y < 0’ >> simp[]
        >- (‘b * y < c * y’ by simp[] >> simp[REAL_LT_TRANS]) >>
        gs[REAL_NOT_LT] >> gs[REAL_LE_LT] >>
        drule_then assume_tac REAL_LT_RMUL_0 >>
        pop_assum $ qspec_then ‘a’ assume_tac >> gvs[])
    >- (‘∃c. max a 0 < c ∧ c < x’ by (irule REAL_MEAN >> simp[REAL_MAX_LT]) >>
        gvs[REAL_MAX_LT] >> qexistsl_tac [‘inv b’,‘inv c’] >> rw[] >>
        rename [‘_ * y’] >> qexists_tac ‘inv y’ >> simp[REAL_INV_INV] >>
        first_assum irule >> Cases_on ‘0 < y’ >> simp[]
        >- (‘a * y < c * y’ by simp[] >> simp[REAL_LT_TRANS]) >>
        gs[REAL_NOT_LT] >> gs[REAL_LE_LT] >>
        ‘0 < b’ by simp[] >> drule_then assume_tac REAL_LT_RMUL_0 >>
        pop_assum $ qspec_then ‘y’ assume_tac >> gvs[])
QED

Theorem open_in_euclidean_DELETE:
  open_in euclidean t ⇒
  open_in euclidean (t DELETE a)
Proof
  strip_tac >>
  ‘t DELETE a = (t ∩ { x | x < a }) ∪ (t ∩ { x | a < x})’
    by (simp[EXTENSION, EQ_IMP_THM] >> rw[] >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule OPEN_IN_UNION >> conj_tac >>
  irule OPEN_IN_INTER >> simp[]
QED

Theorem INJ_IMAGE_DELETE:
  (∀x y. f x = f y ⇔ x = y) ⇒ IMAGE f (x DELETE e) = IMAGE f x DELETE f e
Proof
  simp[EXTENSION] >> metis_tac[]
QED

Theorem homeo_inv:
  0 ∉ A ∧ B = IMAGE inv A ⇒ homeomorphism (EST A, EST B) (inv, inv)
Proof
  simp[homeomorphism, TOPSPACE_SUBTOPOLOGY, OPEN_IN_SUBTOPOLOGY, PULL_EXISTS,
       REAL_INV_INV, BIJ_DEF, INJ_DEF, SURJ_DEF, INJ_IMAGE_INTER,
       REAL_INV_INJ, IMAGE_IMAGE, combinTheory.o_DEF] >> rw[]
  >> (qexists‘IMAGE realinv (t DELETE 0)’ >> reverse conj_tac
      >- (simp[EXTENSION] >> rw[EQ_IMP_THM] >>
          metis_tac[REAL_INV_INV, REAL_INV_0]) >>
      simp[open_in_euclidean_DELETE, open_in_IMAGE_realinv])
QED

Theorem upray_homeo_01:
  ∃f g. homeomorphism (EST {x | c < x }, EST { x | 0 < x ∧ x < 1 }) (f,g)
Proof
  irule_at Any htrans >> irule_at (Pos hd) homeo_shift >>
  ‘{ x | 1 < x } = IMAGE ($+ (1 - c)) { x | c < x }’
    by (simp[EXTENSION, EQ_IMP_THM, PULL_EXISTS] >> rw[] >>
        qexists ‘c + x - 1’ >> simp[]) >>
  first_assum $ irule_at Any >>
  irule_at Any homeo_inv >> simp[EXTENSION] >>
  rw[EQ_IMP_THM] >> simp[] >>
  qexists ‘inv x’ >> simp[REAL_INV_INV]
QED

Theorem upray_LE_homeo_01:
  ∃f g. homeomorphism (EST {x | c ≤ x}, EST {x | 0 ≤ x ∧ x < 1}) (f,g)
Proof
  irule_at Any htrans >> irule_at (Pos hd) homeo_shift >>
  ‘{ x | 1 ≤ x } = IMAGE ($+ (1 - c)) { x | c ≤ x }’
    by (simp[EXTENSION, EQ_IMP_THM, PULL_EXISTS] >> rw[] >>
        qexists ‘c + x - 1’ >> simp[]) >>
  first_x_assum $ irule_at Any >>
  irule_at Any htrans >>
  irule_at Any homeo_inv >>
  ‘{x | 0 < x ∧ x ≤ 1} = IMAGE realinv {x | 1 ≤ x}’
   by (simp[EXTENSION] >> rw[EQ_IMP_THM] >> simp[] >>
       qexists_tac ‘x⁻¹’ >> simp[REAL_INV_INV]) >>
  first_x_assum $ irule_at Any >>
  simp[] >>
  irule_at Any htrans >> irule_at (Pos hd) homeo_shift >>
  ‘{ x | -1 < x ∧ x ≤ 0 } = IMAGE ($+ (-1)) { x | 0 < x ∧ x ≤ 1r }’
    by simp[EXTENSION, REAL_ARITH “x = -1 + y ⇔ y = x + 1r”] >>
  pop_assum $ irule_at Any >> irule_at Any homeo_negate >>
  simp[EXTENSION, EQ_IMP_THM, PULL_EXISTS] >> rpt strip_tac >>
  qexists_tac ‘-x’ >> simp[]
QED

(* fact that only one of these disjuncts is possible follows from 4.3.7 above
   and the fact that {0} can't be homeomorphic to any of the others because
   their cardinalities are totally different. *)
Theorem exercise_4_3_1:
  interval A ∧ A ≠ ∅ ⇒
  (∃f g. homeomorphism (EST A, EST {0}) (f,g)) ∨
  (∃f g. homeomorphism (EST A, EST {x | 0 < x ∧ x < 1}) (f,g)) ∨
  (∃f g. homeomorphism (EST A, EST {x | 0 ≤ x ∧ x ≤ 1}) (f,g)) ∨
  (∃f g. homeomorphism (EST A, EST {x | 0 ≤ x ∧ x < 1}) (f,g))
Proof
  strip_tac >> gvs[better_remark4_3_4ii]
  >- (disj1_tac >> qexistsl_tac [‘λi. 0’, ‘λi. a’] >>
      simp[homeomorphism, TOPSPACE_SUBTOPOLOGY, OPEN_IN_SUBTOPOLOGY] >>
      rpt strip_tac >> simp[BIJ_IFF_INV]
      >- (qexists ‘K a’ >> simp[])
      >- (qexists ‘K 0’ >> simp[])
      >- (Cases_on ‘t ∩ {0} = ∅’ >> simp[]
          >- (qexists ‘∅’ >> simp[]) >>
          qexists ‘ival (a - 1) (a + 1)’ >> simp[] >>
          gs[EXTENSION, ival_def, SF CONJ_ss]) >>
      Cases_on ‘t ∩ {a} = ∅’ >> simp[]
      >- (qexists ‘∅’ >> simp[]) >>
      qexists ‘ival (-1) 1’ >> simp[] >>
      gs[EXTENSION, ival_def, SF CONJ_ss])
  >- metis_tac[closed_ival_homeo_01]
  >- metis_tac[example_4_2_4, REAL_ARITH “0 < 1r”,
               ival_def]
  >- metis_tac[closed_open_ival_homeo_01]
  >- metis_tac[homeomorphism_TRANS,homeomorphism_SYM,
               closed_open_ival_homeo_01,
               homeo_flip_open_closed_ends,
               REAL_ARITH “--x = x:real ∧
                           (-a < -b ⇔ b < a:real)”]
  >- ((* (-inf,a) -> (-a,inf) -> (1,inf) -> (0,1) *)
      disj2_tac >> disj1_tac >> irule_at Any htrans >>
      irule_at (Pos hd) homeo_negate >>
      ‘IMAGE real_neg { x | x < a} = {x | -a < x }’
        by (simp[EXTENSION] >> rw[EQ_IMP_THM] >> simp[] >>
            qexists ‘-x’ >> simp[]) >>
      first_x_assum (irule_at Any o SYM) >>
      metis_tac[upray_homeo_01])
  >- metis_tac[upray_homeo_01]
  >- ((* (-inf,a] -> [-a,inf) -> [1,inf) -> (0,1] -> [0,1) *)
      rpt disj2_tac >>
      irule_at Any htrans >>
      irule_at (Pos hd) homeo_negate >>
      ‘{x | -a ≤ x} = IMAGE real_neg {x | x ≤ a}’
      by (simp[EXTENSION,EQ_IMP_THM,
              PULL_EXISTS,FORALL_AND_THM] >>
         rw[] >> qexists_tac ‘-x’ >>
         simp[]) >>
      first_x_assum (irule_at Any) >>
      metis_tac[upray_LE_homeo_01])
  >- ((* [a,inf) -> [1,inf) -> (0,1] -> [0,1) *)
      metis_tac[upray_LE_homeo_01]) >>
  (* (inf,inf) -> (-1,1) -> (0,1) *)
  simp[SUBTOPOLOGY_UNIV] >>
  disj2_tac >> disj1_tac >>
  irule_at Any htrans >>
  irule_at Any example_4_2_5 >>
  rw[GSYM ival_def] >>
  metis_tac[example_4_2_4,REAL_ARITH “0 < 1r ∧ -1 < 1r”]
QED

(*
example_4_2_6
cardinalTheory.countable_cardeq
*)
Theorem exercise_4_3_2:
    countable A ∧ a ∈ A ∧ b ∈ A ∧ a ≠ b ⇒ ¬connected (EST A)
Proof
    simp[prop_4_3_5,interval_def] >> rpt strip_tac >>
    wlog_tac ‘a < b’ [‘a’,‘b’]
    >- (‘b < a’ by simp[] >> metis_tac[]) >>
    drule_then strip_assume_tac example_4_2_6 >>
    drule_then assume_tac $ cj 1 $ iffLR homeomorphism >>
    gs[TOPSPACE_SUBTOPOLOGY] >>
    ‘ival a b ≈ 𝕌(:real)’ by metis_tac[cardinalTheory.cardeq_def] >>
    ‘¬countable (ival a b)’
      by metis_tac[cardinalTheory.countable_cardeq,
                   real_topologyTheory.UNCOUNTABLE_REAL] >>
    ‘¬(ival a b ⊆ A)’ by metis_tac[COUNTABLE_SUBSET] >>
    gs[SUBSET_DEF,ival_def] >>
    metis_tac[]
QED

(*
countable_rational
num_countable
countable_integer
*)
Overload "π"[local] = “pi”

Theorem COS_PERIODIC_N:
  cos (x + 2 * π * real_of_int i) = cos x
Proof
  wlog_tac ‘0 ≤ i’ []
  >- (gs[integerTheory.INT_NOT_LE] >>
      ONCE_REWRITE_TAC [GSYM COS_NEG] >>
      REWRITE_TAC[REAL_NEG_ADD, REAL_NEG_RMUL,
                  GSYM intrealTheory.real_of_int_neg] >>
      first_x_assum irule >> intLib.ARITH_TAC) >>
  Cases_on ‘i’ >> gs[] >> Induct_on ‘n’ >>
  simp[arithmeticTheory.ADD1] >>
  REWRITE_TAC [GSYM REAL_ADD, REAL_LDISTRIB] >>
  simp[] >> REWRITE_TAC [REAL_ADD_ASSOC, COS_PERIODIC] >>
  Cases_on ‘n = 0’ >> simp[]
QED

Theorem cos_EQ1:
  cos x = 1 ⇔ ∃i. x = 2 * π * real_of_int i
Proof
  wlog_tac ‘0 ≤ x ∧ x < 2 * π’ []
  >- (gs[REAL_NOT_LE, REAL_NOT_LT] >>
      ‘∃j. 0 ≤ x + 2 * π * real_of_int j ∧ x + 2 * π * real_of_int j < 2 * π’
        suffices_by (rw[] >> first_x_assum drule_all >>
                     REWRITE_TAC[COS_PERIODIC_N, REAL_MUL_ASSOC] >>
                     rw[] >> eq_tac >> rw[]
                     >- (pop_assum mp_tac >>
                         REWRITE_TAC [REAL_MUL_ASSOC] >>
                         qmatch_abbrev_tac ‘x + 2 * π * J1 = 2 * π * J2 ⇒ _’>>
                         REWRITE_TAC [REAL_ARITH “x + y = z ⇔ x = z - y:real”,
                                      GSYM REAL_SUB_LDISTRIB] >>
                         simp[Abbr‘J1’, Abbr‘J2’] >>
                         simp[GSYM intrealTheory.real_of_int_sub,
                              Excl "real_of_int_sub"]) >>
                     qexists ‘i + j’ >> simp[]) >>
      qabbrev_tac ‘τ = 2 * π’ >> ‘0 < τ’ by simp[Abbr‘τ’, PI_POS] >>
      simp[REAL_ARITH “0r ≤ x + τ * y ∧ x + τ * y < τ ⇔
                         τ * y - τ < -x ∧ -x ≤ τ * y”] >>
      simp[REAL_ARITH “x * y - x = x * (y - 1r)”] >>
      qspec_then ‘τ’ mp_tac REAL_ARCH_LEAST >> simp[]
      >- (disch_then $ qspec_then ‘-x’ mp_tac >> simp[] >>
          disch_then $ qx_choose_then ‘N’ strip_assume_tac >>
          Cases_on ‘-x = τ * &N’ >> simp[]
          >- (qexists ‘&N’ >> simp[REAL_SUB_LDISTRIB] >>
              ‘0 < τ’ suffices_by simp[] >> simp[Abbr‘τ’, PI_POS]) >>
          qexists ‘&N + 1’ >> simp[] >>
          REWRITE_TAC [GSYM REAL_ADD, REAL_ARITH “(x:real) + 1 - 1 = x”] >>
          gs[arithmeticTheory.ADD1]) >>
      disch_then $ qspec_then ‘x’ mp_tac >> simp[] >>
      disch_then $ qx_choose_then ‘N’ strip_assume_tac >>
      qexists ‘-&N’ >> simp[REAL_SUB_LDISTRIB] >>
      gs[arithmeticTheory.ADD1, REAL_LDISTRIB, GSYM REAL_ADD, Excl "REAL_ADD"]) >>
  eq_tac >> strip_tac
  >- (qexists ‘0’ >> simp[] >>
      qspec_then ‘1’ mp_tac COS_TOTAL >>
      simp[EXISTS_UNIQUE_ALT] >> strip_tac >>
      Cases_on ‘x ≤ π’
      >- metis_tac[COS_0, PI_POS, REAL_LE_LT] >>
      gs[REAL_NOT_LE] >>
      ‘cos ((x - π) + π) = cos x’ by simp[REAL_ARITH “x:real - y + y = x”] >>
      gs[COS_PERIODIC_PI] >>
      ‘cos (x - π) = -1’ by simp[] >>
      qspec_then ‘-1’ mp_tac COS_TOTAL >> impl_tac >- simp[] >>
      disch_then
        (qx_choose_then ‘y’ strip_assume_tac o SRULE[EXISTS_UNIQUE_ALT]) >>
      ‘y = π’ by metis_tac[PI_POS, COS_PI, REAL_LE_LT] >>
      pop_assum SUBST_ALL_TAC >>
      pop_assum $ qspec_then ‘x - π’ mp_tac  >> simp[]) >>
  assume_tac (COS_PERIODIC_N |> Q.INST [‘x’ |-> ‘0’] |> SRULE[]) >>
  simp[COS_0]
QED

Theorem pi_not0[local,simp]:
  π ≠ 0
Proof
  metis_tac[PI_POS, REAL_LT_REFL]
QED

Theorem both_neg_squared_injective:
  a < 0 ∧ b < 0 ∧ a pow 2 = b pow 2 ⇒ a = b
Proof
  rw[] >> CCONTR_TAC >>
  wlog_tac `a < b` [`a`, `b`]
  >- (metis_tac[REAL_NOT_LT, REAL_LE_LT])
  >> `-b < -a ∧ 2 ≠ 0n ∧ 0 ≤ -b` by simp[] >>
  drule_all REAL_POW_LT2 >> rw[]
QED

Theorem both_pos_squared_injective:
  0 ≤ a ∧ 0 ≤ b ∧ a pow 2 = b pow 2 ⇒ a = b
Proof
  Cases_on ‘a = 0’ >> simp[] >> Cases_on ‘b = 0’ >> simp[] >>
  rw[] >>
  mp_tac $ Q.INST [‘a’ |-> ‘-a’, ‘b’ |-> ‘-b’] both_neg_squared_injective >>
  simp[]
QED

Theorem square_EQ1:
  x pow 2 = 1 ⇔ x = 1 ∨ x = -1
Proof
  simp[EQ_IMP_THM, DISJ_IMP_THM] >>
  CCONTR_TAC >> gs[] >>
  ‘x < -1 ∨ -1 < x ∧ x < 1 ∨ 1 < x ’ by simp[] >~
  [‘1 < x’]
  >- (drule REAL_LT1_POW2 >> simp[]) >~
  [‘x < -1’]
  >- (‘1 < -x’ by simp[] >> drule REAL_LT1_POW2 >> simp[]) >~
  [‘-1 < x’, ‘x < 1’]
  >- (‘x ≠ 0’ by (strip_tac >> gs[]) >>
      wlog_tac ‘0 < x’ [‘x’]
      >- (first_x_assum $ qspec_then ‘-x’ mp_tac >> simp[]) >>
      ‘1 < inv x’  by simp[REAL_INV_LT1] >>
      drule REAL_LT1_POW2 >> simp[])
QED

Theorem ASN_POS:
  0 < x ∧ x ≤ 1 ⇒ 0 < asn x
Proof
  rw[] >> ‘-1 ≤ x’ by simp[] >>
  drule_all_then strip_assume_tac ASN >> CCONTR_TAC >>
  gs[REAL_NOT_LT] >>
  Cases_on ‘asn x = 0’ >> gs[SIN_0] >>
  ‘asn x < 0’ by simp[] >>
  ‘sin (-asn x) = -sin (asn x)’ by simp[SIN_NEG] >>
  ‘¬(0 ≤ sin (-asn x))’ by simp[] >>
  drule_at Concl SIN_POS_PI2_LE >> simp[]
QED


Theorem exercise_4_3_3i:
  let X = { (x,y) | x pow 2 + y pow 2 = 1 }
  in
    ∃f g. homeomorphism (EST { x | 0 < x ∧ x < 1 },
                         subtopology euclidean_2 (X DELETE (1,0))) (f,g)
Proof
  simp[] >>
  qabbrev_tac ‘fx = λx. cos (2 * π * x)’ >>
  qabbrev_tac ‘fy = λx. sin (2 * π * x)’ >>
  qabbrev_tac ‘FF = λx. (fx x, fy x)’ >>
  ‘BIJ FF { x | 0 < x ∧ x < 1 } ({ (x,y) | x pow 2 + y pow 2 = 1 } DELETE (1,0))’
    by (rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
        markerLib.UNABBREV_ALL_TAC >> simp[] >> gs[] >>~-
        ([‘_ pow 2 + _ pow 2 = 1’, ‘(cos _) pow 2’],
         metis_tac[REAL_ADD_COMM, SIN_CIRCLE]) >>~-
        ([‘cos _ = 1 ⇒ sin _ ≠ 0’],
         simp[cos_EQ1] >> rw[] >> gs[] >> SPOSE_NOT_THEN kall_tac >>
         intLib.ARITH_TAC) >~
        [‘x pow 2 + y pow 2 = 1’] (* 2 *)
        (* surjection *)
        >- (Cases_on ‘x = 1’ >> gs[REAL_ARITH “x + y = x ⇔ y = 0r”] >>
            Cases_on ‘x < 0’ >> Cases_on ‘y < 0’ (* 4 *) >>
            gs[REAL_NOT_LT] >~
            [‘x pow 2 + y pow 2 = 1’, ‘x < 0’, ‘y < 0’]
            >- (qabbrev_tac ‘a = acs x’ >>
                qexists_tac ‘1 - (a / (2 * π))’ >>
                simp[REAL_SUB_LDISTRIB,REAL_SUB_RDISTRIB,
                     REAL_ARITH “(0r < x - y ⇔ y < x) ∧ (a - b < a ⇔ 0r < b)”]>>
                ‘-1 < x’
                  by (CCONTR_TAC >>
                      gs[REAL_NOT_LT,REAL_LE_LT,
                         REAL_ARITH “x + y = x ⇔ y = 0r”] >>
                      ‘1 < -x’ by simp[] >>
                      dxrule REAL_LT1_POW2 >> simp[] >> strip_tac >>
                      ‘y pow 2 < 0’
                        by metis_tac[REAL_ARITH “a + b < a ⇔ b < 0r”] >>
                      gs[]) >>
                ‘0 < a ∧ a < π’
                  by simp[Abbr‘a’,ACS_BOUNDS_LT] >>
                simp[PI_POS,SIN_COS] >>
                ‘∀a. cos (2 * π − a) = cos (-a)’
                  by metis_tac[real_sub,REAL_ADD_COMM,COS_PERIODIC] >>
                simp[COS_NEG] >> conj_tac (* 2 *)
                >- simp[Abbr‘a’,ACS_COS] >>
                once_rewrite_tac[GSYM COS_NEG] >> simp[REAL_NEG_SUB] >>
                simp[REAL_ARITH “x - a - b = x - (a + b:real)”,COS_NEG] >>
                rw[COS_SIN,REAL_ARITH “a - (b + a) = -b:real”,SIN_NEG] >>
                `-sin a < 0`
                  by (simp[] >> metis_tac[SIN_POS_PI]) >>
                irule both_neg_squared_injective >> rw[] >>
                `(sin a)² = 1 - x²` suffices_by simp[] >>
                `(sin a)² = 1 - (cos a)²`
                  by metis_tac[SIN_CIRCLE, REAL_ARITH ``x + y = 1 ⇔ x = 1r - y``] >>
                simp[REAL_ARITH ``1 - a = 1r - b ⇔ a = b``, Abbr‘a’, ACS_COS]) >~
            [‘x pow 2 + y pow 2 = 1’, ‘x < 0’, ‘0 ≤ y’]
            >- (rw[] >> qexists_tac `1/2 - asn y/(2 * π)` >>
                ‘y < 1’
                  by (CCONTR_TAC >>
                      gs[REAL_NOT_LT,REAL_LE_LT,
                         REAL_ARITH “x + y = y ⇔ x = 0r”] >>
                      dxrule REAL_LT1_POW2 >> simp[] >> strip_tac >>
                      ‘x pow 2 < 0’
                        by metis_tac[REAL_ARITH “a + b < b ⇔ a < 0r”] >>
                      gs[]) >>
                rw[]
                >- (simp[REAL_ARITH ``(0r < x - y ⇔ y < x)``, PI_POS] >>
                    `asn y ≤ (pi/2)` by simp[ASN_BOUNDS] >> assume_tac PI_POS >>
                    gs[])
                >- (simp[REAL_LT_SUB_RADD, REAL_LDISTRIB,
                         REAL_ARITH ``1 < 2r + a ⇔ -1 < a``, PI_POS] >>
                    irule REAL_LTE_TRANS >> irule_at Any $ cj 1 ASN_BOUNDS >>
                    simp[PI_POS])
                >- (simp[REAL_SUB_LDISTRIB] >>
                    ‘cos (π - asn y) = cos (-asn y + π)’
                      by simp[real_sub, REAL_ADD_COMM] >>
                    simp[COS_PERIODIC_PI, COS_NEG] >>
                    irule both_neg_squared_injective >> simp[] >> conj_tac >~
                    [‘0 < cos (asn y)’]
                    >- (irule COS_POS_PI >>
                        ‘-1 < y ∧ y < 1 ’ suffices_by metis_tac[ASN_BOUNDS_LT] >>
                        simp[]) >>
                    ‘(cos (asn y)) pow 2 = 1 - (sin (asn y)) pow 2’
                      by metis_tac[SIN_CIRCLE, REAL_ARITH “x = 1r - y ⇔ y + x = 1”] >>
                    simp[ASN_SIN])
                >- (simp[REAL_LDISTRIB, real_sub, SIN_PERIODIC_PI,
                         REAL_ARITH “π + x = x + π”, SIN_NEG, ASN_SIN])) >~
            [‘x pow 2 + y pow 2 = 1’, ‘0 ≤ x’, ‘y < 0’]
            >- ((* bottom right quadrant; acs x is mirror angle in top right. *)
                qexists ‘1 - acs x / (2 * π)’ >>
                ‘x < 1’ by (CCONTR_TAC >> gs[REAL_NOT_LT, REAL_LE_LT] >>
                            dxrule REAL_LT1_POW2 >> strip_tac >>
                            ‘y pow 2 < 0’
                              by metis_tac[REAL_ARITH “a + b < a ⇔ b < 0r”] >>
                            gs[]) >>
                rw[] >~
                [‘0 < 1 - acs x / (2 * π)’]
                >- (simp[REAL_SUB_LT, PI_POS] >> irule REAL_LT_TRANS >>
                    irule_at Any $ cj 2 ACS_BOUNDS_LT >> simp[PI_POS]) >~
                [‘1 - acs x / (2 * π) < 1’]
                >- simp[REAL_ARITH “1r - x < 1 ⇔ 0 < x”, PI_POS, ACS_BOUNDS_LT] >~
                [‘cos _ = x’]
                >- simp[real_sub, REAL_LDISTRIB, REAL_ARITH “2 * π + x = x + 2 * π”,
                        COS_PERIODIC, COS_NEG, ACS_COS] >~
                [‘sin _ = y’]
                >- (simp[real_sub, REAL_LDISTRIB, REAL_ARITH “2 * π + x = x + 2 * π”,
                         SIN_PERIODIC, SIN_NEG] >>
                    irule both_neg_squared_injective >> simp[] >> conj_tac >~
                    [‘0 < sin (acs x)’]
                    >- (irule SIN_POS_PI >> simp[ACS_BOUNDS_LT]) >>
                    ‘(sin (acs x)) pow 2 = 1 - (cos (acs x)) pow 2’
                      by metis_tac[SIN_CIRCLE, REAL_ARITH “x = 1r - y ⇔ y + x = 1”,
                                   REAL_ADD_COMM] >>
                    simp[ACS_COS])) >~
            [‘x pow 2 + y pow 2 = 1’, ‘0 ≤ x’, ‘0 ≤ y’]
            >- ((* top right *)
                qexists ‘asn y / (2 * π)’ >>
                ‘y ≤ 1’ by (CCONTR_TAC >> gs[REAL_NOT_LE] >>
                            dxrule REAL_LT1_POW2 >> strip_tac >>
                            ‘x pow 2 < 0’
                              by metis_tac[REAL_ARITH “a + b < b ⇔ a < 0r”] >>
                            gs[]) >>
                ‘0 < y’ by (CCONTR_TAC >> gs[REAL_NOT_LT, REAL_LE_LT, square_EQ1]) >>
                rw[PI_POS] >~
                [‘0 < asn y’] >- simp[ASN_POS] >~
                [‘asn y < 2 * π’]
                >- (irule REAL_LET_TRANS >>
                    irule_at Any $ cj 2 ASN_BOUNDS >> simp[PI_POS]) >~
                [‘sin (asn y) = y’] >- simp[ASN_SIN] >~
                [‘cos (asn y) = x’]
                >- (irule both_pos_squared_injective >> simp[] >> conj_tac >~
                    [‘0 ≤ cos (asn y)’]
                    >- (irule COS_POS_PI2_LE >> simp[ASN_BOUNDS] >>
                        simp[REAL_LE_LT, ASN_POS]) >>
                    ‘(cos (asn y)) pow 2 = 1 - (sin (asn y)) pow 2’
                      by metis_tac[SIN_CIRCLE, REAL_ARITH “x = 1r - y ⇔ y + x = 1”,
                                   REAL_ADD_COMM] >>
                    simp[ASN_SIN]))) >>
        (* injection *)
        cheat)>>
  cheat
QED


val _ = export_theory();
