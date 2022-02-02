open HolKernel Parse boolLib bossLib;

open pred_setTheory topologyTheory
open chap2Theory chap4Theory chap3Theory chap3_instancesTheory
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
  (∀x y. x ∈ s ∧ y ∈ s ∧ x < y ⇒ f x < f y) ⇒
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
  qexistsl_tac [‘LINV g (ival 0 1)’,‘g’] >>
  ‘BIJ g (ival 0 1) (ival a b)’ by
    (simp[BIJ_DEF,Abbr‘g’,INJ_DEF,SURJ_DEF,ival_def] >> rw[] (* 6 *)
     >- simp[REAL_SUB_LDISTRIB,
             REAL_ARITH “x:real < x - y + z ⇔ y < z”]
     >- (simp[REAL_SUB_LDISTRIB,
              REAL_ARITH “x - y + z < b ⇔ x - b < y - z”] >>
         simp[GSYM REAL_SUB_RDISTRIB])
     >- (gs[REAL_SUB_LDISTRIB,
            REAL_ARITH “x - y + z = x - y' + z' ⇔ y' - y = z' - z”] >>
         gs[GSYM REAL_SUB_LDISTRIB])
     >- simp[REAL_SUB_LDISTRIB,
             REAL_ARITH “x:real < x - y + z ⇔ y < z”]
     >-  (simp[REAL_SUB_LDISTRIB,
               REAL_ARITH “x - y + z < b ⇔ x - b < y - z”] >>
          simp[GSYM REAL_SUB_RDISTRIB])
     >> qexists_tac ‘(x - a) /(b - a)’ >>
     simp[real_div,REAL_SUB_LDISTRIB] >>
     irule REAL_EQ_RMUL_IMP >>
     qexists_tac ‘b - a’ >>
     REWRITE_TAC[REAL_RDISTRIB,REAL_SUB_RDISTRIB] >>
     simp[] >> simp[REAL_SUB_LDISTRIB]) >>
  drule_then assume_tac $ cj 1 $ iffLR BIJ_DEF >>
  rw[homeomorphism, TOPSPACE_SUBTOPOLOGY] (* 5 *)
  >- simp[BIJ_LINV_BIJ]
  >- (drule_then strip_assume_tac BIJ_LINV_INV >> simp[])
  >- (drule_then strip_assume_tac LINV_DEF >> simp[])
  >- (gs[OPEN_IN_SUBTOPOLOGY] >>
      qexists_tac ‘IMAGE g (t ∩ ival 0 1)’ >>
      reverse conj_tac
      >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> simp[INTER_SUBSET_EQN] >>
          simp[SUBSET_DEF, PULL_EXISTS] >> metis_tac[INJ_DEF]) >>
      rw[] >>
      qabbrev_tac ‘tt = t ∩ ival 0 1’ >>
      ‘open_in euclidean tt’ by (simp[Abbr‘tt’] >> irule OPEN_IN_INTER >>
                                 simp[]) >>
      ‘∃OIS. tt = BIGUNION {ival a b | OIS a b}’ by metis_tac[prop2_2_1] >>
      ‘∀c d. c ∈ ival 0 1 ∧ d ∈ ival 0 1 ⇒
             IMAGE g (ival c d) = ival (g c) (g d)’
        by (rw[] >> simp[EXTENSION, PULL_EXISTS, EQ_IMP_THM] >>
            rw[]
            >- (gs[ival_def] >>
                simp[Abbr‘g’, REAL_SUB_LDISTRIB,
                     REAL_ARITH
                       “a:real - x + x' < a - y + y' ⇔ x' - x < y' - y”] >>
                simp[GSYM REAL_SUB_RDISTRIB]) >>
            cheat) >>
      cheat)
  >> cheat
QED

val _ = export_theory();
