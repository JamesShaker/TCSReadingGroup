open HolKernel Parse boolLib bossLib;
open chap4Theory pred_setTheory topologyTheory realTheory;
open chap2_instancesTheory chap4_instancesTheory chap5Theory realLib;

val _ = new_theory "chap5_instances";

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss]

(*
continuousfn_def
open_in_euclidean
*)

Theorem lemma_5_1_1:
      continuousfn euclidean euclidean f ⇔
        ∀a e.
          0 < e ⇒
          ∃d. 0 < d ∧
              ∀x. a − d < x ∧ x < a + d ⇒ f a − e < f x ∧ f x < f a + e
Proof
    rw[continuousfn_def,EQ_IMP_THM]
    >- (‘open_in euclidean (ival (f a - e) (f a + e))’ by simp[] >>
        first_x_assum $ dxrule_then assume_tac >>
        gs[open_in_euclidean] >>
        first_x_assum $ qspec_then ‘a’ mp_tac >>
        simp[ival_def,SUBSET_DEF] >> rw[] >>
        rename [‘c1 < a’,‘a < c2’] >>
        qexists_tac ‘min (a - c1) (c2 - a)’ >> rw[min_def]) >>
    gs[open_in_euclidean] >>
    qx_gen_tac ‘a’ >> strip_tac >>
    first_x_assum dxrule >>
    simp[ival_def,SUBSET_DEF] >>
    rw[] >> rename [‘c1 < f a’,‘f a < c2’] >>
    first_x_assum $ qspecl_then [‘a’,‘min (f a - c1) (c2 - f a)’] mp_tac >>
    rw[min_def,REAL_SUB_SUB2,REAL_SUB_ADD2] >>
    qexistsl_tac [‘a - d’,‘a + d’] >> simp[] >>
    rw[] >> first_x_assum irule >>
    first_x_assum $ drule_all >> simp[]
QED

Theorem example_5_1_6:
  (∀x. f x = if x ≤ 3 then x - 1 else 0.5*(x+5)) ⇒
  ¬continuousfn euclidean euclidean f
Proof
  rw[continuousfn_def] >> qexists_tac `ival 1 3` >> rw[] >>
  `PREIMAGE f (ival 1 3) = {x | 2 < x ∧ x ≤ 3}`
    by (rw[EXTENSION, ival_def] >> rw[]) >>
  rw[exercise_2_1_1]
QED

Theorem exercise_5_1_2_i:
  (∀x. f x = if x ≤ 0 then -1 else 1) ⇒
  ¬continuousfn euclidean euclidean f
Proof
  rw[continuousfn_def] >> qexists_tac `ival (-2) 1` >> rw[] >>
  `PREIMAGE f (ival (-2) 1) = {x | x ≤ 0}`
    by (rw[EXTENSION, ival_def] >> rw[]) >>
  rw[open_in_euclidean] >> qexists_tac `0` >> rw[ival_def] >>
  simp[SUBSET_DEF] >> Cases_on `a < 0` >> simp[] >>
  Cases_on `0 < b` >> simp[] >>
  qexists_tac `b/2` >> rw[]
QED

Theorem exercise_5_1_2_ii:
  (∀x. f x = if x ≤ 0 then -1 else 1) ⇒
  ¬continuousfn euclidean euclidean f
Proof
  rw[prop_5_1_9] >> qexists_tac `{1}` >> rw[] >>
  `PREIMAGE f {1} = {x | 0 < x}`
    by (rw[EXTENSION] >> rw[]) >> rw[] >>
  `open_in euclidean {x | 0 < x}`
    by rw[] >>
  strip_tac >>
  `{x | 0r < x} = ∅ ∨ {x | 0 < x} = 𝕌(:real)`
    by metis_tac[chap1Theory.clopen_def,
                 chap3_instancesTheory.prop_3_3_3] >>
  gs[EXTENSION] >> pop_assum mp_tac >> simp[]
  >- (qexists_tac `1` >> rw[])
  >> qexists_tac `-1` >> rw[]
QED

Theorem exercise_5_1_3:
  (∀x. f x = if x ≤ 1 then x else x+2) ⇒
  ¬continuousfn euclidean euclidean f
Proof
  rw[continuousfn_def] >> qexists_tac `ival 0 3` >> rw[] >>
  `PREIMAGE f (ival 0 3) = {x | 0 < x ∧ x ≤ 1}`
    by (rw[EXTENSION, ival_def] >> rw[]) >>
  rw[exercise_2_1_1]
QED

Theorem exercise_5_1_4:
  (∀x. f x = if 0 ≤ x ∧ x ≤ 1 then 1 else 2) ⇒
  continuousfn (subtopology euclidean {x | 0 ≤ x ∧ x ≤ 1 ∨ 2 ≤ x ∧ x ≤ 4}) euclidean f
Proof
  rw[continuousfn_def, OPEN_IN_SUBTOPOLOGY, TOPSPACE_SUBTOPOLOGY] >>
  map_every Cases_on [`1 ∈ A`, `2 ∈ A`]
  >- (qexists_tac `UNIV` >> rw[EXTENSION] >>
      metis_tac[])
  >- (qexists_tac `ival (-1) 2` >> rw[EXTENSION,ival_def,EQ_IMP_THM] >> fs[])
  >- (qexists_tac `ival 1 5` >> rw[EXTENSION,ival_def,EQ_IMP_THM] >> fs[])
  >> qexists_tac `∅` >> simp[EXTENSION] >> metis_tac[]
QED

Theorem FINITE_closed:
  FINITE s ⇒ closed_in euclidean s
Proof
  strip_tac >>
  ‘s = BIGUNION {{a} | a IN s}’
    by simp[Once EXTENSION,PULL_EXISTS] >>
  pop_assum SUBST1_TAC >>
  irule_at Any CLOSED_IN_BIGUNION >>
  strip_tac (* 2 *)
  >- simp[PULL_EXISTS] >>
  ‘{{a} | a ∈ s} = IMAGE (\a. {a}) s’
    by simp[Once EXTENSION] >>
  simp[]
QED

Theorem exercise_5_1_10_i:
 finer euclidean (finite_closed_topology UNIV)
Proof
  simp[DISJ_IMP_THM,finer_def,OPEN_IN_EMPTY] >>
  rw[] >> drule_then assume_tac FINITE_closed >>
  gs[closed_in,COMPL_COMPL_applied]
QED

Theorem exercise_5_1_11:
  continuousfn euclidean euclidean f ∧
  (∀q. q ∈ rational ⇒ f q = 0) ⇒
  ∀r. f r = 0
Proof
  CCONTR_TAC >> gs[prop_5_1_9] >>
  ‘closed_in euclidean {0}’ by simp[] >>
  first_x_assum drule >>
  ‘∃A. PREIMAGE f {0} = A ∪ rational ∧ DISJOINT A rational ∧ r ∉ A ∧
       A ∪ rational ≠ UNIV’
    by (simp[PREIMAGE_def, EXTENSION, DISJOINT_DEF] >>
        qexists ‘{ r | r ∉ rational ∧ f r = 0}’ >> simp[] >> rw[]
        >- metis_tac[]
        >- (simp[SF CONJ_ss] >> metis_tac[])) >>
  simp[closed_in, open_in_euclidean, SUBSET_DEF,
       DECIDE “¬p ∨ q ⇔ p ⇒ q”] >>
  qexists ‘r’ >> simp[] >> qx_genl_tac [‘a’, ‘b’] >> strip_tac >>
  gs[ival_def] >>
  metis_tac[rationals_dense, REAL_LT_TRANS, IN_DEF]
QED



val _ = export_theory();

