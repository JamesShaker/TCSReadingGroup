open HolKernel Parse boolLib bossLib;
open chap4Theory pred_setTheory topologyTheory realTheory;
open chap2_instancesTheory chap4_instancesTheory chap5Theory realLib;
open chap3_instancesTheory chap3Theory;
open chap1Theory;

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

Definition path_connected_def:
  path_connected τ ⇔
  ∀a b. a ∈ topspace τ ∧ b ∈ topspace τ ⇒
        ∃f. continuousfn (EST {x | 0 ≤ x ∧ x ≤ 1}) τ f ∧
            f 0 = a ∧ f 1 = b
End

Theorem open_in_linear:
  open_in euclidean t ∧ m ≠ 0 ⇒
  open_in euclidean (IMAGE (λx. m * x + c) t)
Proof
  rw[open_in_euclidean] >>
  first_assum $ drule_then strip_assume_tac >>
  rename [‘x ∈ ival a b’] >>
  Cases_on ‘0 < m’
  >- (qexistsl [‘m * a + c’,‘m * b + c’] >>
      gs[SUBSET_DEF,ival_def] >>
      qx_gen_tac ‘y’ >> strip_tac >>
      qexists_tac ‘(y - c) / m’ >>
      simp[real_div]) >>
  qexistsl [‘m * b + c’,‘m * a + c’] >>
  gs[SUBSET_DEF,ival_def] >>
  qx_gen_tac ‘y’ >> strip_tac >>
  qexists_tac ‘(y - c) / m’ >>
  simp[real_div]
QED

Theorem linear_continuousfn:
  (∀x. x ∈ A ⇒ m * x + c ∈ B) ⇒ continuousfn (EST A) (EST B) (λx. m * x + c)
Proof
  rw[continuousfn_def,TOPSPACE_SUBTOPOLOGY,OPEN_IN_SUBTOPOLOGY] >>
  Cases_on ‘m = 0’ >> gvs[] (* 2 *)
  >- (Cases_on ‘A = {}’ >> gvs[] (* 2 *)
      >- (qexists_tac ‘t’ >> simp[]) >>
      gs[GSYM MEMBER_NOT_EMPTY] >> rename [‘a ∈ A’] >>
      first_assum $ drule_then assume_tac >>
      reverse $ Cases_on ‘c ∈ t’
      >- (qexists_tac ‘∅’ >> simp[EXTENSION]) >>
      qexists_tac ‘UNIV’ >>
      simp[EXTENSION]) >>
  irule_at Any open_in_linear >>
  irule_at Any REAL_INV_NZ >>
  rpt $ first_assum $ irule_at Any >>
  qexists_tac ‘- c * inv m’ >>
  simp[EXTENSION] >> rw[EQ_IMP_THM] >>
  simp[REAL_LDISTRIB,REAL_ARITH “x + -y + y = x:real”] >>
  first_assum $ irule_at Any >>
  simp[REAL_LDISTRIB]
QED

Theorem example_5_2_4:
  interval A ⇒ path_connected (EST A)
Proof
  rw[interval_def,path_connected_def,TOPSPACE_SUBTOPOLOGY] >>
  rename [‘_ 0 = c’,‘_ 1 = d’] >>
  Cases_on ‘c = d’
  >- (qexists_tac ‘K c’ >> simp[exercise_5_1_1_i,TOPSPACE_SUBTOPOLOGY]) >>
  qexists_tac ‘λx. (d - c) * x + c’ >>
  irule_at Any linear_continuousfn >> simp[] >>
  rw[REAL_LE_LT] >> gs[REAL_ARITH “d - c + c = d:real”] >>
  first_x_assum irule >> Cases_on ‘c < d’ >> rw[]
  >- (qexists_tac ‘c’ >> simp[] >> irule REAL_LT_MUL >> simp[])
  >- (qexists_tac ‘d’ >> simp[] >> irule REAL_LTE_TRANS >>
      qexists_tac ‘1 * (d - c) + c’ >> simp[])
  >- (qexists_tac ‘d’ >> simp[] >> irule REAL_LET_TRANS >>
      qexists_tac ‘1 * (d - c) + c’ >> simp[])
  >- (qexists_tac ‘c’ >> simp[] >> irule REAL_LTE_TRANS >>
      qexists_tac ‘0 * (d - c) + c’ >> simp[])
QED

Theorem prop_5_2_6:
  path_connected t ⇒ connected t
Proof
  rw[] >> CCONTR_TAC >> gs[remark_3_3_9, path_connected_def] >>
  `∃a b. a ∈ A ∧ b ∈ B ∧ a ≠ b`
    by metis_tac[MEMBER_NOT_EMPTY, EXTENSION, NOT_IN_EMPTY, IN_INTER] >>
  `a ∈ topspace t ∧ b ∈ topspace t`
    by metis_tac[IN_UNION] >>
  first_x_assum $ dxrule_all_then strip_assume_tac >>
  `clopen (EST {x | 0 ≤ x ∧ x ≤ 1}) ((PREIMAGE f A) ∩ {x | 0 ≤ x ∧ x ≤ 1})`
    by (rw[clopen_def]
        >- (drule $ cj 2 $ iffLR prop_5_1_9 >> rw[TOPSPACE_SUBTOPOLOGY] >>
            first_x_assum irule >> simp[closed_in] >>
            `topspace t DIFF A = B`
              by (simp[EXTENSION] >> metis_tac[IN_INTER, IN_UNION, NOT_IN_EMPTY, EXTENSION]) >>
            rw[] >> metis_tac[SUBSET_UNION])
        >> fs[continuousfn_def, TOPSPACE_SUBTOPOLOGY]) >>
  qabbrev_tac `U = PREIMAGE f A ∩ {x | 0 ≤ x ∧ x ≤ 1}` >>
  `U ≠ topspace (EST {x | 0 ≤ x ∧ x ≤ 1}) ∧ U ≠ ∅`
    by (rw[TOPSPACE_SUBTOPOLOGY]
        >- (simp[EXTENSION] >> qexists_tac `0` >> simp[Abbr `U`] >>
            metis_tac[IN_INTER, NOT_IN_EMPTY])
        >> simp[EXTENSION, Abbr `U`] >> qexists_tac `1` >> rw[]) >>
  `¬connected (EST {x | 0 ≤ x ∧ x ≤ 1})` by metis_tac[connected_def] >>
  gs[prop_4_3_5] >> metis_tac[remark_4_3_4ii]
QED

Theorem Weierstrass_IVT:
  a < b ∧ continuousfn (EST { x | a ≤ x ∧ x ≤ b }) euclidean f ∧ f a ≠ f b ⇒
  ∀p. f a ≤ p ∧ p ≤ f b ∨ f b ≤ p ∧ p ≤ f a ⇒
      ∃c. a ≤ c ∧ c ≤ b ∧ f c = p
Proof
  rpt strip_tac >>
  qabbrev_tac ‘AB = { x | a ≤ x ∧ x ≤ b}’ >>
  ‘connected (EST (IMAGE f AB))’
    by (drule exercise_5_1_8 >> simp[TOPSPACE_SUBTOPOLOGY] >>
        disch_then $ qspecl_then [‘f’, ‘AB’] mp_tac >>
        simp[SUBTOPOLOGY_SUBTOPOLOGY] >>
        strip_tac >> drule_then irule prop_5_2_1 >>
        simp[TOPSPACE_SUBTOPOLOGY, closed_ival_connected, Abbr‘AB’]) >>
  drule_then assume_tac $ iffLR prop_4_3_5 >>
  ‘p ∈ IMAGE f AB’
    by (gs[interval_def, PULL_EXISTS, Abbr‘AB’] >>
        metis_tac[REAL_LE_LT]) >>
  gs[Abbr‘AB’] >> metis_tac[]
QED

Theorem corollary_5_2_10:
  a < b ∧ continuousfn (EST { x | a ≤ x ∧ x ≤ b}) euclidean f ∧
  0 < f a ∧ f b < 0 ⇒
  ∃x. a < x ∧ x < b ∧ f x = 0
Proof
  strip_tac >> drule_then (drule_then $ qspec_then ‘0’ mp_tac) Weierstrass_IVT >>
  impl_tac >- rw[] >>
  metis_tac[REAL_LE_LT, REAL_LT_REFL]
QED
(*
Theorem continuousfn_additive:
  continuousfn t1 euclidean f ∧ continuousfn t1 euclidean g ⇒
  continuousfn t1 euclidean (λx. f x + g x)
Proof
  rw[continuousfn_def] >> .... ????

QED
*)

Theorem corollary_5_2_11:
  continuousfn (EST {x | 0 ≤ x ∧ x ≤ 1}) (EST {x | 0 ≤ x ∧ x ≤ 1}) f ⇒
  ∃z. 0 ≤ z ∧ z ≤ 1 ∧ f z = z
Proof
  strip_tac >>
  qabbrev_tac ‘Z1 = {x | 0r ≤ x ∧ x ≤ 1}’ >>
  Cases_on ‘f 0 = 0’ >- metis_tac[REAL_LE_REFL, SCONV[] “0r ≤ 1”] >>
  Cases_on ‘f 1 = 1’ >- metis_tac[REAL_LE_REFL, SCONV[] “0r ≤ 1”] >>
  ‘0 < f 0 ∧ f 1 < 1’
    by (gs[continuousfn_def, TOPSPACE_SUBTOPOLOGY, Abbr‘Z1’] >>
        metis_tac[REAL_LE_LT, REAL_LE_REFL, SCONV[] “0r ≤ 1”]) >>
  qabbrev_tac ‘g = λx. x - f x’ >>
  ‘continuousfn (EST Z1) euclidean g’
    by (gs[Abbr‘g’, continuousfn_def, TOPSPACE_SUBTOPOLOGY] >>
        rw[] >> rename [‘open_in euclidean A’] >>
        ‘open_in (EST Z1) (A ∩ Z1)’
          by (simp[OPEN_IN_SUBTOPOLOGY] >> metis_tac[]) >>
        first_x_assum drule >>
        simp[PREIMAGE_INTER, OPEN_IN_SUBTOPOLOGY, PULL_EXISTS] >>
        qx_gen_tac ‘B’ >> strip_tac >>
        cheat) >>
  cheat
QED

val _ = export_theory();
