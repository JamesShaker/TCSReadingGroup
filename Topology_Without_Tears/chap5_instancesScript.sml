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



(*The book got the g = λx. f x - x the wrong way around as x - f x*)
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
  qabbrev_tac ‘g = λx. f x - x’ >>
  ‘continuousfn (EST Z1) euclidean g’
    by (*gs[Abbr‘g’, continuousfn_def, TOPSPACE_SUBTOPOLOGY] >>
        rw[] >> rename [‘open_in euclidean A’] >>
        ‘open_in (EST Z1) (A ∩ Z1)’
          by (simp[OPEN_IN_SUBTOPOLOGY] >> metis_tac[]) >>
        first_assum drule >>
        simp_tac (srw_ss()) [PREIMAGE_INTER, OPEN_IN_SUBTOPOLOGY, PULL_EXISTS] >>
        qx_gen_tac ‘B’ >> strip_tac >>
        irule_at Any EQ_REFL >>
        qpat_x_assum ‘open_in (EST Z1) (A ∩ Z1)’ mp_tac >>
        simp[open_in_euclidean,SUBSET_DEF,ival_def,
             OPEN_IN_SUBTOPOLOGY] >>
        disch_then $ qx_choose_then ‘B'’ strip_assume_tac>>
        qx_gen_tac ‘b’ >> strip_tac >>
        first_assum $ drule_then strip_assume_tac >>
        qexistsl [‘f c + a’,‘f c + b’] >>
        qx_gen_tac ‘d’ >> strip_tac >>
        last_assum irule
        simp[open_in_euclidean]
        cheat*) cheat >>
  gs[Abbr‘Z1’] >>
  ‘0 < g 0 ∧ g 1 < 0 ∧ 0r < 1’ by simp[Abbr‘g’] >>
  drule_all_then strip_assume_tac corollary_5_2_10 >>
  gs[Abbr‘g’] >> metis_tac[REAL_LE_LT]
QED

Theorem sq_continuous:
  continuousfn (EST $ ival 0 1) (EST $ ival 0 1) (λx. x * x)
Proof
  simp[continuousfn_def,OPEN_IN_SUBTOPOLOGY,ival_def,
       PULL_EXISTS,TOPSPACE_SUBTOPOLOGY] >>
  rw[] (* 2 *)
  >- (CCONTR_TAC >> gs[REAL_NOT_LT] >>
      ‘x < x pow 2’ by metis_tac[REAL_LTE_TRANS] >>
      gs[]) >>
  simp[PREIMAGE_INTER] >>
  qexists ‘(PREIMAGE (λx. x²) t) ∩ ival 0 1’ >> simp[EXTENSION,ival_def] >> rw[EQ_IMP_THM]
  (* 2 *)
  >- (gs[open_in_euclidean,SUBSET_DEF,ival_def] >>
      rpt strip_tac >>
      first_x_assum $ drule_then strip_assume_tac >>
      qexistsl [‘if a < 0 then 0 else (sqrt a)’,
                ‘min 1 (sqrt b)’] >>
      rw[sqrt_lt,REAL_LT_MIN] (* 3 *)
      >- metis_tac[REAL_LE_POW2,SQRT_MONO_LT,POW_2_SQRT,
                   REAL_LE_LT]
      >- (first_x_assum irule >>
          conj_tac (* 2 *)
          >- metis_tac[REAL_LTE_TRANS,REAL_LE_POW2] >>
          ‘b = (sqrt b) pow 2’
            by (simp[SQRT_POW2] >>
                metis_tac[REAL_LE_TRANS,REAL_LE_POW2,
                          REAL_LE_LT]) >>
          pop_assum SUBST1_TAC >>
          irule REAL_POW_LT2 >> simp[]) >>
      (first_x_assum irule >>
       conj_tac (* 2 *)
       >- metis_tac[REAL_LTE_TRANS,REAL_LE_POW2] >>
       ‘b = (sqrt b) pow 2’
         by (simp[SQRT_POW2] >>
             metis_tac[REAL_LE_TRANS,REAL_LE_POW2,
                       REAL_LE_LT]) >>
       pop_assum SUBST1_TAC >>
       irule REAL_POW_LT2 >> simp[])) >>
  CCONTR_TAC >> gs[REAL_NOT_LT] >>
  ‘x < x pow 2’ by metis_tac[REAL_LTE_TRANS] >>
  gs[]
QED

Theorem exercise_5_2_1:
  path_connected τ₁ ∧ continuousfn τ₁ τ₂ f ⇒
  path_connected (subtopology τ₂ (IMAGE f (topspace τ₁)))
Proof
  rw[path_connected_def,TOPSPACE_SUBTOPOLOGY] >>
  rename [‘_ 0 = f a’,‘_ 1 = f b’] >>
  last_x_assum $ qspecl_then [‘a’,‘b’] mp_tac >>
  simp[] >> disch_then $ qx_choose_then ‘g’ strip_assume_tac >>
  qexists ‘f ∘ g’ >> simp[] >>
  irule prop_5_1_8 >> first_assum $ irule_at Any >>
  resolve_then Any (irule o SRULE [SUBTOPOLOGY_TOPSPACE])
               SUBSET_REFL exercise_5_1_8 >>
  simp[]
QED

(*
Theorem exercise_5_2_2:
  a < b ∧
Proof
QED
*)

Theorem exercice_5_2_3_i:
  continuousfn (EST $ ival 0 1) (EST $ ival 0 1) (λx. x * x) ∧
  ∀z. z ∈ ival 0 1 ⇒ z * z ≠ z
Proof
  rw[sq_continuous,ival_def]
QED

Theorem closed_in_thm[simp]:
  closed_in euclidean {} ∧
  closed_in euclidean {a} ∧
  closed_in euclidean UNIV ∧
  closed_in euclidean {x | a ≤ x } ∧
  closed_in euclidean {x | x ≤ a } ∧
  closed_in euclidean {x | a ≤ x ∧ x ≤ b}
Proof
  simp[closed_is_closed] >>
  simp[closed_in, open_in_euclidean] >> rpt strip_tac >>
  gs[REAL_NOT_LE, SUBSET_DEF, ival_def] >~
  [‘x < a’, ‘_ < x ∧ x < _’]
  >- (qexistsl [‘x - 1’, ‘a’] >> simp[]) >~
  [‘a < x’, ‘_ < x ∧ x < _’]
  >- (qexistsl [‘a’, ‘x + 1’] >> simp[])
QED


Theorem closed_intervals:
  interval A ∧ closed_in euclidean A ⇔
  A = UNIV ∨ A = ∅ ∨ (∃a b. a ≤ b ∧ A = {x | a ≤ x ∧ x ≤ b}) ∨
  (∃a. A = { x | x ≤ a }) ∨ (∃a. A = { x | a ≤ x })
Proof
  rw[better_remark_4_3_4ii, EQ_IMP_THM, closed_is_closed] >>
  simp[] >~
  [‘closed_in euclidean {a}’] (* M-h M-p *)
  >- (‘{a} = {x | a ≤ x ∧ x ≤ a}’ suffices_by metis_tac[REAL_LE_REFL] >>
      simp[EXTENSION]) >~
  [‘closed_in euclidean {x | a ≤ x ∧ x ≤ b}’] (* M-h M-p *)
  >- metis_tac[REAL_LE_LT] >~
  [‘closed_in _ { x | x ≤ a}’] >- metis_tac[] >~
  [‘closed_in _ { x | a ≤ x}’] >- metis_tac[] >~
  [‘closed_in _ {x | a < x}’]
  >- (‘open_in euclidean {x | a < x}’ suffices_by
        (strip_tac >>
        ‘{ x | a < x } ≠ ∅ ∧ { x | a < x } ≠ UNIV’
           by (simp[EXTENSION] >>
               metis_tac [REAL_ARITH “a < a + 1r”, REAL_LT_REFL]) >>
         metis_tac[clopen_def, prop_3_3_3]) >>
      simp[]) >~
  [‘closed_in _ {x | x < a}’]
  >- (‘open_in euclidean {x | x < a}’ suffices_by
        (strip_tac >>
        ‘{ x | x < a } ≠ ∅ ∧ { x | x < a } ≠ UNIV’
           by (simp[EXTENSION] >>
               metis_tac [REAL_ARITH “a - 1r < a”, REAL_LT_REFL]) >>
         metis_tac[clopen_def, prop_3_3_3]) >>
      simp[]) >~
  [‘closed_in _ {x | a < x ∧ x < b}’]
  >- (‘open_in euclidean {x | a < x ∧ x < b}’ suffices_by
        (strip_tac >>
        ‘{ x | a < x ∧ x < b } ≠ ∅ ∧ { x | a < x ∧ x < b } ≠ UNIV’
           by (simp[EXTENSION] >> metis_tac [REAL_LT_REFL, REAL_MEAN]) >>
         metis_tac[clopen_def, prop_3_3_3]) >>
      simp[GSYM ival_def]) >~
  [‘closed_in _ {x | a ≤ x ∧ x < b}’]
  >- (‘F’ suffices_by simp[] >> pop_assum mp_tac >>
      simp[closed_include_all_limits, REAL_NOT_LE, REAL_NOT_LT,
           limpt_thm] >> qexists ‘b’ >>
      simp[open_in_euclidean, ival_def] >> rpt strip_tac >>
      first_x_assum $ drule_then $
        qx_choosel_then [‘c’, ‘d’] strip_assume_tac >>
      ‘max a c < b’ by simp[REAL_MAX_LT] >>
      drule REAL_MEAN >> disch_then $ qx_choose_then ‘e’ strip_assume_tac >>
      qexists ‘e’ >> gs[SUBSET_DEF, REAL_MAX_LT]) >~
  [‘closed_in _ {x | b < x ∧ x ≤ a}’]
  >- (‘F’ suffices_by simp[] >> pop_assum mp_tac >>
      simp[closed_include_all_limits, REAL_NOT_LE, REAL_NOT_LT,
           limpt_thm] >> qexists ‘b’ >>
      simp[open_in_euclidean, ival_def] >> rpt strip_tac >>
      first_x_assum $ drule_then $
        qx_choosel_then [‘c’, ‘d’] strip_assume_tac >>
      ‘b < min a d’ by simp[REAL_LT_MIN] >>
      drule REAL_MEAN >> disch_then $ qx_choose_then ‘e’ strip_assume_tac >>
      qexists ‘e’ >> gs[SUBSET_DEF, REAL_LT_MIN]) >~
  [‘a ≤ b’]
  >- (gs[REAL_LE_LT] >~
      [‘a < b’] >- metis_tac[] >> rpt disj1_tac >> qexists ‘a’ >>
      simp[EXTENSION]) >>
  metis_tac[]
QED

Theorem exercise_5_2_3_ii:
  interval A ∧ has_fixed_points (EST A) ⇒ closed_in euclidean A
Proof
  rw[better_remark_4_3_4ii] >> simp[] >~
  [‘EST {x | a < x ∧ x < b}’]
  >- (‘F’ suffices_by simp[] >>
      qpat_x_assum ‘has_fixed_points _’ mp_tac >>
      simp[has_fixed_points_def] >> qexists ‘λx. 1/2 * x + a / 2’ >> rw[] >~
      [‘1/2 * x + a/2 = x’]
      >- (pop_assum (mp_tac o Q.AP_TERM ‘$* 2r’) >>
          REWRITE_TAC[REAL_LDISTRIB] >> simp[] >> strip_tac >>
          ‘x = a’ by simp[] >> simp[TOPSPACE_SUBTOPOLOGY]) >>
      irule linear_continuousfn >> simp[] >> rpt strip_tac >>
      irule iterateTheory.REAL_LT_LCANCEL_IMP >> qexists ‘2’ >>
      REWRITE_TAC [REAL_LDISTRIB] >> simp[]) >~
  [‘EST { x | x < a}’]
  >- (‘F’ suffices_by simp[] >>
      qpat_x_assum ‘has_fixed_points _’ mp_tac >>
      simp[has_fixed_points_def] >> qexists ‘λx. 1/2 * x + a / 2’ >> rw[] >~
      [‘1/2 * x + a/2 = x’]
      >- (pop_assum (mp_tac o Q.AP_TERM ‘$* 2r’) >>
          REWRITE_TAC[REAL_LDISTRIB] >> simp[] >> strip_tac >>
          ‘x = a’ by simp[] >> simp[TOPSPACE_SUBTOPOLOGY]) >>
      irule linear_continuousfn >> simp[] >> rpt strip_tac >>
      irule iterateTheory.REAL_LT_LCANCEL_IMP >> qexists ‘2’ >>
      REWRITE_TAC [REAL_LDISTRIB] >> simp[]) >~
  [‘EST { x | a < x}’]
  >- (‘F’ suffices_by simp[] >>
      qpat_x_assum ‘has_fixed_points _’ mp_tac >>
      simp[has_fixed_points_def] >> qexists ‘λx. 1/2 * x + a / 2’ >> rw[] >~
      [‘1/2 * x + a/2 = x’]
      >- (pop_assum (mp_tac o Q.AP_TERM ‘$* 2r’) >>
          REWRITE_TAC[REAL_LDISTRIB] >> simp[] >> strip_tac >>
          ‘x = a’ by simp[] >> simp[TOPSPACE_SUBTOPOLOGY]) >>
      irule linear_continuousfn >> simp[] >> rpt strip_tac >>
      (irule iterateTheory.REAL_LT_LCANCEL_IMP ORELSE
       irule REAL_LE_LCANCEL_IMP) >> qexists ‘2’ >>
      REWRITE_TAC [REAL_LDISTRIB] >> simp[]) >~
  [‘EST { x | b ≤ x ∧ x < a }’]
  >-  (‘F’ suffices_by simp[] >>
      qpat_x_assum ‘has_fixed_points _’ mp_tac >>
      simp[has_fixed_points_def] >> qexists ‘λx. 1/2 * x + a / 2’ >> rw[] >~
      [‘1/2 * x + a/2 = x’]
      >- (pop_assum (mp_tac o Q.AP_TERM ‘$* 2r’) >>
          REWRITE_TAC[REAL_LDISTRIB] >> simp[] >> strip_tac >>
          ‘x = a’ by simp[] >> simp[TOPSPACE_SUBTOPOLOGY]) >>
      irule linear_continuousfn >> simp[] >> rpt strip_tac >>
      (irule iterateTheory.REAL_LT_LCANCEL_IMP ORELSE
       irule REAL_LE_LCANCEL_IMP) >> qexists ‘2’ >>
      REWRITE_TAC [REAL_LDISTRIB] >> simp[]) >~
  [‘EST { x | a < x ∧ x ≤ b }’]
  >-  (‘F’ suffices_by simp[] >>
      qpat_x_assum ‘has_fixed_points _’ mp_tac >>
      simp[has_fixed_points_def] >> qexists ‘λx. 1/2 * x + a / 2’ >> rw[] >~
      [‘1/2 * x + a/2 = x’]
      >- (pop_assum (mp_tac o Q.AP_TERM ‘$* 2r’) >>
          REWRITE_TAC[REAL_LDISTRIB] >> simp[] >> strip_tac >>
          ‘x = a’ by simp[] >> simp[TOPSPACE_SUBTOPOLOGY]) >>
      irule linear_continuousfn >> simp[] >> rpt strip_tac >>
      (irule iterateTheory.REAL_LT_LCANCEL_IMP ORELSE
       irule REAL_LE_LCANCEL_IMP) >> qexists ‘2’ >>
      REWRITE_TAC [REAL_LDISTRIB] >> simp[])
QED

Theorem continuousfn_scale:
  continuousfn (EST {x | a ≤ x ∧ x ≤ b}) τ f ∧ 0 < c ⇒
  continuousfn (EST {x | a/c ≤ x ∧ x ≤ b/c}) τ (λx. f (c * x))
Proof
  rw[continuousfn_def] >>
  first_x_assum drule >>
  simp[OPEN_IN_SUBTOPOLOGY] >> strip_tac >>
  qexists ‘{x | c * x ∈ t}’ >> reverse conj_tac
  >- (pop_assum mp_tac >> simp[EXTENSION]) >>
  ‘inv c ≠ 0’ by simp[] >>
  drule_all_then (qspec_then ‘0’ mp_tac) open_in_linear >>
  simp[] >>
  ‘(IMAGE (λx. c⁻¹ * x) t) = {x | c * x ∈ t}’ suffices_by simp[] >>
  simp[EXTENSION]
QED

Theorem continuousfn_scale_neg:
  continuousfn (EST {x | a ≤ x ∧ x ≤ b}) τ f ∧ c < 0 ⇒
  continuousfn (EST {x | b/c ≤ x ∧ x ≤ a/c}) τ (λx. f (c * x))
Proof
  rw[continuousfn_def] >>
  first_x_assum drule >>
  simp[OPEN_IN_SUBTOPOLOGY] >> strip_tac >>
  qexists ‘{x | c * x ∈ t}’ >> reverse conj_tac
  >- (pop_assum mp_tac >> simp[EXTENSION] >> metis_tac[]) >>
  ‘inv c ≠ 0’ by simp[] >>
  drule_all_then (qspec_then ‘0’ mp_tac) open_in_linear >>
  simp[] >>
  ‘(IMAGE (λx. c⁻¹ * x) t) = {x | c * x ∈ t}’ suffices_by simp[] >>
  simp[EXTENSION]
QED

Theorem continuousfn_shift:
  continuousfn (EST {x | a ≤ x ∧ x ≤ b}) τ f ⇒
  continuousfn (EST {x | a - c ≤ x ∧ x ≤ b - c}) τ (λx. f (x + c))
Proof
  rw[continuousfn_def] >>
  first_x_assum drule >>
  simp[OPEN_IN_SUBTOPOLOGY] >> strip_tac >>
  qexists ‘{x | x + c ∈ t}’ >> reverse conj_tac
  >- (pop_assum mp_tac >>
      simp[EXTENSION,REAL_LE_SUB_RADD,REAL_LE_SUB_LADD]) >>
  ‘1r ≠ 0’ by simp[] >>
  drule_all_then (qspec_then ‘-c’ mp_tac) open_in_linear >>
  simp[] >>
  ‘(IMAGE (λx. x + -c) t) = {x | x + c ∈ t}’ suffices_by simp[] >>
  simp[EXTENSION,GSYM real_sub,REAL_EQ_SUB_LADD]
QED

(*
(* open_in euclidean (s ∩ A ∪ t ∩ B) *)
Theorem open_in_EST_UNION:
  open_in (EST A) s ∧ open_in (EST B) t ⇒
  open_in (EST (A ∪ B)) (s ∪ t)
Proof
  simp[OPEN_IN_SUBTOPOLOGY,PULL_EXISTS] >> rw[] >>
  rename [‘s ∩ A ∪ t ∩ B’] >>
  qexists ‘s ∩ t’ >> simp[OPEN_IN_INTER,EXTENSION] >> metis_tac[]
        (*
  simp[OPEN_IN_SUBTOPOLOGY,PULL_EXISTS,UNION_OVER_INTER] >>
  rpt strip_tac >>
  rename[‘ta ∩ A ∪ tb ∩ B’] >>
  qexists ‘ta ∩ tb’ >>
  simp[OPEN_IN_INTER,EXTENSION] >> metis_tac[]*)
QED
*)

Theorem OPEN_IN_IVAL_EXTENDED:
  C ⊆ ival a b ∧ open_in (EST (ival a b)) C ⇒ open_in (EST (ival a b ∪ B)) C
Proof
  simp[OPEN_IN_SUBTOPOLOGY] >> strip_tac >> simp[] >>
  qexists ‘t ∩ ival a b’ >> simp[OPEN_IN_INTER] >>
  simp[EXTENSION] >> metis_tac[]
QED

(*Theorem OPEN_IN_RCLOSED_IVAL_EXTENDED:
  C ⊆ {x | a < x ∧ x ≤ b} ∧ open_in (EST {x | a < x ∧ x ≤ b}) C ⇒
  open_in (EST ({x | a < x ∧ x ≤ b} ∪ ({b} ∪ B))) C
Proof
  simp[OPEN_IN_SUBTOPOLOGY] >> strip_tac >> simp[] >>
  qexists ‘t ∩ ival a b’ >> simp[OPEN_IN_INTER] >>
  simp[EXTENSION, ival_def] >> rw[EQ_IMP_THM]
QED *)

Theorem continuousfn_stitch:
  a ≤ b ∧ b ≤ c ∧ f b ∈ topspace τ ∧ a < c ∧
  continuousfn (EST {x | a < x ∧ x < b}) τ f ∧
  continuousfn (EST {x | b < x ∧ x < c}) τ g ∧ f b = g b ⇒
  continuousfn (EST {x | a < x ∧ x < c}) τ (λx. if x ≤ b then f x else g x)
Proof
  rw[continuousfn_def] >- (rw[] >> Cases_on ‘x = b’ >> gs[]) >>
  map_every qabbrev_tac
            [‘ab = { x | a < x ∧ x < b}’, ‘bc = {x | b < x ∧ x < c}’,
             ‘ac = {x | a < x ∧ x < c}’] >>
  ‘open_in (EST ab) (PREIMAGE f A ∩ ab) ∧ open_in (EST bc) (PREIMAGE g A ∩ bc)’
    by simp[] >>
  reverse $ Cases_on ‘a < b’
  >- (‘a = b’ by simp[] >> fs[] >> rw[] >>
      ‘PREIMAGE (λx. if x ≤ a then f x else g x) A ∩ ac =
       PREIMAGE g A ∩ ac’ suffices_by simp[] >>
      simp[EXTENSION, Abbr‘ac’] >>
      metis_tac[REAL_ARITH “a < x ⇒ ¬(x ≤ a:real)”])>>
  reverse $ Cases_on ‘b < c’
  >- (‘b = c’ by simp[] >> fs[] >> rw[] >>
      ‘PREIMAGE (λx. if x ≤ b then f x else g x) A ∩ ab =
       PREIMAGE f A ∩ ab’ suffices_by simp[] >>
      simp[EXTENSION, Abbr‘ab’, REAL_LE_LT, SF CONJ_ss] >>
      simp[SF CONJ_ss]) >>
  ‘ac = ab ∪ bc ∪ {b}’
    by (simp[Abbr‘ab’, Abbr‘bc’, Abbr‘ac’, EXTENSION] >> rw[EQ_IMP_THM] >>
        simp[]) >>
  simp[UNION_OVER_INTER] >>
  ‘PREIMAGE (λx. if x ≤ b then f x else g x) A ∩ ab = PREIMAGE f A ∩ ab’
    by (simp[EXTENSION, Abbr‘ab’] >> rw[]) >>
  ‘PREIMAGE (λx. if x ≤ b then f x else g x) A ∩ bc = PREIMAGE g A ∩ bc’
    by (simp[EXTENSION, Abbr‘bc’] >> rw[] >> iff_tac >> strip_tac >>
        ‘x = b’ by simp[] >> gvs[]) >>
  simp[] >>
  ntac 2 (pop_assum kall_tac) >>
  ‘open_in (EST (ab ∪ bc ∪ {b})) (PREIMAGE f A ∩ ab)’
    by (‘ab = ival a b’ by simp[EXTENSION, Abbr‘ab’, ival_def] >>
        REWRITE_TAC [GSYM UNION_ASSOC] >> simp[] >>
        irule OPEN_IN_IVAL_EXTENDED >> gvs[]) >>
  ‘open_in (EST (ab ∪ bc ∪ {b})) (PREIMAGE g A ∩ bc)’
    by (‘bc = ival b c’ by simp[EXTENSION, Abbr‘bc’, ival_def] >> fs[] >>
        qpat_assum ‘open_in (EST (ival b c)) _’
                   (mp_then Any mp_tac OPEN_IN_IVAL_EXTENDED) >>
        simp[] >> metis_tac[UNION_ASSOC, UNION_COMM]) >>
  Cases_on ‘PREIMAGE (λx. if x ≤ b then f x else g x) A ∩ {b} = ∅’
  >- simp[OPEN_IN_UNION] >>
  ‘PREIMAGE (λx. if x ≤ b then f x else g x) A ∩ {b} = {b} ∧ g b ∈ A’
    by (simp[EXTENSION] >> pop_assum mp_tac >> simp[GSYM MEMBER_NOT_EMPTY] >>
        rw[] >> metis_tac[]) >>
  simp[] >>
  OPEN_IN_RCLOSED_IVAL_EXTENDED

Theorem continuousfn_stitch:
  a ≤ b ∧ b ≤ c ∧
  continuousfn (EST {x | a ≤ x ∧ x ≤ b}) τ f ∧
  continuousfn (EST {x | b ≤ x ∧ x ≤ c}) τ g ∧ f b = g b ⇒
  continuousfn (EST {x | a ≤ x ∧ x ≤ c}) τ (λx. if x ≤ b then f x else g x)
Proof
  rw[continuousfn_def] >- rw[] >>
  rpt $ first_x_assum $ drule_then assume_tac >>
  map_every qabbrev_tac
            [‘ab = { x | a ≤ x ∧ x ≤ b}’, ‘bc = {x | b ≤ x ∧ x ≤ c}’,
             ‘ac = {x | a ≤ x ∧ x ≤ c}’] >>
  ‘ac = ab ∪ bc’
    by simp[Abbr‘ab’, Abbr‘bc’, Abbr‘ac’, EXTENSION] >>
  simp[UNION_OVER_INTER] >>
  ‘PREIMAGE (λx. if x ≤ b then f x else g x) A ∩ ab = PREIMAGE f A ∩ ab’
    by (simp[EXTENSION, Abbr‘ab’] >> rw[]) >>
  ‘PREIMAGE (λx. if x ≤ b then f x else g x) A ∩ bc = PREIMAGE g A ∩ bc’
    by (simp[EXTENSION, Abbr‘bc’] >> rw[] >> iff_tac >> strip_tac >>
        ‘x = b’ by simp[] >> gvs[]) >>
  simp[] >>
  ntac 2 (pop_assum kall_tac) >>
  gs[OPEN_IN_SUBTOPOLOGY] >>
  rename [‘aot ∩ ab ∪ cot ∩ bc = _ ∩ (ab ∪ bc)’] >>


    simp[OPEN_IN_UNION, OPEN_IN_INTER] >>
  simp[EXTENSION] >> rw[EQ_IMP_THM] >> simp[] >> CCONTR_TAC >> gs[]




  ‘ac = ab ∪ bc’
    by simp[Abbr‘ab’, Abbr‘bc’, Abbr‘ac’, EXTENSION] >>
  simp[UNION_OVER_INTER] >> irule OPEN_IN_UNION >>
  simp[] >> conj_tac >> irule OPEN_IN_SUBTOPOLOGY_UNION >> simp[] >>
  simp[OPEN_IN_SUBTOPOLOGY]


  cheat
QED

Theorem path_connected_nexus:
  path_connected τ ⇔
    topspace τ = ∅ ∨
    ∃p. p ∈ topspace τ ∧
        ∀a. a ∈ topspace τ ⇒
            ∃f. continuousfn (EST {x | 0 ≤ x ∧ x ≤ 1}) τ f ∧ f 0 = a ∧ f 1 = p
Proof
  Cases_on ‘topspace τ = ∅’
  >- simp[path_connected_def] >>
  simp[] >> iff_tac
  >- (simp[path_connected_def] >> metis_tac[MEMBER_NOT_EMPTY]) >>
  rw[path_connected_def] >>
  ‘∃fa fb. continuousfn (EST {x | 0 ≤ x ∧ x ≤ 1}) τ fa ∧ fa 0 = a ∧ fa 1 = p ∧
           continuousfn (EST {x | 0 ≤ x ∧ x ≤ 1}) τ fb ∧ fb 0 = b ∧ fb 1 = p’ by (
    metis_tac[]) >>
  qexists ‘λx. if x ≤ 1/2 then fa (2*x) else fb (2*(1-x))’ >>
  simp[] >> cheat
  (*gs[continuousfn_def] >> rw[] >>*)
QED

(*
path_connected_def
euclidean_2_def
subtopology
continuousfn_def
*)
Theorem exercice_5_2_7:
  path_connected (subtopology euclidean_2 {(x,y) | ¬rational x ∨ ¬rational y})
Proof
  simp[path_connected_nexus] >> cheat
QED

val _ = export_theory();
