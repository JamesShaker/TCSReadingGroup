open HolKernel Parse boolLib bossLib;

open pred_setTheory intrealTheory 
open topologyTheory chap1Theory chap2_2Theory realTheory
open transcTheory;
open arithmeticTheory;
open pairTheory;

local open realSimps in end

val _ = new_theory "chap2";

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss]

Definition ival_def:
  ival (r:real) s = { x | r < x ∧ x < s }
End

Definition euclidean_def:
  euclidean = topology { s | ∀x. x ∈ s ⇒ ∃a b. x ∈ ival a b ∧ ival a b ⊆ s}
End

Theorem euclidean_istopology:
  istopology { s | ∀x. x ∈ s ⇒ ∃a b. x ∈ ival a b ∧ ival a b ⊆ s}
Proof
  simp[istopology, PULL_EXISTS, SUBSET_DEF, ival_def] >> rpt strip_tac
  >- (qpat_x_assum ‘∀x. x ∈ s ⇒ _’ $ drule_then $
       qx_choosel_then [‘sL’, ‘sR’] strip_assume_tac >>
      qpat_x_assum ‘∀x. x ∈ t ⇒ _’ $ drule_then $
       qx_choosel_then [‘tL’, ‘tR’] strip_assume_tac >>
      qexistsl_tac [‘max sL tL’, ‘min sR tR’] >>
      simp[REAL_MAX_LT, REAL_LT_MIN]) >>
  metis_tac[]
QED

Theorem open_in_euclidean:
  open_in euclidean s ⇔ ∀x. x ∈ s ⇒ ∃a b. x ∈ ival a b ∧ ival a b ⊆ s
Proof
  simp[euclidean_def, topology_tybij |> cj 2 |> iffLR,
       euclidean_istopology]
QED

Theorem topspace_euclidean[simp]:
  topspace euclidean = univ(:real)
Proof
  simp[topspace, Once EXTENSION, open_in_euclidean] >> qx_gen_tac ‘r’ >>
  qexists_tac ‘UNIV’ >> simp[ival_def] >> qx_gen_tac ‘s’ >>
  qexistsl_tac [‘s - 1’, ‘s + 1’] >> simp[]
QED

Theorem ivals_open[simp]:
  open_in euclidean (ival r s)
Proof
  simp[open_in_euclidean] >> metis_tac[SUBSET_REFL]
QED

Theorem neginfr_open[simp]:
  open_in euclidean { x | x < r }
Proof
  simp[open_in_euclidean] >> qx_gen_tac ‘a’ >> strip_tac >>
  qexistsl_tac [‘a - 1’, ‘r’] >> simp[ival_def, SUBSET_DEF]
QED

Theorem rposinf_open[simp]:
  open_in euclidean {x | r < x}
Proof
  simp[open_in_euclidean] >> qx_gen_tac ‘a’ >> strip_tac >>
  qexistsl_tac [‘r’, ‘a + 1’] >> simp[ival_def, SUBSET_DEF]
QED

Theorem closed_not_open:
  (* text has c < d as assumption *)
  c ≤ d ⇒ ¬open_in euclidean { x | c ≤ x ∧ x ≤ d }
Proof
  simp[open_in_euclidean] >> strip_tac >> qexists_tac ‘c’ >>
  simp[] >> CCONTR_TAC >> gs[SUBSET_DEF, ival_def] >>
  first_x_assum $ qspec_then ‘(a + c) / 2’ mp_tac >>
  simp[]
QED



Theorem closed_is_closed[simp]:
  closed_in euclidean { x | c ≤ x ∧ x ≤ d }
Proof
  simp[closed_in] >>
  ‘open_in euclidean {x | x < c} ∧ open_in euclidean {x | d < x}’
    by simp[] >>
  dxrule_all OPEN_IN_UNION >>
  ‘{x | d < x} ∪ {x | x < c} = UNIV DIFF {x | c ≤ x ∧ x ≤ d}’
    suffices_by simp[] >>
  simp[EXTENSION]
QED

Theorem singles_closed:
  closed_in euclidean {x}
Proof
  ‘{x} = {a | x ≤ a ∧ a ≤ x}’ by simp[EXTENSION] >>
  simp[]
QED

Theorem real_of_int_addN:
  real_of_int i + &n = real_of_int (i + &n)
Proof
  Cases_on ‘i’ >> simp[]
QED

Theorem real_of_int_LTN[simp]:
  real_of_int i < &j ⇔ i < &j
Proof
  Cases_on ‘i’ >> simp[]
QED

Theorem real_of_int_NLT[simp]:
  &i < real_of_int j ⇔ &i < j
Proof
  Cases_on ‘j’ >> simp[]
QED

Theorem integers_closed:
  closed_in euclidean { real_of_int i | T }
Proof
  simp[closed_in] >>
  ‘UNIV DIFF {real_of_int i | T} =
   BIGUNION { ival (real_of_int i) (real_of_int (i + 1)) | T }’
    by (simp[Once EXTENSION, PULL_EXISTS] >> qx_gen_tac ‘r’ >> eq_tac
        >- (simp[ival_def] >> strip_tac >> qexists_tac ‘flr r’ >>
            simp[INT_FLOOR_BOUNDS, real_of_int_addN,
                 Excl "real_of_int_add"] >>
            assume_tac (cj 1 INT_FLOOR_BOUNDS) >>
            pop_assum $ qspec_then ‘r’ mp_tac >> simp[REAL_LE_LT]) >>
        simp[ival_def] >> rpt strip_tac >>
        gs[real_of_int_addN, Excl "real_of_int_add"] >>
        intLib.ARITH_TAC) >>
  simp[] >> irule OPEN_IN_BIGUNION >> simp[PULL_EXISTS]
QED

(* next: between any two rational numbers there is an irrational number *)

Definition rational_def:
rational q ⇔ ∃a:int b:int. q = real_of_int a / real_of_int b ∧ b ≠ 0
End

Theorem rational_Nats[simp]:
  rational (&n)
Proof
  simp[rational_def] >> qexistsl_tac [‘&n’, ‘1’] >> simp[]
QED

Theorem rational_Ints[simp]:
  rational (real_of_int i)
Proof
  simp[rational_def] >> qexistsl_tac [‘i’, ‘1’] >> simp[]
QED

Theorem real_of_int_eq_n[simp]:
  (real_of_int i = &n ⇔ i = &n) ∧ (&n = real_of_int i ⇔ i = &n) ∧
  (real_of_int i = -&n ⇔ i = -&n) ∧ (-&n = real_of_int i ⇔ i = -&n)
Proof
   Cases_on ‘i’ >> simp[]
QED

Theorem rational_ADD_I:
rational a ∧ rational b ⇒ rational (a + b)
Proof
  rw[rational_def] >> simp[REAL_ADD_RAT,GSYM real_of_int_mul,Excl "real_of_int_mul",
                          GSYM real_of_int_add,Excl "real_of_int_add"] >>
  irule_at Any EQ_REFL >> simp[]
QED

Theorem rational_neg[simp]:
rational (- a) ⇔ rational a
Proof
  ‘∀a. rational a ⇒ rational (- a)’
    suffices_by metis_tac[REAL_NEG_NEG] >>
  rw[rational_def] >> simp[neg_rat,GSYM real_of_int_neg,Excl "real_of_int_neg"]  >>
  metis_tac[]
QED

Theorem irrational_ADD_I:
  rational a ∧ ¬rational b ⇒ ¬rational (a + b)
Proof
  CCONTR_TAC >> gs[] >>
  ‘rational (-a)’ by simp[] >>
  ‘a + b + (-a) = b’ by simp[] >> metis_tac[rational_ADD_I]
QED

Theorem irrational_ADD_I' = ONCE_REWRITE_RULE [REAL_ADD_COMM] irrational_ADD_I

Theorem rational_MULT_I:
  rational a ∧ rational b ⇒ rational (a * b)
Proof
  rw[rational_def] >>
  simp[mult_rat,Excl "REALMULCANON",Excl "RMUL_EQNORM1",Excl "RMUL_EQNORM2",
      GSYM real_of_int_mul,Excl "real_of_int_mul"] >>
  irule_at Any EQ_REFL >> simp[]
QED

Theorem rational_inv[simp]:
  rational (inv a) ⇔ rational a
Proof
  ‘∀a. rational a ⇒ rational (inv a)’
    suffices_by metis_tac[REAL_INV_INV] >>
  rw[rational_def] >>
  rename [‘real_of_int a / real_of_int b’] >>
  Cases_on ‘a = 0’ (* 2 *)
  >- (simp[REAL_DIV_ZERO] >> metis_tac[]) >>
  simp[real_div,Excl "REALMULCANON",Excl "RMUL_EQNORM1",Excl "RMUL_EQNORM2",
      REAL_INV_MUL',REAL_INV_INV] >>
  metis_tac[REAL_MUL_COMM]
QED

Theorem rational_DIV_I:
  rational a ∧ rational b ⇒ rational (a/b)
Proof
  simp[real_div, rational_MULT_I]
QED



Theorem irrational_MULT_I:
  a ≠ 0 ∧ rational a ∧ ¬rational b ⇒ ¬rational (a * b)
Proof
  CCONTR_TAC >> gs[] >>
  ‘rational (inv a)’ by simp[] >>
  ‘a * b * (inv a) = b’ by simp[] >> metis_tac[rational_MULT_I]
QED

Theorem irrational_MULT_I' = ONCE_REWRITE_RULE [REAL_MUL_COMM] irrational_MULT_I

Theorem irrational_DIVNUM_I:
  ¬rational a ∧ rational b ∧ b ≠ 0 ⇒ ¬rational (a/b)
Proof
  rpt strip_tac >>
  ‘rational (a/b * b)’ by simp[rational_MULT_I] >>
  gs[]
QED

Theorem irrational_DIVDEN_I:
  rational a ∧ ¬rational b ∧ a ≠ 0 ⇒ ¬rational (a/b)
Proof
  rpt strip_tac >>
  ‘rational (inv (a/b))’ by simp[] >>
  fs[real_div, Excl "rational_inv", REAL_INV_MUL', REAL_INV_INV] >>
  ‘rational (a * (inv a * b))’ by simp[rational_MULT_I] >> gs[]
QED

Theorem positive_rationals_natural:
  rational a ∧ 0 < a ⇒ ∃m n. n ≠ 0 ∧ a = &m / &n
Proof
  rw[rational_def] >> rename [`0 < real_of_int a / real_of_int b`] >>
  Cases_on `a` >> Cases_on `b` >> gs[real_div]
  >- (rename[`&a = (&_)⁻¹ * &(_ * b)`] >> qexistsl_tac [`a`, `b`] >>
      simp[]) >>
  rename[`-(-&a)⁻¹ * &b`] >> qexistsl_tac [`b`, `a`] >> simp[REAL_NEG_INV]
QED

Theorem sqrt_2_irrational:
  ¬rational (sqrt 2)
Proof
  strip_tac >> drule positive_rationals_natural >> simp[SQRT_POS_LT] >>
  rpt strip_tac >> CCONTR_TAC >> qabbrev_tac `k = LEAST k. ∃j. j ≠ 0 ∧ &k / &j = sqrt 2` >>
  `∃j. j ≠ 0 ∧ &k / &j = sqrt 2`
    by (simp[Abbr `k`] >> numLib.LEAST_ELIM_TAC >> rw[] >> metis_tac[]) >>
  `∀a b. b ≠ 0 ∧ &a / &b = sqrt 2 ⇒ k ≤ a`
    by (simp[Abbr `k`] >> numLib.LEAST_ELIM_TAC >> rw[] >>
        metis_tac[DECIDE ``x:num <= y ⇔ ¬ (y < x)``]) >>
  `(sqrt 2) pow 2 = 2` by simp[SQRT_POW2] >>
  `0 < k`
    by (CCONTR_TAC >> gs[] >>
        `0r pow 2 = 0` by simp[] >> `0r = 2r` by metis_tac[] >> gs[]) >>
  `&k = sqrt 2 * &j` by gvs[real_div] >> `&k pow 2 = (sqrt 2 * &j) pow 2` by simp[] >>
  qpat_x_assum `&k = _` $ K all_tac >> gs[POW_MUL, REAL_OF_NUM_POW] >>
  `EVEN (k ** 2)` by metis_tac[EVEN_EXISTS] >> gs[EVEN_EXP_IFF] >>
  `∃k0. k = k0 * 2` by gs[EVEN_EXISTS] >> qpat_x_assum `Abbrev _` $ K all_tac >>
  gvs[EXP_BASE_MULT] >> `2 * (k0 ** 2) = j ** 2` by simp[] >>
  `EVEN (j ** 2)` by metis_tac[EVEN_EXISTS] >> gs[EVEN_EXP_IFF] >>
  `∃j0. j = j0 * 2` by gs[EVEN_EXISTS] >> gvs[EXP_BASE_MULT] >>
  `k0 ** 2 = 2 * j0 ** 2` by simp[] >>
  `&(k0 ** 2) / &(j0 ** 2) = 2r`
    by (simp[real_div] >> simp[MULT_DIV]) >>
  `sqrt ( & (k0 ** 2) / & (j0 ** 2)) = sqrt 2` by simp[] >>
  qpat_x_assum `_ = 2r` $ K all_tac >>
  gs[GSYM REAL_OF_NUM_POW, SQRT_DIV, POW_2_SQRT] >>
  `2 * k0 ≤ k0` by metis_tac[] >> gs[]
QED

Theorem sqrt2_bounds[simp]:
  0 < sqrt 2 ∧ sqrt 2 < 2
Proof
  conj_tac >- simp[SQRT_POS_LT] >>
  CCONTR_TAC >> gs[REAL_NOT_LT] >>
  drule_at (Pos last) POW_LE >> simp[] >>
  qexists_tac ‘2’ >> simp[SQRT_POW_2]
QED


Theorem rationals_bracket_irrationals:
  ∀a b. rational a ∧ rational b ∧ a < b ⇒ ∃c. ¬rational c ∧ a < c ∧ c < b
Proof
  rw[] >> qexists_tac ‘(b - a) * sqrt 2 / 2 + a’ >> rpt conj_tac
  >- (ONCE_REWRITE_TAC [REAL_ADD_COMM] >> irule irrational_ADD_I >>
      simp[] >> REWRITE_TAC[real_div] >>
      irule irrational_MULT_I' >> simp[] >>
      irule irrational_MULT_I' >> simp[real_sub] >>
      simp[rational_ADD_I, sqrt_2_irrational])
  >- (simp[REAL_LT_ADDL] >> irule REAL_LT_MUL >> simp[]) >>
  simp[GSYM REAL_LT_SUB_LADD]
QED

Theorem density_lemma'[local]:
  ¬rational a ∧ rational b ⇒
  (a < b ⇒ ∃c. ¬rational c ∧ a < c ∧ c < b) ∧
  (b < a ⇒ ∃c. ¬rational c ∧ b < c ∧ c < a)
Proof
  strip_tac >> wlog_tac ‘a < b’ [‘a’, ‘b’]
  >- (gs[] >> strip_tac >>
      first_x_assum $ qspecl_then [‘-a’, ‘-b’] mp_tac >> simp[] >>
      disch_then $ qx_choose_then ‘c0’ strip_assume_tac >>
      qexists_tac ‘-c0’ >> simp[]) >>
  simp [] >> qexists_tac ‘(a + b) / 2’ >> simp[] >>
  simp[irrational_ADD_I', irrational_DIVNUM_I]
QED

Theorem irrationals_dense:
  ∀a b. a < b ⇒ ∃r. ¬rational r ∧ a < r ∧ r < b
Proof
  rpt strip_tac >>
  map_every Cases_on [‘rational a’, ‘rational b’]
  >- metis_tac[rationals_bracket_irrationals]
  >- metis_tac[density_lemma']
  >- metis_tac[density_lemma'] >>
  qabbrev_tac ‘m = (a + b) / 2’ >>
  ‘a < m ∧ m < b’ by simp[Abbr‘m’] >>
  Cases_on ‘rational m’ >> simp[SF SFY_ss] >>
  drule_all (cj 1 density_lemma') >> metis_tac[REAL_LT_TRANS]
QED

Theorem rationals_dense:
  ∀a b. a < b ⇒ ∃r. rational r ∧ a < r ∧ r < b
Proof
  rpt strip_tac >>
  ‘0 < b - a’ by simp[] >>
  dxrule_then (qspec_then ‘1’ $ qx_choose_then ‘m’ assume_tac) REAL_ARCH >>
  gs[REAL_SUB_LDISTRIB] >>
  ‘a * &m + 1 < b * &m’ by simp[] >>
  drule_then (qx_choose_then ‘d’ strip_assume_tac) ints_exist_in_gaps >>
  ‘m ≠ 0’ by (strip_tac >> gs[]) >>
  ‘a < real_of_int d / &m ∧ real_of_int d / &m < b’ by simp[] >>
  ‘rational (real_of_int d / &m)’ by simp[rational_DIV_I] >>
  metis_tac[]
QED

Theorem rationals_not_open_euclidean:
  ¬open_in euclidean { r | rational r }
Proof
  simp[open_in_euclidean] >> qexists_tac ‘0’ >> simp[] >>
  rpt gen_tac >> reverse (Cases_on ‘a < b’)
  >- simp[ival_def] >>
  disj2_tac >> simp[SUBSET_DEF, ival_def] >>
  metis_tac[irrationals_dense]
QED

Theorem rationals_not_closed_euclidean:
  ¬closed_in euclidean { r | rational r }
Proof
  simp[closed_in, open_in_euclidean] >> qexists_tac ‘sqrt 2’ >>
  simp[sqrt_2_irrational] >> rpt strip_tac >>
  Cases_on ‘a < b’ >> simp[ival_def, SUBSET_DEF] >>
  metis_tac[rationals_dense]
QED

Theorem exercise_2_1_1:
  a < b ⇒ ¬open_in euclidean { r | a ≤ r ∧ r < b } ∧
          ¬closed_in euclidean {r  | a ≤ r ∧ r < b } ∧
          ¬open_in euclidean {r | a < r ∧ r ≤ b } ∧
          ¬closed_in euclidean { r | a < r ∧ r ≤ b}
Proof
  rw[open_in_euclidean, closed_in]
  >- (qexists_tac ‘a’ >> simp[] >> qx_genl_tac [‘c’, ‘d’] >>
      Cases_on ‘a ∈ ival c d’ >> simp[] >>
      gs[ival_def, SUBSET_DEF] >>
      ‘∃ac. c < ac ∧ ac < a’ by metis_tac[rationals_dense] >>
      qexists_tac ‘ac’ >> simp[])
  >- (simp[ival_def, SUBSET_DEF] >> qexists_tac ‘b’ >> simp[]>>
      qx_genl_tac [‘c’, ‘d’] >>
      map_every Cases_on [‘c < b’, ‘b < d’] >> simp[] >>
      ‘∃cb. max a c < cb ∧ cb < b’
        by metis_tac[rationals_dense, REAL_MAX_LT]>>
      qexists_tac ‘cb’ >> gs[REAL_MAX_LT])
  >- (qexists_tac ‘b’ >> simp[ival_def, SUBSET_DEF] >>
      qx_genl_tac [‘c’, ‘d’] >>
      map_every Cases_on [‘c < b’, ‘b < d’] >> simp[] >>
      ‘∃bd. b < bd ∧ bd < d’ by metis_tac[rationals_dense] >>
      qexists_tac ‘bd’ >> simp[])
  >- (simp[ival_def, SUBSET_DEF] >> qexists_tac ‘a’ >> simp[]>>
      qx_genl_tac [‘c’, ‘d’] >>
      map_every Cases_on [‘c < a’, ‘a < d’] >> simp[] >>
      ‘∃ab. a < ab ∧ ab < min b d’
        by metis_tac[rationals_dense, REAL_LT_MIN]>>
      qexists_tac ‘ab’ >> gs[REAL_LT_MIN])
QED

Theorem exercise_2_1_2:
  closed_in euclidean { r | a ≤ r } ∧
  closed_in euclidean { r | r ≤ a }
Proof
  simp[closed_in] >>
  ‘UNIV DIFF {r | a ≤ r } = {r | r < a} ∧
   UNIV DIFF {r | r ≤ a } = {r | a < r}’
    suffices_by simp[] >>
  simp[EXTENSION]
QED

Theorem exercise_2_1_3:
  ∃A. (∀a. a ∈ A ⇒ closed_in euclidean a) ∧
      INFINITE A ∧
      ¬closed_in euclidean (BIGUNION A)
Proof
  qexists_tac ‘{ {r} | 0 < r ∧ r < 1 }’>>
  simp[PULL_EXISTS, singles_closed] >>
  simp[closed_in] >> conj_tac
  >- (simp[infinite_num_inj] >>
      qexists_tac ‘λn. {inv (&(n + 2))}’  >>
      simp[INJ_IFF]) >>
  ‘BIGUNION {{r} | 0 < r ∧ r < 1} = ival 0 1’
    by simp[Once EXTENSION, PULL_EXISTS, ival_def] >>
  simp[] >> simp[open_in_euclidean] >>
  qexists_tac ‘0’ >> simp[ival_def, SUBSET_DEF] >>
  qx_genl_tac [‘c’, ‘d’] >>
  map_every Cases_on  [‘c < 0’, ‘0 < d’] >> simp[] >>
  ‘∃d0. 0 < d0 ∧ d0 < min 1 d’
    by metis_tac[rationals_dense, REAL_MIN_LT, REAL_LT_MIN,
                 REAL_LT_01] >>
  qexists_tac ‘d0’ >> gs[REAL_LT_MIN]
QED


Theorem real_of_int_Nmul:
 &n * real_of_int i = real_of_int (&n * i)
Proof
 Cases_on ‘i’ >> simp[]
QED

Theorem real_of_int_NLE[simp]:
 &i ≤ real_of_int j ⇔ &i ≤ j
Proof
  Cases_on ‘j’ >> simp[integerTheory.INT_NOT_LE]
QED

Theorem exercise_2_1_4i:
  ¬open_in euclidean { real_of_int i | T }
Proof
  simp[open_in_euclidean, PULL_EXISTS] >>
  qexists_tac ‘0’ >> qx_genl_tac [‘c’, ‘d’] >>
  Cases_on ‘real_of_int 0 ∈ ival c d’ >> simp[] >>
  gs[ival_def, SUBSET_DEF] >>
  Cases_on ‘1 ≤ d’
  >- (qexists_tac ‘1 / 2’ >> simp[] >>
      ‘0 < 1/2 ∧ 1/2 < 1’ by simp[] >>
      rpt strip_tac >>
      pop_assum (SUBST_ALL_TAC o SYM) >>
      gs[] >>
      qspecl_then [‘0’, ‘i’] mp_tac integerTheory.INT_DISCRETE >>
      simp[])
  >- (qexists_tac ‘d / 2’ >> simp[] >>
      REWRITE_TAC [real_div] >> simp[] >> rpt strip_tac >> gvs[] >>
      gs[real_of_int_Nmul,Excl "real_of_int_mul"] >>
      pop_assum mp_tac >> intLib.ARITH_TAC)
QED

open intrealTheory;

Theorem ival_without_int:
  ∀x. (¬∃z:int. x = real_of_int z) ⇒
      ∃a b. x ∈ ival a b ∧ ∀z:int. real_of_int z ∉ ival a b
Proof
  simp[ival_def] >> rpt strip_tac >>
  wlog_tac ‘0 ≤ x’ [‘x’]
  >- (first_x_assum $ qspec_then ‘-x’ assume_tac >> gvs[] >>
      ‘∀z. -x ≠ real_of_int z’
        by (rpt strip_tac >>
            metis_tac[REAL_NEG_NEG,real_of_int_neg]) >>
      first_x_assum drule >> strip_tac >>
      qexistsl_tac [‘-b’,‘-a’] >> gvs[] >> strip_tac >>
      first_x_assum $ qspec_then ‘-z’ mp_tac >> rpt strip_tac >>
      gvs[])
  >- (qexistsl_tac [‘&(flr x)’,‘&(clg x)’] >> rpt strip_tac (* 3 *)
      >- (gvs[REAL_LT_LE,NUM_FLOOR_LE] >> strip_tac >>
          metis_tac[real_of_int_num])
      >- (gvs[REAL_LT_LE,LE_NUM_CEILING] >> metis_tac[real_of_int_num]) >>
      CCONTR_TAC >> fs[] >> Cases_on ‘x ≤ 0 ∨ x = &flr x’ >> gvs[] (* 3 *)
      >- (‘x = 0’ by gvs[] >> metis_tac[real_of_int_num])
      >- metis_tac[integerTheory.INT_LT_ANTISYM] >>
      irule integerTheory.INT_DISCRETE >>
      ‘&(flr x + 1) = (&flr x) + 1:int’
        by gvs[GSYM integerTheory.INT_ADD] >> metis_tac[])
QED

Theorem exercise_2_1_4ii:
  closed_in euclidean {&(z : num) | P z}
Proof
  simp[closed_in,open_in_euclidean] >> rpt strip_tac >>
  Cases_on ‘∃z:num. x = &z’
  >- (gvs[] >> qexistsl_tac [‘&z - 1/2’,‘&z + 1/2’] >>
      simp[ival_def,SUBSET_DEF] >> rpt strip_tac
      >- simp[REAL_LT_SUB_RADD]
      >> gvs[] >> ‘z = z'’ suffices_by (strip_tac >> gvs[]) >>
      rename [‘&a - 1/2 < &b’] >>
      ‘2 * &a - 1 < 2 * &b ∧ 2 * &b < 2 * &a + 1’
        by
        (strip_tac >> rev_drule REAL_LT_LMUL_IMP >> strip_tac >>
         first_x_assum $ qspec_then ‘2’ mp_tac >> strip_tac >>
         ‘0r < 2r’ by simp[] >> first_x_assum drule >> strip_tac
         >- (‘2 * (&a − 1 / 2) = 2 * &a − 1’ suffices_by metis_tac[] >>
             simp[REAL_SUB_LDISTRIB])
         >- (‘2 * &b < 2 * (&a + 1 / 2)’  by simp[REAL_LT_LMUL_IMP] >>
             ‘2 * (&a + 1 / 2) = 2 * &a + 1’ suffices_by metis_tac[] >>
             simp[REAL_ADD_LDISTRIB])) >>
      wlog_tac ‘a < b’ [] (* 2 *)
      >- (CCONTR_TAC >> ‘b < a’ by simp[] >>
          irule integerTheory.INT_DISCRETE >>
          qexistsl_tac [‘&a’,‘&b’] >> simp[REAL_LT] >> gvs[REAL_LT_SUB_RADD])
      >> CCONTR_TAC >> irule integerTheory.INT_DISCRETE >>
      qexistsl_tac [‘&b’,‘&a’] >> simp[REAL_LT] >> gvs[REAL_LT_SUB_RADD]) >>
  reverse (Cases_on ‘∃z:int. x = real_of_int z’)
  >- (drule ival_without_int >> strip_tac >>
      qexistsl_tac [‘a’,‘b’] >> gvs[SUBSET_DEF] >>
      rpt strip_tac >> metis_tac[real_of_int_num]) >>
  gvs[] >>
  ‘z < 0’ by (Cases_on ‘z’ >> gvs[]) >>
  qexistsl_tac [‘real_of_int z - 1’,‘real_of_int z + 1’] >>
  gvs[ival_def,SUBSET_DEF] >> rpt strip_tac >> gvs[] >>
  rename [‘real_of_int z - 1 < &n’] >>
  gs[real_of_int_addN, Excl "real_of_int_add"] >>
  qpat_x_assum ‘z < 0’ mp_tac >> qpat_x_assum ‘&n < z + 1’ mp_tac >>
  intLib.ARITH_TAC
QED

(*
Theorem ival_11[simp]:
  ival a b = ival c d ⇔ a = c ∧ b = d
Proof
  simp[EXTENSION, ival_def, Once EQ_IMP_THM] >>
  rpt strip_tac >> cheat
QED
*)

Theorem prop2_2_1:
  open_in euclidean s ⇔ ∃P. s = BIGUNION { ival a b | P a b }
Proof
  simp[EQ_IMP_THM, PULL_EXISTS, OPEN_IN_BIGUNION] >>
  simp[open_in_euclidean] >> strip_tac >>
  gs[GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >>
  rename [‘ival (F1 _) (F2 _)’] >>
  qexists_tac ‘λa b. ∃x. a = F1 x ∧ b = F2 x ∧ x ∈ s’ >>
  simp[Once EXTENSION] >> simp[EQ_IMP_THM] >> rpt strip_tac >>
  simp[PULL_EXISTS] >- metis_tac[] >>
  gvs[] >> first_x_assum drule >>
  metis_tac[SUBSET_DEF]
QED

(* example 2.2.3 *)
Theorem ivals_basis:
  basis { ival a b | T } euclidean
Proof
  simp[basis_def, PULL_EXISTS] >> rpt strip_tac >>
  drule_then strip_assume_tac (iffLR prop2_2_1) >>
  simp[] >> irule_at Any EQ_REFL >> simp[SUBSET_DEF, PULL_EXISTS] >>
  metis_tac[]
QED

Definition open_rectangle:
  open_rectangle (a: real) b c d = {(x, y) | a < x ∧ x < b ∧ c < y ∧ y < d}
End

Definition open_rectangles:
  open_rectangles = {open_rectangle a b c d | a < b ∧ c < d}
End

(* example 2.2.9 *)
Theorem open_rectangle_topology_exists:
  (* triangle inequality implies *)
  ∃t. topspace t = UNIV ∧ basis open_rectangles t
Proof
  simp[prop_2_2_8] >> rw[] (* 2 *)
  >- (simp[Once EXTENSION, open_rectangles, PULL_EXISTS, open_rectangle, FORALL_PROD] >>
      qx_genl_tac [`x`, `y`] >> qexistsl_tac [`x-1`, `x+1`, `y-1`, `y+1`] >>
      simp[])
  >> Cases_on `b1 ∩ b2 = ∅` (* 2 *)
  >- (qexists_tac `∅` >> simp[])
  >> gvs[open_rectangles] >>
  rename [`open_rectangle a b c d ∩ open_rectangle h i j k ≠ ∅`] >>
  wlog_tac `a ≤ h` [`a`, `b`, `c`, `d`, `h`, `i`, `j`, `k`] (* 2 *)
  >- (`h ≤ a` by simp[] >> metis_tac[INTER_COMM])
  >> `h < b`
        by (CCONTR_TAC >> gs[REAL_NOT_LT] >> qpat_x_assum `_ ∩ _ ≠ _` mp_tac >>
            simp[EXTENSION, open_rectangle, FORALL_PROD]) >>
  Cases_on `c ≤ j` (* 2 *)
  >- (`j < d`
        by (CCONTR_TAC >> gs[REAL_NOT_LT] >> qpat_x_assum `_ ∩ _ ≠ _` mp_tac >>
            simp[EXTENSION, open_rectangle, FORALL_PROD]) >>
      qexists_tac `{open_rectangle h (min b i) j (min d k)}` >> simp[] >> conj_tac
      >- (irule_at Any EQ_REFL >> simp[REAL_LT_MIN])
      >> simp[open_rectangle, EXTENSION, FORALL_PROD] >> qx_genl_tac [`x`, `y`] >>
      simp[EQ_IMP_THM, REAL_LT_MIN])
  >> gs[REAL_NOT_LE] >>
  `c < k`
    by (CCONTR_TAC >> gs[REAL_NOT_LT] >> qpat_x_assum `_ ∩ _ ≠ _` mp_tac >>
            simp[EXTENSION, open_rectangle, FORALL_PROD]) >>
  qexists_tac `{open_rectangle h (min b i) c (min d k)}` >> simp[] >> conj_tac
      >- (irule_at Any EQ_REFL >> simp[REAL_LT_MIN])
      >> simp[open_rectangle, EXTENSION, FORALL_PROD] >> qx_genl_tac [`x`, `y`] >>
      simp[EQ_IMP_THM, REAL_LT_MIN]
QED

Theorem negx_squared[simp]:
  (-a) pow 2 = a pow 2
Proof
  simp[Once REAL_NEG_MINUS1]
QED

Definition tri_ineq:
  tri_ineq = ∀x y u v a b. sqrt ((x - a) pow 2 + (y - b) pow 2) ≤
                           sqrt ((x - u) pow 2 + (y - v) pow 2) +
                           sqrt ((u - a) pow 2 + (v - b) pow 2)
End

Definition D_def:
  D = {(x,y) | x pow 2 + y pow 2 < 1 }
End

Definition R_def:
  R a b =
  let r = sqrt (a pow 2 + b pow 2);
      d = (1 - r)/8
  in open_rectangle (a - d) (a + d) (b - d) (b + d)
End
           
Theorem exercise_2_2_1_i:
  tri_ineq ⇒
  ∀a b. (a,b) ∈ D ⇒ R a b ⊆ D 
Proof
  SRW_TAC [] [D_def,R_def] >> irule SUBSET_TRANS >>
  qexists_tac ‘{(x,y)| sqrt((x-a) pow 2 + (y - b) pow 2) < 1 - r}’ >>
  conj_tac (*2*)
  >- (simp[SUBSET_DEF,open_rectangle,PULL_EXISTS] >>
      qabbrev_tac ‘s = 1 - r’ >> qx_genl_tac [‘x’,‘y’] >> strip_tac >>
      irule REAL_LET_TRANS >>
      qexists_tac ‘sqrt (d pow 2 + d pow 2)’ >> strip_tac (* 2 *)
      >- (simp[Abbr‘d’] >>
          ‘s² / 64 + s² / 64 = s pow 2 / 32’
            by
            (simp[REAL_DIV_ADD,REAL_DOUBLE] >>
             REWRITE_TAC [real_div] >> simp[]) >>
          simp[SQRT_DIV] >>
          ‘0 ≤ s’
            by (simp[Abbr‘s’,Abbr‘r’,REAL_SUB_LE] >>
                SUBST1_TAC (GSYM SQRT_1) >> irule SQRT_MONO_LE >>
                simp[REAL_LE_POW2,REAL_LE_ADD]) >>
          simp[POW_2_SQRT,REAL_LT_LDIV_EQ,SQRT_POS_LT] >>
          ‘0 < s ∧ 1 < sqrt 32’ suffices_by simp[] >>
          reverse conj_tac
          >- (‘0r ≤ 1’ by simp[] >> dxrule SQRT_MONO_LT >> simp[SQRT_1])>>
          simp[Abbr‘r’, Abbr‘s’, REAL_SUB_LT] >>
          ONCE_REWRITE_TAC [GSYM SQRT_1] >>
          irule SQRT_MONO_LT >> simp[REAL_LE_POW2, REAL_LE_ADD]) >>
      irule SQRT_MONO_LE >> simp[REAL_LE_POW2, REAL_LE_ADD] >>
      irule REAL_LE_ADD2 >> conj_tac
      >- (Cases_on ‘a ≤ x’ >- (irule POW_LE >> simp[]) >>
          ‘(x - a)² = (a - x)²’
            suffices_by (simp[] >> strip_tac >>
                         irule POW_LE >> simp[]) >>
          ‘a - x = -(x-a)’ by simp[] >> simp[]) >>
      Cases_on ‘b ≤ y’ >- (irule POW_LE >> simp[]) >>
      ‘(y - b)² = (b - y)²’
        suffices_by (simp[] >> strip_tac >>
                     irule POW_LE >> simp[]) >>
      ‘b - y = -(y-b)’ by simp[] >> simp[]) >>
  simp[SUBSET_DEF, PULL_EXISTS] >>
  qx_genl_tac [‘x’, ‘y’] >> simp[Abbr‘r’] >>
  simp[REAL_LT_SUB_LADD] >> strip_tac >>
  qsuff_tac ‘sqrt (x pow 2 + y pow 2) < sqrt (1)’
  >- (strip_tac >>
      drule_at Any REAL_POW_LT2 >>
      disch_then $ qspec_then ‘2’ MP_TAC >> simp[] >>
      simp[SQRT_POS_LE,REAL_LE_ADD,SQRT_POW_2] ) >>
  simp[SQRT_1] >>
  irule REAL_LET_TRANS >>
  FIRST_ASSUM $ irule_at Any >>
  gs[tri_ineq] >>
  FIRST_X_ASSUM $ qspecl_then [‘x’,‘y’,‘a’,‘b’,‘0’,‘0’] mp_tac >>
                simp[]
QED

Theorem exercise_2_2_1_ii:
  tri_ineq ⇒
  D = BIGUNION {R a b | (a,b) ∈ D}
Proof
  strip_tac >>
  irule SUBSET_ANTISYM >>
  reverse conj_tac
  >- simp[BIGUNION_SUBSET,PULL_EXISTS,exercise_2_2_1_i] >>
     
QED

val _ = export_theory();
