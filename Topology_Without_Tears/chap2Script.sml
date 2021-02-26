open HolKernel Parse boolLib bossLib;

open pred_setTheory intrealTheory
open topologyTheory chap1Theory realTheory
open transcTheory;
open arithmeticTheory;

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


Theorem irrational_MULT_I:
  a ≠ 0 ∧ rational a ∧ ¬rational b ⇒ ¬rational (a * b)
Proof
  CCONTR_TAC >> gs[] >>
  ‘rational (inv a)’ by simp[] >>
  ‘a * b * (inv a) = b’ by simp[] >> metis_tac[rational_MULT_I]
QED

Theorem irrational_MULT_I' = ONCE_REWRITE_RULE [REAL_MUL_COMM] irrational_MULT_I


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

Theorem rationals_dense:
  ∀a b. a < b ⇒ ∃r. rational r ∧ a < r ∧ r < b
Proof
  rpt strip_tac >>
  ‘0 < b - a ’ by simp[] >>
  dxrule_then (qspec_then ‘1’ strip_assume_tac) REAL_ARCH >>
  gs[REAL_SUB_LDISTRIB] >>
  ‘a * &n + 1 < b * &n’ by simp[] >>
  (* See : https://math.stackexchange.com/questions/421580/is-there-a-rational-number-between-any-two-irrationals *)
  (* still need, existence of an integer between two reals further than 1 apart *)
  cheat
QED

Theorem irrationals_bracketted:
  ∀a b. a < b ⇒ ∃c. ¬rational c ∧ a < c ∧ c < b
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


Theorem rationals_not_open_euclidean:
  ¬open_in euclidean { r | rational r }
Proof
  simp[open_in_euclidean] >> qexists_tac ‘0’ >> simp[] >>
  rpt gen_tac >> Cases_on ‘a < b’
  >- (disj2_tac >> simp[SUBSET_DEF, ival_def] >>
      reverse (Cases_on ‘rational a’)
      >- (Cases_on ‘rational b’
          >- (qexists_tac ‘(a + b) / 2’ >> simp[] >>
              REWRITE_TAC[real_div] >> irule irrational_MULT_I' >>
              simp[irrational_ADD_I']) >>



val _ = export_theory();
