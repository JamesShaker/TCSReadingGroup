open HolKernel Parse boolLib bossLib;

open pred_setTheory intrealTheory
open topologyTheory chap1Theory realTheory

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





val _ = export_theory();
