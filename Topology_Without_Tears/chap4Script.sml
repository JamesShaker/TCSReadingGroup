open HolKernel Parse boolLib bossLib;
open topologyTheory pred_setTheory
open chap1Theory chap2_2Theory chap3Theory;

val _ = new_theory "chap4";

(* ===============================
      Chapter 4. Homeomorphisms
   =============================== *)

(* subspace topology is already defined in HOL
   as subtopology *)

Theorem example_4_1_4:
	basis B t ⇒
	basis {b ∩ Y | b ∈ B} (subtopology t Y)
Proof
	rw[basis_def, OPEN_IN_SUBTOPOLOGY]
	>- metis_tac[]
	>> first_x_assum drule >> rw[] >>
	qexists_tac `{b ∩ Y | b ∈ u}` >> rw[]
	>- (rw[SUBSET_DEF] >> metis_tac[SUBSET_DEF])
	>> rw[Once EXTENSION] >> simp[PULL_EXISTS] >>
	metis_tac[]
QED

Theorem exercise_4_1_4:
  A ⊆ B (* ∧ B ⊆ topspace τ *) ⇒
  subtopology τ A = subtopology (subtopology τ B) A
Proof
  rw[TOPOLOGY_EQ, OPEN_IN_SUBTOPOLOGY, PULL_EXISTS] >>
  ‘B ∩ A = A’ by gs[EXTENSION, SUBSET_DEF, SF CONJ_ss] >>
  ASM_REWRITE_TAC [GSYM INTER_ASSOC]
QED

Theorem exercise_4_1_5:
  closed_in (subtopology τ Y) Z ⇔ ∃A. Z = A ∩ Y ∧ closed_in τ A
Proof
  rw[OPEN_IN_SUBTOPOLOGY, closed_in, TOPSPACE_SUBTOPOLOGY, EQ_IMP_THM] (* 4 *) >~
  [‘topspace τ ∩ Y DIFF Z = A ∩ Y’]
  >- (qexists_tac ‘topspace τ DIFF A’ >>
      simp[DIFF_DIFF_SUBSET, OPEN_IN_SUBSET] >>
      simp[DIFF_INTER] >> gs[EXTENSION] >> metis_tac[SUBSET_DEF]) >~
  [‘A ∩ Y ⊆ topspace τ’]
  >- metis_tac[SUBSET_TRANS, INTER_SUBSET] >~
  [‘A ∩ Y ⊆ Y’] >- simp[INTER_SUBSET] >>
  rename[‘open_in τ (topspace τ DIFF A)’] >>
  first_assum $ irule_at (Pat ‘open_in _ _’) >>
  gs[EXTENSION, SUBSET_DEF] >> metis_tac[]
QED

Theorem exercise_4_1_6[simp]:
  subtopology (discrete_topology X) Y = discrete_topology (X ∩ Y)
Proof
  simp[TOPOLOGY_EQ, OPEN_IN_SUBTOPOLOGY, EQ_IMP_THM] >> rpt strip_tac >>
  gvs[] (* 2 *) >>
  metis_tac[SUBSET_DEF, IN_INTER, EXTENSION]
QED

Theorem exercise_4_1_7[simp]:
  subtopology (indiscrete_topology X) Y = indiscrete_topology (X ∩ Y)
Proof
  simp[TOPOLOGY_EQ, OPEN_IN_SUBTOPOLOGY, EQ_IMP_THM] >> rpt strip_tac >>
  gvs[] >> simp[SF DNF_ss]
QED

val _ = export_theory();
