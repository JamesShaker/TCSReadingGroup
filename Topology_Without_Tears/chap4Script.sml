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

(*hint: Y is open in subtopology τ Y*)        
Theorem exercise_4_1_10:
  Y ⊆ topspace τ ⇒
  ({s | open_in (subtopology τ Y) s} ⊆ {s | open_in τ s} ⇔ open_in τ Y)
Proof
  strip_tac >>
  rw[SUBSET_DEF,OPEN_IN_SUBTOPOLOGY,PULL_EXISTS,EQ_IMP_THM,OPEN_IN_INTER] >>
  first_x_assum $ qspec_then ‘topspace τ’ assume_tac >>
  gs[SUBSET_INTER2]
QED

Theorem exercise_4_1_11:
  A ⊆ topspace τ ∧ B ⊆ topspace τ ∧ connected (subtopology τ A) ∧
  connected (subtopology τ B) ∧ A ∩ B ≠ ∅ ⇒ connected (subtopology τ (A ∪ B))
Proof
  rw[connected_def,TOPSPACE_SUBTOPOLOGY,clopen_def,OPEN_IN_SUBTOPOLOGY,
     CLOSED_IN_SUBTOPOLOGY] >> eq_tac >> strip_tac (* 3 *)
  >- (gvs[] >> rename [‘open_in τ X’,‘closedSets τ Y’] >>
      ‘X ∩ A = Y ∩ A ∧ X ∩ B = Y ∩ B’ by
        (pop_assum mp_tac >> simp[EXTENSION] >> metis_tac[]) >>
      ‘(X ∩ A = topspace τ ∩ A ∨ X ∩ A = {}) ∧
       (X ∩ B = topspace τ ∩ B ∨ X ∩ B = {})’
        by metis_tac[] >>
      gs[SUBSET_DEF,EXTENSION] >> metis_tac[])
  >- metis_tac[CLOSED_IN_TOPSPACE,OPEN_IN_TOPSPACE] >>
  metis_tac[OPEN_IN_EMPTY,CLOSED_IN_EMPTY,INTER_EMPTY]
QED  

val _ = export_theory();

