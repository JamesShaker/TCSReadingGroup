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

val _ = export_theory();