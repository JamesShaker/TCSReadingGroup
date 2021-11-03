open HolKernel Parse boolLib bossLib;

open pred_setTheory topologyTheory
open chap2Theory chap4Theory chap3Theory

val _ = new_theory "chap4_instances";

Theorem open_in_euclidean_UNIV[simp]:
  open_in euclidean UNIV
Proof
  ‘UNIV = topspace euclidean’
    suffices_by simp[OPEN_IN_TOPSPACE, Excl "topspace_euclidean"] >>
  simp[]
QED

Theorem example_4_1_6:
  subtopology euclidean ints = discrete_topology ints
Proof
  simp[TOPOLOGY_EQ, OPEN_IN_SUBTOPOLOGY] >>
  simp[EQ_IMP_THM, SUBSET_INTER, PULL_EXISTS] >> rpt strip_tac >>
  Cases_on ‘s = ints’
  >- (qexists_tac ‘UNIV’ >> simp[]) >>
  ‘closed_in euclidean (ints DIFF s)’ by cheat >> cheat
QED

val _ = export_theory();
