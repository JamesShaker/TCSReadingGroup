open HolKernel Parse boolLib bossLib;

open pred_setTheory
(* inherit from existing topology theory *)
open topologyTheory

val _ = new_theory "chap1";

(*

        open_in : 'a topology -> 'a set set
        topology : 'a set set -> 'a topology
        topspace : 'a toplogoy -> 'a set


Not every set of sets corresponds to a topology, but the topology
function is total, so if it is passed a set that doesn't correspond to
a topology, it's behaviour is unspecified.

“open_in t s”     "s is an open set in topology t"

     or

“s ∈ open_in t”

     or

Will maybe

“s ∈ openSets t”

*)

Theorem SING_INTER[local]:
  {a} ∩ (a INSERT B) = {a} ∧ (a INSERT B) ∩ {a} = {a}
Proof
  csimp[EXTENSION]
QED

Theorem INTER_EQ[local]:
  (x ∩ y = x ⇔ x ⊆ y) ∧ (y ∩ x = x ⇔ x ⊆ y)
Proof
  simp[SUBSET_DEF, EXTENSION] >> metis_tac[]
QED

Theorem POW_INSERT':
  POW (x INSERT s) = POW s ∪ { x INSERT t | t ∈ POW s }
Proof
  simp[Once EXTENSION, POW_INSERT] >> metis_tac[]
QED

Theorem pow6[local] =
        (SIMP_CONV (srw_ss()) [POW_EQNS] THENC
         SIMP_CONV (srw_ss()) [LET_THM, GSYM INSERT_SING_UNION])
        “POW {a;b;c;d;e;f}”

Theorem example1_1_2:
  (* does it matter if elements a..f are distinct? *)
  istopology {{a;b;c;d;e;f}; ∅; {a}; {c;d}; {a;c;d}; {b;c;d;e;f}}
Proof
  simp[istopology] >> reverse (rw[])
  >- (‘k ∈ POW {{a;b;c;d;e;f}; ∅; {a}; {c;d}; {a;c;d}; {b;c;d;e;f}}’
        by simp[IN_POW] >>
      pop_assum mp_tac >> pop_assum (K ALL_TAC) >>
      simp[pow6] >> rw[] >> ONCE_REWRITE_TAC[EXTENSION] >> dsimp[] >> metis_tac[]) >>
  simp[SING_INTER, INTER_EQ] >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem example1_1_3:
  ALL_DISTINCT [a;b;c;d;e] ⇒
  ¬istopology {{a;b;c;d;e};∅;{a};{c;d};{a;c;e};{b;c;d}}
Proof
  simp[istopology] >> strip_tac >> disj2_tac >>
  qexists_tac ‘{{c;d}; {a;c;e}}’ >> simp[SUBSET_DEF] >> rw[] >>
  ONCE_REWRITE_TAC[EXTENSION] >> simp[] >> metis_tac[NOT_INSERT_EMPTY]
QED

Theorem example1_1_4:
  ALL_DISTINCT[a;b;c;d;e;f] ⇒
  ¬istopology {{a;b;c;d;e;f}; ∅; {a}; {f}; {a;f}; {a;c;f}; {b;c;d;e;f}}
Proof
  simp[istopology] >> strip_tac >> disj1_tac >>
  qexistsl_tac [‘{a;c;f}’, ‘{b;c;d;e;f}’] >> simp[SING_INTER, INTER_EQ] >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem example1_1_5:
  ¬istopology (univ(:num) INSERT {s | FINITE s})
Proof
  simp[istopology] >> disj2_tac >>
  qexists_tac ‘{{n} | 2 ≤ n }’ >>
  simp[SUBSET_DEF, PULL_EXISTS] >> rw[] >>
  ONCE_REWRITE_TAC [EXTENSION] >> simp[]
  >- (qexists_tac ‘1’ >> gen_tac >> Cases_on ‘1 ∈ s’ >> simp[] >> gen_tac >>
      Cases_on ‘2 ≤ n’ >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >>
  ‘INJ (λn. {n + 2}) UNIV {{n} | 2 ≤ n}’
    by simp[INJ_IFF] >>
  drule INFINITE_INJ >> simp[]
QED

Definition discrete_topology_def:
  discrete_topology X = topology (POW X)
End

Theorem openSets_discrete:
  open_in (discrete_topology X) s ⇔ s ⊆ X
Proof
  ‘open_in (discrete_topology X) = POW X’ suffices_by simp[] >>
  simp[discrete_topology_def] >> simp[GSYM (cj 2 topology_tybij)] >>
  simp[istopology] >> conj_tac
  >- simp[IN_POW, SUBSET_DEF] >>
  simp[SUBSET_DEF, IN_POW]>> metis_tac[]
QED

Definition indiscrete_topology_def:
  indiscrete_topology X = topology {∅; X}
End

Theorem openSets_indiscrete:
  open_in (indiscrete_topology X) s ⇔ s = X ∨ s = ∅
Proof
  ‘open_in (indiscrete_topology X) = {∅; X}’ suffices_by (simp[] >> metis_tac[]) >>
  simp[indiscrete_topology_def] >> simp[GSYM (cj 2 topology_tybij)] >>
  simp[istopology] >> rw[] >> simp[] >>
  ‘k ∈ POW {∅; X}’ by simp[IN_POW] >> pop_assum mp_tac >>
  simp[POW_EQNS] >> rw[] >> simp[]
QED

Theorem prop1_1_9:
  (∀x. x ∈ topspace t ⇒ open_in t {x}) ⇒
  t = discrete_topology (topspace t)
Proof
  simp[TOPOLOGY_EQ, openSets_discrete] >> strip_tac >> gen_tac >> eq_tac
  >- (simp[topspace, SUBSET_DEF] >> metis_tac[]) >>
  gvs[topspace, PULL_EXISTS] >> simp[SUBSET_DEF] >> strip_tac >>
  ‘s = BIGUNION {{x} | x ∈ s}’ by simp[Once EXTENSION, PULL_EXISTS] >>
  pop_assum SUBST1_TAC >> irule (cj 3 OPEN_IN_CLAUSES) >>
  simp[PULL_EXISTS]
QED


val _ = export_theory();
