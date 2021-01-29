open HolKernel Parse boolLib bossLib;

open pred_setTheory
(* inherit from existing topology theory *)
open topologyTheory
open arithmeticTheory

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

Theorem pow3[local] =
        (SIMP_CONV (srw_ss()) [POW_EQNS] THENC
         SIMP_CONV (srw_ss()) [LET_THM, GSYM INSERT_SING_UNION])
        “POW {a;b;c}”

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

Theorem openSets_discrete[simp]:
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

Theorem openSets_indiscrete[simp]:
  open_in (indiscrete_topology X) s ⇔ s = X ∨ s = ∅
Proof
  ‘open_in (indiscrete_topology X) = {∅; X}’ suffices_by (simp[] >> metis_tac[]) >>
  simp[indiscrete_topology_def] >> simp[GSYM (cj 2 topology_tybij)] >>
  simp[istopology] >> rw[] >> simp[] >>
  ‘k ∈ POW {∅; X}’ by simp[IN_POW] >> pop_assum mp_tac >>
  simp[POW_EQNS] >> rw[] >> simp[]
QED

Theorem topspace_indiscrete[simp]:
  topspace (indiscrete_topology X) = X
Proof
  simp[topspace] >> dsimp[Once EXTENSION]
QED

Theorem X_DIFF_EQ_X:
  X DIFF Y = X ⇔ DISJOINT X Y
Proof
  simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem DIFF_EQ_EMPTY[simp]:
  X DIFF Y = ∅ ⇔ X ⊆ Y
Proof
  simp[EXTENSION, SUBSET_DEF] >> metis_tac[]
QED

Theorem closed_in_indiscrete[simp]:
  closed_in (indiscrete_topology X) s ⇔ s = ∅ ∨ s = X
Proof
  simp[closed_in, EQ_IMP_THM, X_DIFF_EQ_X, DISJOINT_DEF] >> rpt strip_tac >> simp[]
  >- (gs[EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
  metis_tac[SUBSET_ANTISYM]
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

Theorem MAX_SET_all_x_lse_n_eq_n:
  MAX_SET {x | x ≤ n} = n
Proof
  DEEP_INTRO_TAC MAX_SET_ELIM >> rw[]
  >- (`{x | x ≤ n} = count (n+1)` suffices_by simp[] >> simp[EXTENSION])
  >- (fs[EXTENSION] >> fs[NOT_LESS_EQUAL] >> `n < 0` by fs[] >>
      `0 ≤ n` by fs[] >> fs[])
  >> metis_tac[LESS_EQ_REFL, LESS_EQUAL_ANTISYM]
QED

Theorem exercise_6:
  istopology ({univ (:num);∅} UNION (IMAGE (\n. {x | x ≤ n}) univ(:num)))
Proof
  rw[istopology] >> simp[] >> TRY (metis_tac[]) (* 2 *)
  >- (disj2_tac >> qexists_tac ‘MIN n n'’ >> rw[EQ_IMP_THM,EXTENSION]) >>
  Cases_on ‘UNIV IN k’ (* 2 *)
  >- (‘BIGUNION k = UNIV’
       by (rw[EXTENSION,EQ_IMP_THM] >> metis_tac[IN_UNIV]) >>
     simp[]) >>
  Cases_on ‘k = {∅}’ >> simp[] >> Cases_on ‘k = {}’ >> simp[] >>
  Cases_on ‘FINITE k’ (* 2 *)
  >- (fs[SUBSET_DEF] >> disj2_tac >>
      `FINITE {n | {x | x ≤ n} ∈ k}`
          by (‘INJ (\n. {x | x ≤ n}) {n | {x | x ≤ n} ∈ k} (k DELETE {})’
                by (simp[INJ_DEF] >> rw[]
                    >- (simp[EXTENSION] >> qexists_tac `0` >> simp[])
                    >> pop_assum mp_tac >> simp[EXTENSION] >>
                    metis_tac[LESS_EQ_REFL, LESS_EQUAL_ANTISYM]) >>
              drule FINITE_INJ >> rw[]) >>
      qexists_tac ‘MAX_SET {n | {x | x ≤ n} ∈ k}’ >> rw[EQ_IMP_THM,EXTENSION]
      >- (rename [‘n IN i’,‘i IN k’] >>
          ‘∃m. i = {x | x ≤ m}’ by metis_tac[NOT_IN_EMPTY] >>
          gvs[] >> DEEP_INTRO_TAC MAX_SET_ELIM >> simp[] >> rw[] (* 2 *)
          >- fs[EXTENSION]
          >> metis_tac[LESS_EQ_TRANS])
      >> pop_assum mp_tac >> DEEP_INTRO_TAC MAX_SET_ELIM >> rw[]
      >- (pop_assum mp_tac >> simp[EXTENSION] >> rw[] >>
          `∃y. {y' | y' ≤ y} ∈ k` suffices_by metis_tac[] >>
          `∃z. z ∈ k ∧ z ≠ ∅` suffices_by metis_tac[] >>
          CCONTR_TAC >> gs[] >> `∀z. z ∈ k ⇒ z = ∅` by metis_tac[] >>
          qpat_x_assum `k ≠ {∅}` mp_tac >> simp[Once EXTENSION] >> rw[EQ_IMP_THM] >>
          metis_tac[MEMBER_NOT_EMPTY])
      >> first_x_assum $ irule_at Any >> simp[])
  >> fs[SUBSET_DEF] >> disj1_tac >> simp[EXTENSION] >> rw[] >>
  `∃y. {y' | y' ≤ y} ∈ k ∧ x ≤ y`
      suffices_by (strip_tac >> first_x_assum $ irule_at Any >> simp[]) >>
  CCONTR_TAC >> gs[] >>
  `∀y. {y' | y' ≤ y} ∈ k ⇒ ¬(x ≤ y)` by metis_tac[] >>
  fs[NOT_LESS_EQUAL] >>
  qpat_x_assum `INFINITE k` mp_tac >> simp[] >>
  `FINITE (k DELETE {})` suffices_by simp[] >>
  `INJ (\s. MAX_SET s) (k DELETE {}) (count x)`
                by (simp[INJ_DEF] >> rw[]
                    >- (first_x_assum drule >> rw[] >> fs[] >>
                        first_x_assum drule >> rw[] >> DEEP_INTRO_TAC MAX_SET_ELIM >>
                        simp[] >> `{x | x ≤ n} = count (n+1)` suffices_by simp[] >>
                        simp[EXTENSION])
                    >> `∃m n. s = {x | x ≤ m} ∧ s' = {x | x ≤ n}` by metis_tac[] >>
                    metis_tac[MAX_SET_all_x_lse_n_eq_n]) >>
  drule FINITE_INJ >> rw[]
QED

Theorem prop122i = CONJ OPEN_IN_TOPSPACE OPEN_IN_EMPTY
Theorem prop122ii = OPEN_IN_BIGUNION
Theorem prop122iii = OPEN_IN_BIGINTER

Theorem biginter_couterexample[local]:
  let S_n n = 1 INSERT { m | n + 1 ≤ m } (* S_n from Example 1_2_3 *)
  in
    (∀n. FINITE (COMPL (S_n n))) ∧
    BIGINTER (IMAGE S_n UNIV) = {1}
Proof
  simp[] >> conj_tac
  >- (gen_tac >> irule SUBSET_FINITE >> qexists_tac ‘count (n + 1)’ >>
      simp[SUBSET_DEF]) >>
  simp[Once EXTENSION, PULL_EXISTS] >> gen_tac >> eq_tac >> simp[] >>
  disch_then $ qspec_then ‘x’ mp_tac >> simp[]
QED

(* what the book calls a closed set is written closed_in, here we alias with closedSet *)
Overload closedSets = “closed_in”

Theorem prop1_2_5:
  closed_in top ∅ ∧ closed_in top (topspace top) ∧ (* i *)
  ((∀t. t ∈ s ⇒ closed_in top t) ∧ s ≠ ∅ ⇒ closed_in top (BIGINTER s)) ∧
  ((∀t. t ∈ s ⇒ closed_in top t) ∧ FINITE s ⇒ closed_in top (BIGUNION s))
Proof
  simp[CLOSED_IN_BIGINTER, CLOSED_IN_BIGUNION, CLOSED_IN_EMPTY, CLOSED_IN_TOPSPACE]
QED

Definition clopen_def:
  clopen top s ⇔ closed_in top s ∧ open_in top s
End

Theorem exercise1_2_2:
  (∀s. s ⊆ topspace top ⇒ closed_in top s) ⇒
  top = discrete_topology (topspace top)
Proof
  strip_tac >> irule prop1_1_9 >>
  gs[closed_in] >> qx_gen_tac ‘e’ >> strip_tac >>
  first_x_assum $ qspec_then ‘topspace top DIFF {e}’ mp_tac >> simp[] >>
  simp[DIFF_DIFF_SUBSET, SUBSET_DEF]
QED

Theorem exercise1_2_3:
  ALL_DISTINCT [a;b;c;d] ⇒
  let t = {∅; {a;c}; {b;d}; {a;b;c;d}}
  in
  istopology t ∧ (∀s. open_in (topology t) s ⇒ closed_in (topology t) s)
Proof
  simp[] >> strip_tac >> conj_asm1_tac
  >- (simp[istopology] >> rw[] >> simp[] >>
      simp[SING_INTER, INTER_EQ] >>
      simp[Once EXTENSION]
      >- metis_tac[] >- metis_tac[] >>
      gs[SUBSET_DEF] >> Cases_on ‘k = ∅’ >> simp[] >>
      ONCE_REWRITE_TAC [EXTENSION] >>
      Cases_on ‘k = {∅}’ (* 2 *)
      >- simp[] >>
      disj2_tac >> Cases_on ‘{a;b;c;d} IN k’ (* 2 *)
      >- (disj2_tac >> disj2_tac >>
          simp[EQ_IMP_THM,PULL_EXISTS,FORALL_AND_THM,DISJ_IMP_THM] >>
          ntac 4 (qexists_tac ‘{a;b;c;d}’) >> simp[] >>
          rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) (* 4 *) >>
          fs[]) >>
      Cases_on ‘{a;c} IN k’ >> Cases_on ‘{b;d} IN k’ (* 4 *)
      >- (disj2_tac >> disj2_tac >>
         simp[EQ_IMP_THM,PULL_EXISTS,FORALL_AND_THM,DISJ_IMP_THM] >>
         qexistsl_tac [‘{a;c}’,‘{b;d}’,‘{a;c}’,‘{b;d}’] >> simp[] >>
         rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) (* 4 *) >>
         fs[])
      >- (disj1_tac >>
         simp[EQ_IMP_THM,PULL_EXISTS,FORALL_AND_THM,DISJ_IMP_THM] >>
         ntac 2 (qexists_tac ‘{a;c}’) >> simp[] >>
         rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) (* 4 *) >>
         fs[])
      >- (disj2_tac >> disj1_tac >>
         simp[EQ_IMP_THM,PULL_EXISTS,FORALL_AND_THM,DISJ_IMP_THM] >>
         ntac 2 (qexists_tac ‘{b;d}’) >> simp[] >>
         rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) (* 4 *) >>
         fs[]) >>
      ‘∀x. x ∈ k ⇒ x = ∅’ by metis_tac[] >>
      ‘k = {∅}’ suffices_by metis_tac[] >>
      rw[EXTENSION] >> fs[GSYM MEMBER_NOT_EMPTY] >>
      metis_tac[UNIQUE_MEMBER_SING])
  >> `topspace (topology {∅; {a; c}; {b; d}; {a; b; c; d}}) = {a; b; c; d}`
        by (simp[topspace, topology_tybij |> cj 2 |> iffLR] >> simp[Once EXTENSION] >> dsimp[] >>
            metis_tac[]) >>
  simp[topology_tybij |> cj 2 |> iffLR, closed_in] >>
  rw[] >> simp[] >> fs[] >> rw[]
QED

Definition finite_closed_topology_def:
  finite_closed_topology X = topology (∅ INSERT { s | FINITE (X DIFF s) ∧ s ⊆ X})
End

Theorem finite_closed_topology_istopology:
  istopology (∅ INSERT { s | FINITE (X DIFF s) ∧ s ⊆ X})
Proof
  rw[istopology] >> simp[]
  >- (disj2_tac >> conj_tac
      >- (`X DIFF s ∩ t = (X DIFF s) ∪ (X DIFF t)` by (simp[EXTENSION] >> metis_tac[]) >>
          simp[]) >> gs[SUBSET_DEF]) >>
  Cases_on `k = ∅` >> fs[] >> Cases_on `k = {∅}` >> fs[] >>
  `X DIFF (BIGUNION k) = BIGINTER { X DIFF t | t ∈ k }`
    by (simp[Once EXTENSION, PULL_EXISTS] >> metis_tac[MEMBER_NOT_EMPTY]) >> conj_tac
  >- (simp[] >> irule FINITE_BIGINTER >> simp[PULL_EXISTS] >>
      ‘∃t. t ∈ k ∧ t ≠ ∅’
        by (qpat_x_assum ‘k ≠ ∅’ mp_tac >> qpat_x_assum ‘k ≠ {∅}’ mp_tac >>
            ONCE_REWRITE_TAC[EXTENSION] >> simp[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
      qexists_tac `t` >> rw[] >> gvs[SUBSET_DEF] >> metis_tac[]) >>
  simp[BIGUNION_SUBSET] >> rw[] >> qpat_x_assum `k ⊆ _` mp_tac >> simp[SimpL ``$==>``, Once SUBSET_DEF] >>
  rw[] >> first_x_assum drule >> rw[] >> simp[]
QED

Theorem finite_closed_open_sets[simp]:
  open_in (finite_closed_topology X) s ⇔ s = ∅ ∨ FINITE (X DIFF s) ∧ s ⊆ X
Proof
  simp[topology_tybij |> cj 2 |> iffLR, finite_closed_topology_def,
       finite_closed_topology_istopology]
QED

Theorem finite_closed_topspace[simp]:
  topspace (finite_closed_topology X) = X
Proof
  simp[topspace, Once EXTENSION, EQ_IMP_THM] >> rw[] (* 3 *)
  >- gvs[]
  >- gvs[SUBSET_DEF]
  >- (first_assum (irule_at (Pos hd)) >> simp[])
QED

Theorem finite_closed_closed_sets[simp]:
  closed_in (finite_closed_topology X) s ⇔ s = X ∨ s ⊆ X ∧ FINITE s
Proof
  simp[closed_in] >> csimp[DIFF_DIFF_SUBSET, SUBSET_DIFF_EMPTY] >>
  metis_tac[SUBSET_ANTISYM, SUBSET_REFL]
QED

val _ = export_rewrites ["topology.CLOSED_IN_EMPTY",
                         "topology.OPEN_IN_EMPTY",
                         "topology.OPEN_IN_TOPSPACE",
                         "topology.CLOSED_IN_TOPSPACE"]

Theorem clopen_EMPTY[simp]:
  clopen top {}
Proof
  simp[clopen_def]
QED

Theorem clopen_topspace[simp]:
  clopen top (topspace top)
Proof
  simp[clopen_def]
QED

Theorem example1_3_3:
  (∃a b c. clopen (finite_closed_topology X) a ∧
           clopen (finite_closed_topology X) b ∧
           clopen (finite_closed_topology X) c ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c) ⇒
  FINITE X
Proof
  strip_tac >>
  ‘∃d. clopen (finite_closed_topology X) d ∧ d ≠ ∅ ∧ d ≠ X’
    by metis_tac[clopen_EMPTY, clopen_topspace, finite_closed_topspace] >>
  qpat_x_assum ‘clopen _ _’ mp_tac >>
  csimp[clopen_def] >> strip_tac >>
  ‘X = d ∪ (X DIFF d)’ by simp[UNION_DIFF] >>
  metis_tac[FINITE_UNION]
QED

(* topologies are preserved over preimages *)
Theorem example1_3_9:
  istopology {PREIMAGE f s | open_in (yt : 'b topology) s}
Proof
  simp[istopology] >> rw[] (* 3 *)
  >- (irule_at (Pos hd) PREIMAGE_EMPTY >> simp[])
  >- (rename [‘PREIMAGE f s1 ∩ PREIMAGE f s2’] >>
      irule_at (Pos hd) (GSYM PREIMAGE_INTER) >>
      simp[OPEN_IN_INTER])
  >- (gvs[SUBSET_DEF, GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >>
      rename [‘_ = PREIMAGE f (g _) ∧ open_in yt (g _)’] >>
      qexists_tac ‘BIGUNION (IMAGE g k)’ >> conj_tac
      >- (simp[Once EXTENSION, PULL_EXISTS] >> qx_gen_tac ‘e’ >>
          eq_tac >> strip_tac (* 2 *)
          >- (first_assum (irule_at Any) >> first_x_assum drule >>
              simp[Once EXTENSION] >> metis_tac[]) >>
          first_x_assum drule >> simp[Once EXTENSION] >> metis_tac[]) >>
      irule OPEN_IN_BIGUNION >> simp[PULL_EXISTS])
QED

Definition sierpinski_space_def:
  sierpinski_space x y = topology {∅; {x}; {x; y}}
End

Theorem sierpinski_space_is_topology:
  istopology ({∅; {x}; {x; y}})
Proof
  rw[istopology] >> simp[]
  >- (simp[EXTENSION] >> metis_tac[])
  >- (simp[EXTENSION] >> metis_tac[]) >>
  ‘k ∈ POW {∅; {x}; {x; y}}’ by simp[IN_POW] >>
  pop_assum mp_tac >> pop_assum (K ALL_TAC) >>
  simp[pow3] >> rw[] >> ONCE_REWRITE_TAC[EXTENSION] >> dsimp[] >> metis_tac[]
QED

Theorem open_in_sierpinski_space[simp]:
 open_in (sierpinski_space x y) s ⇔ s = {} ∨ s = {x} ∨ s = {x; y}
Proof
simp[sierpinski_space_def,cj 2 topology_tybij |> iffLR,sierpinski_space_is_topology]
QED

Theorem topspace_sierpinski_space[simp]:
 topspace (sierpinski_space x y) = {x;y}
Proof
simp[topspace,Once EXTENSION] >> dsimp[] >> metis_tac[]
QED

Definition T1_space_def:
T1_space X ⇔ ∀x. x IN topspace X ⇒ closed_in X {x}
End

Theorem topspace_discrete_topology[simp]:
∀X. topspace (discrete_topology X) = X
Proof
simp[topspace,discrete_topology_def,EXTENSION,PULL_EXISTS] >>
metis_tac[SUBSET_DEF]
QED


Theorem closed_in_discrete_topology[simp]:
∀X s. closed_in (discrete_topology X) s ⇔ s ⊆ X
Proof
simp[closed_in]
QED


Theorem discrete_topology_T1:
∀X. T1_space (discrete_topology X)
Proof
simp[T1_space_def]
QED

Theorem finite_closed_topology_T1:
∀X. T1_space (finite_closed_topology X)
Proof
simp[T1_space_def]
QED


Definition T0_space_def:
T0_space X ⇔ ∀a b. a IN topspace X ∧ b IN topspace X ∧ a ≠ b ⇒
                   ∃s. open_in X s ∧ (a IN s ∧ b NOTIN s ∨ b IN s ∧ a NOTIN s)
End

Theorem T1_is_T0:
∀X. T1_space X ⇒ T0_space X
Proof
simp[T1_space_def,T0_space_def,closed_in] >> rw[] >>
qexists_tac ‘(topspace X) DIFF {a}’ >> simp[]
QED



Theorem sierpinski_space_T0:
T0_space (sierpinski_space x y)
Proof
simp[T0_space_def] >> rw[] (* 2 *)
>- (qexists_tac ‘{a}’ >> simp[]) >- (qexists_tac ‘{b}’ >> simp[])
QED

Definition countable_closed_topology_def:
  countable_closed_topology X = topology (∅ INSERT { s | countable (X DIFF s) ∧ s ⊆ X})
End

Theorem better_BIGINTER_SUBSET:
  (∃t. t ∈ P ∧ t ⊆ s) ⇒ BIGINTER P ⊆ s
Proof
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem countable_BIGINTER:
  (∃s. s ∈ P ∧ countable s) ⇒ countable (BIGINTER P)
Proof
  strip_tac >> irule COUNTABLE_SUBSET >> qexists_tac `s` >> rw[] >>
  irule better_BIGINTER_SUBSET >> metis_tac[SUBSET_REFL]
QED

Theorem countable_closed_topology_istopology:
  istopology (∅ INSERT { s | countable (X DIFF s) ∧ s ⊆ X})
Proof
  rw[istopology] >> simp[]
  >- (disj2_tac >> conj_tac
      >- (`X DIFF s ∩ t = (X DIFF s) ∪ (X DIFF t)` by (simp[EXTENSION] >> metis_tac[]) >>
          simp[])
      >> gs[SUBSET_DEF]) >>
  Cases_on `k = ∅` >> fs[] >> Cases_on `k = {∅}` >> fs[] >>
  `X DIFF (BIGUNION k) = BIGINTER { X DIFF t | t ∈ k }`
    by (simp[Once EXTENSION, PULL_EXISTS] >> metis_tac[MEMBER_NOT_EMPTY]) >> conj_tac
  >- (simp[] >> irule countable_BIGINTER >> simp[PULL_EXISTS] >>
      ‘∃t. t ∈ k ∧ t ≠ ∅’
        by (qpat_x_assum ‘k ≠ ∅’ mp_tac >> qpat_x_assum ‘k ≠ {∅}’ mp_tac >>
            ONCE_REWRITE_TAC[EXTENSION] >> simp[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
      qexists_tac `t` >> rw[] >> gvs[SUBSET_DEF] >> metis_tac[]) >>
  simp[BIGUNION_SUBSET] >> rw[] >> qpat_x_assum `k ⊆ _` mp_tac >> simp[SimpL ``$==>``, Once SUBSET_DEF] >>
  rw[] >> first_x_assum drule >> rw[] >> simp[]
QED

Theorem countable_closed_open_sets[simp]:
  open_in (countable_closed_topology X) s ⇔ s = ∅ ∨ countable (X DIFF s) ∧ s ⊆ X
Proof
  simp[topology_tybij |> cj 2 |> iffLR, countable_closed_topology_def,
       countable_closed_topology_istopology]
QED

Theorem topspace_countable_closed[simp]:
  topspace (countable_closed_topology X) = X
Proof
  simp[topspace, Once EXTENSION, EQ_IMP_THM] >> rw[] (* 3 *)
  >- gvs[]
  >- gvs[SUBSET_DEF]
  >- (first_assum (irule_at (Pos hd)) >> simp[])
QED

Definition top_INTER_def:
  top_INTER t1 t2 = topology {s | open_in t1 s ∧ open_in t2 s}
End

Theorem top_INTER_istopology:
  istopology {s | open_in t1 s ∧ open_in t2 s}
Proof
  rw[istopology] >> simp[OPEN_IN_INTER] >>
  irule OPEN_IN_BIGUNION >> rw[] >> fs[SUBSET_DEF]
QED

Theorem top_INTER_open_sets[simp]:
  open_in (top_INTER t1 t2) s ⇔ open_in t1 s ∧ open_in t2 s
Proof
  simp[topology_tybij |> cj 2 |> iffLR, top_INTER_def,
       top_INTER_istopology]
QED

(*
Thm topspace_top_INTER_old:
topspace (top_INTER t1 t2) = topspace t1 ∩ topspace t2

topspace_top_INTER_old is false.
Counter example:
t1 = empty, {a;b}
t2 = empty, {b;c}
*)

Theorem topspace_top_INTER[simp]:
  topspace t1 = topspace t2 ⇒ topspace (top_INTER t1 t2) = topspace t2
Proof
  simp[topspace] >> ONCE_REWRITE_TAC [EXTENSION] >> rw[] >> eq_tac
  >- metis_tac[]
  >> rw[] >> qexists_tac `topspace t1` >> rw[]
  >- (rw[topspace] >> metis_tac[])
  >> `topspace t1 = topspace t2` suffices_by simp[] >> rw[topspace, Once EXTENSION]
QED

Theorem exercise1_3_7_iii:
  topspace t1 = topspace t2 ∧ T1_space t1 ∧ T1_space t2 ⇒ T1_space (top_INTER t1 t2)
Proof
  simp[T1_space_def] >> rw[] >> fs[closed_in] >> metis_tac[]
QED

Definition top_BIGINTER_def:
  top_BIGINTER X = topology (BIGINTER (IMAGE open_in X))
End

Theorem IN_open_in[simp]:
  s ∈ open_in t ⇔ open_in t s
Proof
  simp[IN_DEF]
QED

Theorem exercise1_3_7_vi[simp]:
  open_in (top_BIGINTER X) s <=> ∀t. t ∈ X ⇒ open_in t s
Proof
  simp[top_BIGINTER_def] >>
  ‘istopology (BIGINTER (IMAGE open_in X))’
    by (simp[istopology, PULL_EXISTS, OPEN_IN_INTER] >> rpt strip_tac >>
        irule OPEN_IN_BIGUNION >> gs[SUBSET_DEF, PULL_EXISTS]) >>
  drule (topology_tybij |> cj 2 |> iffLR) >> simp[PULL_EXISTS]
QED

Theorem topspace_top_BIGINTER:
  Ts ≠ ∅ ∧ (∀t. t ∈ Ts ⇒ topspace t = X) ⇒ topspace (top_BIGINTER Ts) = X
Proof
  strip_tac >>
  simp[topspace] >> ONCE_REWRITE_TAC[EXTENSION] >> simp[] >>
  rpt strip_tac >> eq_tac >> rpt strip_tac
  >- (fs[topspace,Once EXTENSION] >> metis_tac[]) >>
  rename [‘_ IN Ts ⇒ _’, ‘Ts ≠ ∅’, ‘y IN _ ∧ _’] >>
  qexists_tac ‘X’ >> simp[] >> rpt strip_tac >> first_x_assum drule >>
  strip_tac >> gvs[OPEN_IN_TOPSPACE]
QED

Definition door_space_def:
  door_space t ⇔ ∀s. s ⊆ topspace t ⇒ open_in t s ∨ closed_in t s
End

Theorem exercise1_3_9_i:
  door_space (discrete_topology X)
Proof
  simp[door_space_def]
QED

Theorem exercise1_3_9_ii:
  a ≠ b ⇒ ¬door_space (indiscrete_topology {a;b})
Proof
  simp[door_space_def] >> csimp[] >> strip_tac >> qexists_tac ‘{a}’ >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem finite_open:
  INFINITE X ⇒ ~istopology { s | FINITE s ∧ s ⊆ X }
Proof
  simp[infinite_num_inj, INJ_IFF] >>
  rw[istopology] >> disj2_tac >>
  qexists_tac ‘IMAGE (λn. {f n}) UNIV’ >> simp[] >>
  simp[SUBSET_DEF, PULL_EXISTS]
QED

Theorem exercise1_3_9_iii:
  INFINITE X ⇒ ¬door_space (finite_closed_topology X)
Proof
  simp[door_space_def] >> simp[SimpL “$==>”, infinite_num_inj, INJ_IFF] >>
  strip_tac >> qexists_tac ‘{ f n | EVEN n}’  >>
  simp[SUBSET_DEF, PULL_EXISTS] >> rpt strip_tac
  >- (gs[EXTENSION] >> metis_tac[EVEN])
  >- (drule_then (qspec_then ‘{f n | ODD n}’ mp_tac) SUBSET_FINITE >>
      simp[SUBSET_DEF, PULL_EXISTS, ODD_EVEN] >>
      simp[infinite_num_inj] >> qexists_tac ‘λn. f (2 * n + 1)’ >>
      simp[INJ_IFF, EVEN_ADD, EVEN_MULT])
  >- (pop_assum mp_tac >> simp[EXTENSION] >> qexists_tac ‘f (SUC 0)’ >> simp[]) >>
  pop_assum mp_tac >> simp[infinite_num_inj] >> qexists_tac ‘f o $* 2’ >>
  simp[INJ_IFF, EVEN_MULT]
QED

Definition saturated_def:
  saturated t s ⇔ s ⊆ topspace t ∧
                  ∃os. os ≠ ∅ ∧ s = BIGINTER os ∧ (∀x. x ∈ os ⇒ open_in t x)
End

Theorem exercise1_3_10_i:
  open_in t s ⇒ saturated t s
Proof
  simp[saturated_def, OPEN_IN_SUBSET] >> strip_tac >>
  qexists_tac ‘{s}’ >> simp[]
QED

Theorem exercise1_3_10_ii:
  T1_space t ⇒ ∀s. s ⊆ topspace t ⇒ saturated t s
Proof
  simp[T1_space_def, saturated_def] >> rpt strip_tac >>
  Cases_on ‘open_in t s’
  >- (qexists_tac ‘{s}’ >> simp[]) >>
  qabbrev_tac ‘sbar = topspace t DIFF s’ >>
  ‘sbar ⊆ topspace t’ by simp[Abbr‘sbar’] >>
  qabbrev_tac ‘OS = { topspace t DIFF {e} | e ∈ sbar }’ >>
  ‘OS ≠ ∅’
    by (simp[Once EXTENSION, Abbr‘OS’, Abbr‘sbar’] >>
        ‘topspace t DIFF s ≠ ∅’ by
          (simp[] >> strip_tac >> metis_tac[SUBSET_ANTISYM, OPEN_IN_TOPSPACE]) >>
        drule_then (qx_choose_then ‘ee’ mp_tac) (iffRL MEMBER_NOT_EMPTY) >>
        simp[] >> metis_tac[]) >>
  ‘s = BIGINTER OS’
    by (simp[Once EXTENSION, Abbr‘sbar’, PULL_EXISTS, Abbr‘OS’] >>
        qx_gen_tac ‘a’ >>
        eq_tac >> rpt strip_tac
        >- gs[SUBSET_DEF]
        >- metis_tac[]
        >- (‘a ∈ topspace t’ suffices_by metis_tac[] >>
            ‘topspace t DIFF s ≠ ∅’ by
              (simp[] >> strip_tac >> metis_tac[SUBSET_ANTISYM, OPEN_IN_TOPSPACE]) >>
            drule_then (qx_choose_then ‘ee’ mp_tac) (iffRL MEMBER_NOT_EMPTY) >>
            simp[] >> metis_tac[])) >>
  qexists_tac ‘OS’ >> simp[] >> simp[Abbr‘OS’, PULL_EXISTS, Abbr‘sbar’] >>
  metis_tac[closed_in]
QED

Theorem exercise1_3_10_iii:
  a ≠ b ⇒ ¬saturated (indiscrete_topology {a;b}) {a}
Proof
  simp[saturated_def] >> rpt strip_tac >> Cases_on ‘os = ∅’ >> gs[]>>
  CCONTR_TAC >> gs[] >> qpat_x_assum ‘{a} = _’ mp_tac >>
  simp[EXTENSION] >>
  ‘∀s. s ∈ os ⇒ s = {a;b} ∨ s = ∅’ by metis_tac[] >>
  Cases_on ‘os = {{a;b}}’
  >- (qexists_tac ‘b’ >> simp[]) >>
  ‘∅ ∈ os’ by (pop_assum mp_tac >> simp[Once EXTENSION, PULL_EXISTS] >>
               qx_gen_tac‘s’ >> strip_tac >>
               ‘s ∈ os ⇔ s ≠ {a;b}’ by metis_tac[] >>
               Cases_on ‘s = {a;b}’ >> gs[]
               >- metis_tac[MEMBER_NOT_EMPTY] >> metis_tac[]) >>
  qexists_tac ‘a’ >> simp[] >> first_assum (irule_at Any) >> simp[]
QED

val _ = export_theory();
