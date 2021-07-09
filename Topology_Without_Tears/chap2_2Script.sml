open HolKernel Parse boolLib bossLib;

open chap1Theory pred_setTheory topologyTheory;

val _ = new_theory "chap2_2";

(* definition 2.2.2 *)
Definition basis_def:
  basis B t ⇔
    (∀s. s ∈ B ⇒ open_in t s) ∧
    (∀s. open_in t s ⇒ ∃u. u ⊆ B ∧ s = BIGUNION u)
End

Theorem basis_def':
  ∀B t.
    basis B t ⇔
      (∀s. s ∈ B ⇒ open_in t s) ∧
      ∀s. open_in t s ⇔ ∃u. u ⊆ B ∧ s = BIGUNION u
Proof       
  rw[basis_def] >> eq_tac  (* 2 *)
  >- (simp[] >> rpt strip_tac >> eq_tac >> simp[] >> metis_tac[SUBSET_DEF,OPEN_IN_BIGUNION])
  >> metis_tac[]
QED
            
Theorem basis_topology_unique:
  ∀B t1 t2. basis B t1 ∧ basis B t2 ⇒ t1 = t2
Proof
  rw[basis_def',TOPOLOGY_EQ]
QED


Theorem example2_2_4:
  basis { {x} | x ∈ X } (discrete_topology X)
Proof
  simp[basis_def, PULL_EXISTS] >> rpt strip_tac >>
  (* could supposedly appeal to prop1_1_9 here *)
  qexists_tac ‘{{x} | x ∈ s}’ >> gs[SUBSET_DEF, PULL_EXISTS] >>
  simp[Once EXTENSION, PULL_EXISTS]
QED


Theorem remark2_2_6:
  basis B t ∧ B ⊆ B1 ∧ (∀s. s ∈ B1 ⇒ open_in t s) ⇒
  basis B1 t
Proof
  simp[basis_def] >> rpt strip_tac >>
  metis_tac[SUBSET_TRANS]
QED

Theorem prop_2_2_8:
  (∃t. topspace t = X ∧ basis B t) ⇔
    BIGUNION B = X ∧
    ∀b1 b2. b1 ∈ B ∧ b2 ∈ B ⇒
            ∃bs. bs ⊆ B ∧ b1 ∩ b2 = BIGUNION bs
Proof
  simp[basis_def] >> rw[EQ_IMP_THM] (* 4 *)
  >- (first_assum (qspec_then ‘topspace t’ mp_tac) >>
      impl_tac >- simp[] >>
      simp[PULL_EXISTS] >> rpt strip_tac >>
     reverse (rw[SET_EQ_SUBSET])(* 2 *)
      >- (simp[SUBSET_DEF] >> metis_tac[SUBSET_DEF])
      >- (pop_assum (SUBST_ALL_TAC o GSYM) >>
          simp[SUBSET_DEF,PULL_EXISTS] >> rw[] >>
          metis_tac[SUBSET_DEF,OPEN_IN_SUBSET]))
  >- metis_tac[OPEN_IN_INTER]
  >> qexists_tac `topology {s | ∃bs. bs ⊆ B ∧ s = BIGUNION bs}` >>
  `istopology {s | ∃bs. bs ⊆ B ∧ s = BIGUNION bs}`
    by (rw[istopology] (* 3 *)
        >- dsimp[]
        >- (rename[`BIGUNION bs1 ∩ BIGUNION bs2`] >>
            qabbrev_tac `a = {b1 ∩ b2 | b1 ∈ bs1 ∧ b2 ∈ bs2}` >>
            `BIGUNION bs1 ∩ BIGUNION bs2 = BIGUNION a`
              by (simp[Abbr `a`, Once EXTENSION] >> rw[EQ_IMP_THM]
                  >- (simp[PULL_EXISTS] >> metis_tac[])
                  >> metis_tac[IN_INTER]) >> simp[] >>
            `∀e. e ∈ a ⇒ ∃as. as ⊆ B ∧ e = BIGUNION as`
              by (simp[Abbr `a`, PULL_EXISTS] >> metis_tac[SUBSET_DEF]) >>
            gs[SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
            qexists_tac `BIGUNION (IMAGE f a)` >> rw[Abbr `a`]
            >- (simp[SUBSET_DEF, PULL_EXISTS] >> gs[PULL_EXISTS] >> metis_tac[SUBSET_DEF])
            >> simp[Once EXTENSION, PULL_EXISTS] >> gs[PULL_EXISTS] >>
            rw[EQ_IMP_THM]
            >- (first_x_assum drule_all >> rw[] >>
                pop_assum mp_tac >> simp[Once EXTENSION] >> metis_tac[])
            >> first_x_assum drule_all >> simp[EXTENSION] >> metis_tac[])
        >> pop_assum mp_tac >> simp[Once SUBSET_DEF] >> strip_tac >>
        gs[SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
        qexists_tac `BIGUNION (IMAGE f k)` >> conj_tac
        >- (simp[SUBSET_DEF, PULL_EXISTS] >> metis_tac[SUBSET_DEF])
        >> simp[Once EXTENSION, PULL_EXISTS, EQ_IMP_THM] >> rw[]
        >- (first_x_assum drule >> simp[EXTENSION] >> metis_tac[])
        >> first_x_assum drule >> simp[EXTENSION] >> metis_tac[]) >>
  simp[iffLR (cj 2 topology_tybij), topspace] >>
  rw[]
  >- (simp[Once EXTENSION, PULL_EXISTS] >> metis_tac[SUBSET_DEF])
  >> qexists_tac `{s}`  >> simp[]
QED


val _ = export_theory();
