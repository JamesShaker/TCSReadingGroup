open HolKernel Parse boolLib bossLib;

open chap1Theory pred_setTheory topologyTheory;

val _ = new_theory "chap2";

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
  >- (simp[] >> rpt strip_tac >> eq_tac >> simp[] >>
      metis_tac[SUBSET_DEF,OPEN_IN_BIGUNION])
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
            rename [‘f _ ⊆ B ∧ _ = BIGUNION (f _)’] >>
            qexists_tac `BIGUNION (IMAGE f a)` >> rw[Abbr `a`]
            >- (simp[SUBSET_DEF, PULL_EXISTS] >> gs[PULL_EXISTS] >>
                metis_tac[SUBSET_DEF])
            >> simp[Once EXTENSION, PULL_EXISTS] >> gs[PULL_EXISTS] >>
            rw[EQ_IMP_THM]
            >- (first_x_assum drule_all >> rw[] >>
                pop_assum mp_tac >> simp[Once EXTENSION] >> metis_tac[])
            >> first_x_assum drule_all >> simp[EXTENSION] >> metis_tac[])
        >> pop_assum mp_tac >> simp[Once SUBSET_DEF] >> strip_tac >>
        gs[SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
        rename [‘f _ ⊆ B ∧ _ = BIGUNION (f _)’] >>
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

Theorem prop_2_3_2:
  basis B t ⇔
    (∀b. b ∈ B ⇒ open_in t b) ∧
    ∀x U. open_in t U ∧ x ∈ U ⇒ ∃b. b ∈ B ∧ b ⊆ U ∧ x ∈ b
Proof
  eq_tac >> rpt strip_tac
  >- gs[basis_def]
  >- (gs[basis_def] >>
      first_x_assum $ drule_then strip_assume_tac >> gvs[] >>
      rename [‘open_in t (BIGUNION Us)’, ‘b ∈ Us’] >>
      first_assum $ irule_at Any >> simp[SUBSET_BIGUNION_I] >>
      gs[SUBSET_DEF]) >>
  rw[basis_def] >>
  first_x_assum $ drule_then assume_tac >>
  qexists_tac ‘{ b | b ⊆ s ∧ b ∈ B }’ >> conj_tac
  >- simp[SUBSET_DEF] >>
  simp[Once EXTENSION] >> qx_gen_tac ‘a’ >> eq_tac
  >- (strip_tac >> first_x_assum drule>> metis_tac[SUBSET_DEF]) >>
  metis_tac[SUBSET_DEF]
QED

Theorem prop_2_3_3:
  basis B t ⇒
  ∀U. open_in t U ⇔
        U ⊆ topspace t ∧ ∀x. x ∈ U ⇒ ∃b. x ∈ b ∧ b ∈ B ∧ b ⊆ U
Proof
  rw[EQ_IMP_THM]
  >- simp[OPEN_IN_SUBSET]
  >- metis_tac[prop_2_3_2] >>
  ‘U = BIGUNION { b | b ⊆ U ∧ b ∈ B }’ suffices_by
    (disch_then SUBST1_TAC >> irule OPEN_IN_BIGUNION >> simp[] >>
     gs[basis_def]) >>
  simp[Once EXTENSION] >> qx_gen_tac ‘a’ >> rw[EQ_IMP_THM] >>
  metis_tac[SUBSET_DEF]
QED

(* WARNING: understand difference between prop_2_2_8 and prop_2_3_2 *)
(* Theorem basis_empty:
  basis B (mktopology {∅}) ⇔ B = ∅ ∨ B = {∅}
Proof
  simp[prop_2_3_2]
*)

(* improve TWT, by removing need to be non-empty and over same space, as
   latter is implied by two conditions *)
Theorem prop_2_3_4:
  basis B1 t1 ∧ basis B2 t2 ⇒
  (t1 = t2 ⇔
     (∀b x. x ∈ b ∧ b ∈ B1 ⇒ ∃b'. x ∈ b' ∧ b' ⊆ b ∧ b' ∈ B2) ∧
     (∀b x. x ∈ b ∧ b ∈ B2 ⇒ ∃b'. x ∈ b' ∧ b' ⊆ b ∧ b' ∈ B1))
Proof
  strip_tac >> simp[TOPOLOGY_EQ] >> eq_tac >> rpt strip_tac
  >- metis_tac[basis_def, prop_2_3_2]
  >- metis_tac[basis_def, prop_2_3_2] >>
  eq_tac >> strip_tac
  >- (‘∃bs1. bs1 ⊆ B1 ∧ BIGUNION bs1 = s’ by metis_tac[basis_def] >>
      ‘s = BIGUNION { b2 | b2 ∈ B2 ∧ b2 ⊆ s}’
        by (simp[Once EXTENSION] >> qx_gen_tac ‘a’ >> eq_tac
            >- (gvs[] >> strip_tac >>
                rename [‘a ∈ s’, ‘s ∈ bs1’, ‘bs1 ⊆ B1’] >>
                ‘s ∈ B1’ by gs[SUBSET_DEF] >>
                ‘∃b'. a ∈ b' ∧ b' ∈ B2 ∧ b' ⊆ s’ by metis_tac[] >>
                qexists_tac ‘b'’ >> simp[] >>
                metis_tac[SUBSET_BIGUNION_SUBSET_I]) >>
            metis_tac[SUBSET_DEF]) >>
      pop_assum SUBST1_TAC >>
      irule OPEN_IN_BIGUNION >> simp[] >> metis_tac[basis_def]) >>
  ‘∃bs2. bs2 ⊆ B2 ∧ BIGUNION bs2 = s’ by metis_tac[basis_def] >>
  ‘s = BIGUNION { b1 | b1 ∈ B1 ∧ b1 ⊆ s}’
    by (simp[Once EXTENSION] >> qx_gen_tac ‘a’ >> eq_tac
        >- (gvs[] >> strip_tac >>
            rename [‘a ∈ s’, ‘s ∈ bs2’, ‘bs2 ⊆ B2’] >>
            ‘s ∈ B2’ by gs[SUBSET_DEF] >>
            ‘∃b'. a ∈ b' ∧ b' ∈ B1 ∧ b' ⊆ s’ by metis_tac[] >>
            qexists_tac ‘b'’ >> simp[] >>
            metis_tac[SUBSET_BIGUNION_SUBSET_I]) >>
        metis_tac[SUBSET_DEF]) >>
  pop_assum SUBST1_TAC >>
  irule OPEN_IN_BIGUNION >> simp[] >> metis_tac[basis_def]
QED

Theorem exercise2_3_2_i:
  basis B t ∧ B ⊆ B_1 ∧ B_1 ⊆ {s | open_in t s} ⇒ basis B_1 t
Proof
  rpt strip_tac >> fs[basis_def] >> strip_tac
  >- fs[SUBSET_DEF]
  >- metis_tac[SUBSET_TRANS]
QED

Definition subbasis_def:
  subbasis sb t ⇔
    (∀s. s ∈ sb ⇒ open_in t s) ∧ sb ≠ {} ∧
    basis {BIGINTER ss | ss ⊆ sb ∧ FINITE ss ∧ ss ≠ {}} t
End

Theorem COMPL_BIGINTER:
  COMPL (BIGINTER ss) = BIGUNION { COMPL s | s ∈ ss }
Proof
  simp[Once EXTENSION, PULL_EXISTS] >> metis_tac[]
QED

Theorem COMPL_DELETE:
  COMPL (s DELETE e) = COMPL s ∪ {e}
Proof
  simp[EXTENSION]
QED

Theorem exercise2_3_6:
  x ∈ X ∧ X ≠ {x} ⇒
  subbasis {X DELETE e | e | e ∈ X} (finite_closed_topology X)
Proof
  simp[subbasis_def, PULL_EXISTS] >> rw[]
  >- (‘X DIFF (X DELETE e) = {e}’ suffices_by simp[] >>
      simp[EXTENSION] >> metis_tac[])
  >- (simp[Once EXTENSION] >> metis_tac[])
  >- (simp[basis_def, PULL_EXISTS] >> rpt strip_tac
      >- (‘BIGINTER ss ⊆ X’ by (irule BIGINTER_SUBSET >>
                                gs[GSYM MEMBER_NOT_EMPTY] >>
                                gs[SUBSET_DEF] >> metis_tac[IN_DELETE]) >>
          simp[] >> Cases_on ‘BIGINTER ss = ∅’ >>
          simp[DIFF_INTER_COMPL, COMPL_BIGINTER, INTER_BIGUNION, PULL_EXISTS] >>
          conj_tac
          >- (qmatch_abbrev_tac ‘FINITE sss’ >>
              ‘sss = IMAGE (λs. X ∩ COMPL s) ss’ suffices_by simp[] >>
              simp[Once EXTENSION, Abbr‘sss’, PULL_EXISTS]) >>
          qx_gen_tac ‘s’ >> strip_tac >>
          ‘s ∈ {X DELETE e | e | e ∈ X}’ by gs[SUBSET_DEF] >>
          gs[COMPL_DELETE, UNION_OVER_INTER, FINITE_INTER])
      >- (qexists_tac ‘{}’ >> simp[]) >>
      Cases_on‘s = ∅’
      >- (qexists_tac ‘{}’ >> simp[]) >>
      Cases_on ‘s = X’
      >- (gvs[] >>
          ‘∃y. y ∈ X ∧ y ≠ x’
            by (CCONTR_TAC >> gvs[] >> qpat_x_assum ‘X ≠ {x}’ mp_tac >>
                simp[] >> simp[EXTENSION] >> metis_tac[]) >>
          qexists_tac ‘{X DELETE x; X DELETE y}’ >> simp[] >> rpt conj_tac
          >- (qexists_tac ‘{X DELETE x}’ >> simp[] >> metis_tac[])
          >- (qexists_tac ‘{X DELETE y}’ >> simp[] >> metis_tac[]) >>
          simp[EXTENSION] >> metis_tac[]) >>
      qexists_tac ‘{s}’ >> simp[] >>
      qexists_tac ‘{X DELETE e | e | e ∈ X ∧ e ∉ s}’ >> simp[PULL_EXISTS] >>
      rpt conj_tac
      >- (simp[Once EXTENSION, PULL_EXISTS] >> qx_gen_tac ‘a’ >>
          eq_tac >- metis_tac[SUBSET_DEF] >>
          simp[IMP_CONJ_THM, FORALL_AND_THM] >>
          rpt strip_tac>>
          CCONTR_TAC >> first_x_assum $ drule_at Concl >> simp[] >>
          ‘X DIFF s ≠ {}’ suffices_by simp[EXTENSION, SUBSET_DEF] >>
          simp[SUBSET_DIFF_EMPTY] >> metis_tac[SUBSET_ANTISYM])
      >- (simp[SUBSET_DEF, PULL_EXISTS] >> metis_tac[])
      >- (qmatch_abbrev_tac ‘FINITE sss’ >>
          ‘sss = IMAGE (λe. X DELETE e) (X DIFF s)’ suffices_by simp[] >>
          simp[Abbr‘sss’, Once EXTENSION]) >>
      simp[Once EXTENSION] >>
      ‘X DIFF s ≠ {}’ suffices_by simp[EXTENSION, SUBSET_DEF] >>
      simp[SUBSET_DIFF_EMPTY] >> metis_tac[SUBSET_ANTISYM])
QED

Definition second_countable_def:
  second_countable t ⇔ ∃B. basis B t ∧ countable B
End

Theorem SUBSET_TWO_ELEMENT_SET:
  x ⊆ {a;b} ⇔ x = ∅ ∨ x = {a} ∨ x = {b} ∨ x = {a;b}
Proof
  eq_tac >> simp[DISJ_IMP_THM] >>
  simp[SUBSET_DEF] >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem BIGUNION_EQ_SING:
  BIGUNION X = {x} ⇔ X = {{x}} ∨ X = {{x}; ∅}
Proof
  reverse eq_tac >- (strip_tac >> simp[]) >>
  CONV_TAC CONTRAPOS_CONV >> simp[] >> strip_tac >>
  Cases_on ‘X = ∅’ >> simp[] >>
  Cases_on ‘X = {∅}’ >> simp[] >>
  ‘∃s e. s ∈ X ∧ e ∈ s ∧ e ≠ x’
    suffices_by (strip_tac >> simp[EXTENSION] >> metis_tac[]) >>
  CCONTR_TAC >> gvs[] >>
  ‘X ⊆ {{x}; ∅}’
    by (simp[SUBSET_DEF] >> qx_gen_tac ‘s’ >> strip_tac >>
        ‘∀e. e ∉ s ∨ e = x’ by metis_tac[] >>
        Cases_on ‘s = ∅’ >> simp[] >>
        ‘∀d. d ∈ s ⇒ d = x’ by metis_tac[] >>
        simp[EXTENSION] >> metis_tac[MEMBER_NOT_EMPTY]) >>
  metis_tac[SUBSET_TWO_ELEMENT_SET]
QED

Theorem exercise_2_2_4_ii:
  ¬countable X ⇒ ¬second_countable (discrete_topology X)
Proof
  simp[second_countable_def] >> rpt strip_tac >>
  Cases_on ‘basis B (discrete_topology X)’ >> simp[] >>
  ‘∀x. x ∈ X ⇒ {x} ∈ B’
    by (rpt strip_tac >>
        ‘open_in (discrete_topology X) {x}’
          by simp[openSets_discrete] >>
        drule_then (drule_then strip_assume_tac o cj 2) $
          iffLR basis_def >>
        gs[BIGUNION_EQ_SING]) >>
  ‘INJ (λx. {x}) X B’ by simp[INJ_DEF] >>
  metis_tac[inj_countable]
QED

val _ = export_theory();
