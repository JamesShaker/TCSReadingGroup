open HolKernel Parse boolLib bossLib;

open chap4Theory pred_setTheory topologyTheory

val _ = new_theory "chap5";

Theorem lemma5_1_2:
  (∀x. x ∈ topspace τ ⇒ f x ∈ topspace τ') ⇒
  ((∀U. open_in τ' U ⇒ open_in τ (PREIMAGE f U ∩ topspace τ)) ⇔
   ∀a U. a ∈ topspace τ ∧ open_in τ' U ∧ f a ∈ U ⇒
         ∃V. open_in τ V ∧ a ∈ V ∧ IMAGE f V ⊆ U)
Proof
  rw[EQ_IMP_THM]
  >- (first_assum $ irule_at (Pat ‘open_in τ _’) >>
      first_assum $ irule_at (Pat ‘open_in τ' _’) >>
      simp[] >> simp[SUBSET_DEF, PULL_EXISTS]) >>
  simp[chap3Theory.corollary_3_2_9] >> rpt strip_tac >>
  first_x_assum $ drule_all_then strip_assume_tac >>
  first_assum $ irule_at Any >> simp[OPEN_IN_SUBSET] >>
  qpat_x_assum ‘IMAGE f V ⊆ U’ mp_tac >>
  simp[SUBSET_DEF, PULL_EXISTS]
QED

Definition continuousfn_def:
  continuousfn t1 t2 f ⇔
    (∀a. a ∈ topspace t1 ⇒ f a ∈ topspace t2) ∧
    ∀A. open_in t2 A ⇒ open_in t1 (PREIMAGE f A ∩ topspace t1)
End

Theorem example_5_1_4:
  continuousfn t t I
Proof
  simp[continuousfn_def, PREIMAGE_I, OPEN_IN_INTER]
QED

Theorem example_5_1_5:
  c ∈ topspace t2 ⇒
  continuousfn t1 t2 (K c)
Proof
  simp[continuousfn_def] >> rw[] >>
  Cases_on ‘c ∈ A’ >> simp[]
  >- (‘PREIMAGE (K c) A ∩ topspace t1 = topspace t1’
        suffices_by simp[] >>
      simp[EXTENSION]) >>
  ‘PREIMAGE (K c) A = ∅’ suffices_by simp[] >>
  simp[EXTENSION]
QED

Theorem prop_5_1_7:
  continuousfn t1 t2 f ⇔
    (∀x. x ∈ topspace t1 ⇒ f x ∈ topspace t2) ∧
    ∀a U. a ∈ topspace t1 ∧ open_in t2 U ∧ f a ∈ U ⇒
          ∃V. open_in t1 V ∧ a ∈ V ∧ IMAGE f V ⊆ U
Proof
  simp[continuousfn_def] >> eq_tac >> rw[]
  >- metis_tac[lemma5_1_2] >>
  irule (iffRL lemma5_1_2) >>
  qexists_tac‘t2’ >> metis_tac[]
QED

Theorem prop_5_1_8:
  continuousfn t1 t2 f ∧ continuousfn t2 t3 g ⇒
  continuousfn t1 t3 (g o f)
Proof
  simp[continuousfn_def] >> rw[] >>
  simp[GSYM PREIMAGE_COMP] >>
  first_x_assum $ dxrule_then assume_tac >>
  first_x_assum $ dxrule >>
  qmatch_abbrev_tac ‘open_in t1 AA ⇒ open_in t1 BB’ >>
  ‘AA = BB’ suffices_by simp[] >>
  simp[Abbr‘AA’, Abbr‘BB’, EXTENSION, SF CONJ_ss]
QED

Theorem PREIMAGE_DIFF[local]:
  A DIFF PREIMAGE f B ∩ A = PREIMAGE f (IMAGE f A DIFF B) ∩ A
Proof
  simp[EXTENSION] >> metis_tac[]
QED

Theorem prop_5_1_9:
  continuousfn t1 t2 f ⇔
    (∀a. a ∈ topspace t1 ⇒ f a ∈ topspace t2) ∧
    ∀A. closed_in t2 A ⇒ closed_in t1 (PREIMAGE f A ∩ topspace t1)
Proof
  rw[closed_in, continuousfn_def, EQ_IMP_THM, PREIMAGE_DIFF]
  >- (first_x_assum drule >>
      qmatch_abbrev_tac ‘open_in t1 AA ⇒ open_in t1 BB’ >>
      ‘AA = BB’ suffices_by simp[] >>
      simp[Abbr‘AA’, Abbr‘BB’, EXTENSION, SF CONJ_ss]) >>
  ‘A ⊆ topspace t2’ by simp[OPEN_IN_SUBSET] >>
  ‘A = topspace t2 DIFF (topspace t2 DIFF A)’
    by (simp[EXTENSION] >> metis_tac[SUBSET_DEF]) >>
  first_x_assum $ qspec_then ‘topspace t2 DIFF A’ mp_tac >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  qmatch_abbrev_tac ‘open_in t1 AA ⇒ open_in t1 BB’ >>
  ‘AA = BB’ suffices_by simp[] >>
  simp[Abbr‘AA’, Abbr‘BB’, EXTENSION, SF CONJ_ss]
QED

Theorem remark_5_1_10:
  homeomorphism (t1,t2) (f, g) ⇒
  continuousfn t1 t2 f
Proof
  simp[homeomorphism, continuousfn_def] >> rw[]
  >- metis_tac[BIJ_DEF, SURJ_DEF] >>
  first_x_assum drule >>
  qmatch_abbrev_tac ‘open_in t1 AA ⇒ open_in t1 BB’ >>
  ‘AA = BB’ suffices_by simp[] >>
  simp[Abbr‘AA’, Abbr‘BB’, EXTENSION, SF CONJ_ss] >>
  qx_gen_tac ‘a’ >> eq_tac >> rw[] >>
  metis_tac[BIJ_DEF, SURJ_DEF, OPEN_IN_SUBSET, SUBSET_DEF]
QED

Theorem prop_5_1_11:
  homeomorphism (t1,t2) (f,g) ⇔
    (∀x. x ∈ topspace t1 ⇒ g (f x) = x) ∧
    (∀y. y ∈ topspace t2 ⇒ f (g y) = y) ∧
    continuousfn t1 t2 f ∧
    continuousfn t2 t1 g
Proof
  rw[homeomorphism,EQ_IMP_THM,continuousfn_def]
  >- (metis_tac[BIJ_DEF,SURJ_DEF])
  >- (‘PREIMAGE f A ∩ topspace t1 = IMAGE g A’ suffices_by metis_tac[] >>
      rw[EXTENSION,EQ_IMP_THM] >> metis_tac[BIJ_DEF,SURJ_DEF,in_open_in_topspace])
  >- (metis_tac[BIJ_DEF,SURJ_DEF])
  >- (‘PREIMAGE g A ∩ topspace t2 = IMAGE f A’ suffices_by metis_tac[] >>
      rw[EXTENSION,EQ_IMP_THM] >> metis_tac[BIJ_DEF,SURJ_DEF,in_open_in_topspace])
  >- (simp[BIJ_IFF_INV] >> metis_tac[])
  >- (simp[BIJ_IFF_INV] >> metis_tac[])
  >- (‘PREIMAGE f V ∩ topspace t1 = IMAGE g V’ suffices_by metis_tac[] >>
      rw[EXTENSION,EQ_IMP_THM] >> metis_tac[BIJ_DEF,SURJ_DEF,in_open_in_topspace])
  >- (‘PREIMAGE g U ∩ topspace t2 = IMAGE f U’ suffices_by metis_tac[] >>
      rw[EXTENSION,EQ_IMP_THM] >> metis_tac[BIJ_DEF,SURJ_DEF,in_open_in_topspace])
QED

Theorem prop_5_1_12:
    continuousfn t1 t2 f ∧ (∀x. x ∈ A ∩ topspace t1 ⇒ g x = f x) ⇒
        continuousfn (subtopology t1 A) t2 g
Proof
    rw[continuousfn_def,TOPSPACE_SUBTOPOLOGY,OPEN_IN_SUBTOPOLOGY] >>
    rename [‘open_in t2 B’] >> first_x_assum $ drule_then strip_assume_tac >>
    first_assum $ irule_at Any >>
    simp[EXTENSION] >> simp[SF CONJ_ss,CONJ_ASSOC]
QED

Theorem exercise_5_1_1_i:
    c ∈ topspace t2 ⇒ continuousfn t1 t2 (K c)
Proof
    rw[continuousfn_def] >>
    Cases_on ‘c ∈ A’
    >- (‘PREIMAGE (K c) A ∩ topspace t1 = topspace t1’ suffices_by simp[OPEN_IN_TOPSPACE] >>
        simp[EXTENSION]) >>
    ‘PREIMAGE (K c) A = ∅’ suffices_by simp[OPEN_IN_EMPTY] >>
    simp[EXTENSION]
QED

(*
PREIMAGE_BIGUNION
*)
Theorem exercise_5_1_5:
    basis B t2 ⇒
        (continuousfn t1 t2 f ⇔
         (∀x. x ∈ topspace t1 ⇒ f x ∈ topspace t2) ∧
         (∀U. U ∈ B ⇒ open_in t1 (PREIMAGE f U ∩ topspace t1)))
Proof
    rw[continuousfn_def,EQ_IMP_THM]
    >- (metis_tac[chap2Theory.basis_def]) >>
    drule_all_then strip_assume_tac $ cj 2 $ iffLR chap2Theory.basis_def >>
    gvs[PREIMAGE_BIGUNION,INTER_BIGUNION] >>
    irule OPEN_IN_BIGUNION >>
    simp[PULL_EXISTS] >> metis_tac[SUBSET_DEF]
QED

val _ = export_theory();
