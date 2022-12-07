open HolKernel Parse boolLib bossLib;

open chap3Theory chap4Theory pred_setTheory topologyTheory

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
  simp[corollary_3_2_9] >> rpt strip_tac >>
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

Theorem exercise_5_1_6:
  (∀a. a ∈ A ⇒ f a ∈ topspace t2) ⇒
  continuousfn (discrete_topology A) t2 f
Proof
  rw[continuousfn_def]
QED

Theorem exercise_5_1_7:
  (∀a. a ∈ topspace t1 ⇒ f a ∈ B) ⇒
  continuousfn t1 (indiscrete_topology B) f
Proof
  simp[continuousfn_def, PREIMAGE_EMPTY, DISJ_IMP_THM] >> rw[] >>
  ‘PREIMAGE f B ∩ topspace t1 = topspace t1’ suffices_by simp[] >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem exercise_5_1_8:
  continuousfn t1 t2 f ∧ A ⊆ topspace t1 ∧
  (∀a. a ∈ A ⇒ g a = f a)
⇒
  continuousfn (subtopology t1 A) (subtopology t2 (IMAGE f A)) g
Proof
  simp[continuousfn_def, TOPSPACE_SUBTOPOLOGY, OPEN_IN_SUBTOPOLOGY] >>
  rw[] >> first_x_assum $ drule_then assume_tac >>
  first_assum $ irule_at Any >>
  ‘PREIMAGE g (t ∩ IMAGE f A) ∩ A = PREIMAGE f t ∩ A’
    by (simp[EXTENSION] >> metis_tac[]) >>
  metis_tac[INTER_COMM, INTER_ASSOC]
QED

Theorem exercise_5_1_9:
  (∀a. a ∈ topspace t1 ⇒ f a ∈ topspace t2) ⇒
  (continuousfn t1 t2 f ⇔
     ∀a N. a ∈ topspace t1 ∧ neigh t2 (N, f a) ⇒
           ∃M. neigh t1 (M,a) ∧ IMAGE f M ⊆ N)
Proof
  rw[continuousfn_def] >> eq_tac >> rpt strip_tac
  >- (gs[neigh, PULL_EXISTS] >>
      first_x_assum $ drule_then assume_tac >>
      irule_at Any SUBSET_REFL >>
      first_assum $ irule_at Any >> simp[] >> conj_tac
      >- simp[IN_DEF] >>
      simp[SUBSET_DEF, PULL_EXISTS] >> metis_tac[SUBSET_DEF]) >>
  gs[neigh, PULL_EXISTS] >>
  rename [‘open_in t2 B’, ‘open_in t1 (PREIMAGE f B ∩ topspace t1)’] >>
  first_x_assum $ resolve_then Any assume_tac SUBSET_REFL >>
  first_x_assum $ drule_at_then (Pat ‘open_in _ _’) assume_tac >>
  first_x_assum $ resolve_then Any assume_tac OPEN_IN_SUBSET >> gs[] >>
  qabbrev_tac ‘pfb = PREIMAGE f B ∩ topspace t1’ >>
  ‘∀a. B (f a) ⇔ f a ∈ B’ by simp[IN_DEF] >> pop_assum (gs o single) >>
  ‘∀a. a ∈ topspace t1 ∧ f a ∈ B ⇔ a ∈ pfb’
    by (simp[Abbr‘pfb’] >> metis_tac[]) >>
  pop_assum (gs o single) >>
  gs[GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >>
  rename [‘open_in t1 (opfn _)’, ‘opfn _ ⊆ nfn _’] >>
  ‘∀x. opfn x x ⇔ x ∈ opfn x’ by simp[IN_DEF] >>
  pop_assum (gs o single) >>
  ‘pfb = BIGUNION (IMAGE opfn pfb)’
    suffices_by (disch_then SUBST1_TAC >>
                 irule OPEN_IN_BIGUNION >>
                 simp[PULL_EXISTS]) >>
  simp[Once EXTENSION, PULL_EXISTS] >>
  rw[EQ_IMP_THM] >- metis_tac[] >>
  rename [‘a ∈ opfn y’, ‘y ∈ pfb’, ‘a ∈ pfb’] >>
  ‘a ∈ nfn y’ by metis_tac[SUBSET_DEF] >>
  ‘IMAGE f (nfn y) ⊆ B’ by simp[] >>
  pop_assum mp_tac >>
  simp_tac (srw_ss())[Abbr‘pfb’, SUBSET_DEF, PULL_EXISTS] >>
  metis_tac[in_open_in_topspace]
QED


Definition finer_def:
finer τ1 τ2 ⇔ topspace τ1 = topspace τ2 ∧
 ∀s. open_in τ2 s ⇒ open_in τ1 s
End

Theorem PREIMAGE_I[simp]:
 PREIMAGE I X = X
Proof
 simp[EXTENSION]
QED

Theorem exercise_5_1_10_ii:
   finer τ1 τ2 ⇔
   continuousfn τ1 τ2 I ∧ topspace τ1 = topspace τ2
Proof
  rw[finer_def,continuousfn_def,PREIMAGE_I,EQ_IMP_THM] >>
  gs[iffLR SUBSET_INTER_ABSORPTION,OPEN_IN_SUBSET]
QED

Theorem exercise_5_1_12:
  continuousfn τ1 τ2 f ∧ INJ f (topspace τ1) (topspace τ2) ⇒
  (* i *) (T2_space τ2 ⇒ T2_space τ1) ∧
  (* ii *) (T1_space τ2 ⇒ T1_space τ1)
Proof
  rw[T2_space_def, chap1Theory.T1_space_def] >~
  [‘closed_in t1 {a}’, ‘INJ _ (topspace t1) (topspace t2)’]
  >- (gs[prop_5_1_9] >>
      ‘f a ∈ topspace t2’ by simp[] >>
      ‘closed_in t2 {f a}’ by simp[] >>
      ‘PREIMAGE f {f a} ∩ topspace t1 = {a}’ suffices_by metis_tac[] >>
      simp[EXTENSION, EQ_IMP_THM] >> metis_tac[INJ_DEF]) >~
  [‘a ∈ topspace τ1’, ‘b ∈ topspace τ1’, ‘a ≠ b’]
  >- (gs[continuousfn_def] >>
      ‘f a ∈ topspace τ2 ∧ f b ∈ topspace τ2 ∧ f a ≠ f b’
        by metis_tac[INJ_DEF] >>
      first_x_assum $ drule_all_then strip_assume_tac >>
      rename [‘open_in τ2 fA’, ‘open_in τ2 fB’, ‘fA ∩ fB = ∅’] >>
      qabbrev_tac ‘fA' = PREIMAGE f fA ∩ topspace τ1’ >>
      qabbrev_tac ‘fB' = PREIMAGE f fB ∩ topspace τ1’ >>
      ‘open_in τ1 fA' ∧ open_in τ1 fB'’ by metis_tac[] >>
      qexistsl [‘fA'’, ‘fB'’] >> simp[Abbr‘fA'’, Abbr‘fB'’] >>
      gs[EXTENSION] >> metis_tac[])
QED

Theorem SUBSET_closure[simp]:
  A ⊆ closure t A
Proof
  simp[closure_def]
QED

(*
closure_subset_topspace
remark_3_1_10_ii
*)

Theorem exercise_5_1_13:
  (∀a. a ∈ topspace t1 ⇒ f a ∈ topspace t2) ⇒
  (continuousfn t1 t2 f ⇔
     ∀A. A ⊆ topspace t1 ⇒
         IMAGE f (closure t1 A) ⊆ closure t2 (IMAGE f A))
Proof
  rw[prop_5_1_9, EQ_IMP_THM]
  >- (‘closed_in t2 (closure t2 (IMAGE f A))’
        by (irule remark_3_1_10_i >>
            simp[SUBSET_DEF, PULL_EXISTS] >>
            metis_tac[SUBSET_DEF]) >>
      first_x_assum $ drule_then strip_assume_tac >>
      qabbrev_tac ‘B = IMAGE f A’ >>
      qabbrev_tac ‘A2 = PREIMAGE f (closure t2 B) ∩ topspace t1’ >>
      ‘closure t1 A ⊆ A2’
        by (irule remark_3_1_10_ii >>
            simp[SUBSET_DEF, PULL_EXISTS, Abbr‘A2’] >>
            gs[SUBSET_DEF] >> qx_gen_tac ‘a’ >>
            strip_tac >>
            irule $ iffLR SUBSET_DEF >> qexists ‘B’ >>
            simp[] >> simp[Abbr‘B’]) >>
      irule SUBSET_TRANS >>
      irule_at Any IMAGE_SUBSET>>
      first_assum $ irule_at Any >>
      simp[Abbr‘A2’, SUBSET_DEF, PULL_EXISTS]) >>
  rename [‘closed_in t1 (PREIMAGE f B ∩ topspace t1)’] >>
  qabbrev_tac ‘A = PREIMAGE f B ∩ topspace t1’ >>
  ‘A ⊆ topspace t1’ by simp[Abbr‘A’] >>
  ‘A = closure t1 A’ suffices_by (DISCH_THEN SUBST1_TAC >> simp[remark_3_1_10_i]) >>
  simp[SET_EQ_SUBSET,SUBSET_DEF] >> qx_gen_tac ‘a’ >> strip_tac >>
  ‘a ∈ topspace t1’ by metis_tac[closure_subset_topspace,SUBSET_DEF] >>
  ‘f a ∈ B’ suffices_by simp[Abbr ‘A’] >>
  first_x_assum drule >> simp[SUBSET_DEF,PULL_EXISTS] >> DISCH_THEN drule >>
  ‘IMAGE f A ⊆ B’ by simp[Abbr‘A’, SUBSET_DEF, PULL_EXISTS] >>
  metis_tac [remark_3_1_10_ii,SUBSET_DEF]
QED


Theorem prop_5_2_1:
  continuousfn t1 t2 f ∧ SURJ f (topspace t1) (topspace t2) ∧
  connected t1 ⇒ connected t2
Proof
  rw[connected_def] >> CCONTR_TAC >>
  rename [‘clopen t2 U’] >>
  Cases_on ‘U = {}’ >> gs[] >> Cases_on ‘U = topspace t2’ >> gs[] >>
  ‘clopen t1 (PREIMAGE f U ∩ topspace t1)’
    by (simp_tac (srw_ss()) [chap1Theory.clopen_def] >>
        metis_tac[prop_5_1_9,continuousfn_def,chap1Theory.clopen_def]) >>
  pop_assum mp_tac >> simp[] >>
  simp[EXTENSION] >> reverse strip_tac (* 2 *)
  >- (gs[SURJ_DEF] >>
      metis_tac[MEMBER_NOT_EMPTY,chap1Theory.clopen_def,
                OPEN_IN_SUBSET,SUBSET_DEF]) >>
  simp[EQ_IMP_THM] >>
  pop_assum mp_tac >> simp[EXTENSION,EQ_IMP_THM] >>
  metis_tac[SURJ_DEF,SUBSET_DEF,chap1Theory.clopen_def,
            OPEN_IN_SUBSET]
QED




        
val _ = export_theory();