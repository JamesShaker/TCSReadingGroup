open HolKernel Parse boolLib bossLib;

open chap1Theory chap3Theory chap4Theory pred_setTheory topologyTheory
     arithmeticTheory

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

Definition has_fixed_points_def:
  has_fixed_points t = ∀f. continuousfn t t f ⇒
                           ∃x. x ∈ topspace t ∧ f x = x
End

Theorem exercise_5_2_3_iii:
  a ≠ b ∧ a ∈ X ∧ b ∈ X ⇒
    ¬has_fixed_points (discrete_topology X) ∧
    ¬has_fixed_points (indiscrete_topology X)
Proof
  rw[has_fixed_points_def, continuousfn_def]
  >- (qexists `λx. if x = a then b else a` >> rw[])
  >> (rw[DISJ_IMP_THM] >> qexists `λx. if x = a then b else a` >>
      rw[EXTENSION] >> DISJ1_TAC >> rw[])
QED

(*
Theorem exercise_5_2_3_iv:
  has_fixed_points (finite_closed_topology X) ⇔ ∃a. X = {a}
Proof
  reverse $ rw[has_fixed_points_def, prop_5_1_9, EQ_IMP_THM]
  >- gs[]
  >> Cases_on `X = ∅` >> gs[] >> CCONTR_TAC >> gs[] >>
  `∃a b. a ≠ b ∧ a ∈ X ∧ b ∈ X`
    by (CCONTR_TAC >> gs[] >> `∃x. x ∈ X` by metis_tac[MEMBER_NOT_EMPTY] >>
        `X ≠ {x}` by gs[] >> pop_assum mp_tac >>
        simp_tac (srw_ss ()) [EXTENSION] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`λx. if x = a then b else a`] mp_tac) >>
  rw[] >> rw[]
  >- (rw[EXTENSION] >> DISJ1_TAC >> rw[])
  >- ()
  >>

QED
*)


Theorem FINITE_DERANGEMENT_EX:
  ∀s x1 x2. x1 ∈ s ∧ x2 ∈ s ∧ x1 ≠ x2 ∧ FINITE s ⇒
            ∃f. BIJ f s s ∧ ∀x. x ∈ s ⇒ f x ≠ x
Proof            
  ‘∀n. 1 < n ⇒ ∃f. BIJ f (count n) (count n) ∧ ∀m. m < n ⇒ f m ≠ m’
    suffices_by
    (rw[] >>
     ‘∃f n. BIJ f s (count n)’ by metis_tac[FINITE_BIJ_COUNT,BIJ_SYM] >>
     ‘1 < n’
       by (CCONTR_TAC >> gs[arithmeticTheory.NOT_LESS] >>
           Cases_on ‘n = 0’ >> gs[] >>
           ‘n = 1’ by simp[] >>
           gs[BIJ_DEF,INJ_IFF,DECIDE “x < 1 ⇔ x = 0”]) >>
    first_x_assum $ drule_then (qx_choose_then ‘g’ strip_assume_tac) >>
    qexists ‘LINV f s o g o f’ >> rw[] (* 2 *)
    >- (irule BIJ_COMPOSE  >> irule_at Any BIJ_LINV_BIJ >>
       first_assum $ irule_at Any >>
       irule BIJ_COMPOSE >> metis_tac[]) >>
    disch_then (mp_tac o Q.AP_TERM ‘f’) >>
    rev_drule_then assume_tac BIJ_LINV_INV >>
    ‘f x ∈ count n ∧ g (f x) ∈ count n’ by metis_tac[BIJ_DEF,INJ_DEF] >>
    simp[] >> first_x_assum irule >> gs[]) >>
 rw[] >> qexists ‘λm. if m = 0 then n - 1 else m - 1’  >>
 simp[BIJ_DEF,INJ_IFF,SURJ_DEF,AllCaseEqs(),SF DNF_ss] >>
 rw[DECIDE “x ≠ 0 ⇒ (x - 1 = y ⇔ x = y + 1)”,SF CONJ_ss]
QED 

Theorem INF_COUNTABLE_DERANGEMENT_EX:
  INFINITE A ∧ countable A ⇒
  ∃f. f PERMUTES A ∧
      ∀x. x ∈ A ⇒ f x ≠ x
Proof
  ‘∃d. d PERMUTES 𝕌(:num) ∧ ∀n. d n ≠ n’ by (
    qexists_tac ‘λi. if EVEN i then i + 1 else i - 1’ >> rw[]
    >~ [‘¬EVEN _’] >- (strip_tac >> ‘n = 0’ by simp[] >> gs[]) >>
    rw[BIJ_DEF,INJ_DEF,SURJ_DEF,AllCaseEqs()] >>
    gs[GSYM ODD_EVEN] >>
    imp_res_tac ODD_POS >> gs[]
    >~ [‘_ ∨ _’] >- (csimp[EXISTS_OR_THM,DECIDE “x + 1n = y ⇔ x = y - 1n ∧ 0 < y”,
                           EVEN_SUB, GSYM ODD_EVEN, ODD_POS] >>
                     csimp[DECIDE “0 < x ⇒ (x - 1n = y ⇔ x = y + 1n)”,
                           ODD_POS, ODD_ADD]) >>
    gs[DECIDE “0 < x ⇒ (x - 1n = y ⇔ x = y + 1n) ∧ (y = x - 1n ⇔ x = y + 1n)”,
       ODD_POS, ODD_ADD, EVEN_ODD]) >>
  rw[] >> gs[COUNTABLE_ALT_BIJ] >>
  drule_then strip_assume_tac BIJ_INV >> gs[] >>
  qexists ‘enumerate A ∘ d ∘ g’ >> rw[]
  >- (rpt $ irule_at Any BIJ_COMPOSE >> metis_tac[]) >>
  disch_then $ mp_tac o Q.AP_TERM ‘g’ >> simp[]
QED

Theorem DERANGEMENT_EX:
  ∀s x1 x2. x1 ∈ s ∧ x2 ∈ s ∧ x1 ≠ x2 ⇒
            ∃f. BIJ f s s ∧ ∀x. x ∈ s ⇒ f x ≠ x
Proof
  rw[] >> Cases_on ‘FINITE s’ >- metis_tac[FINITE_DERANGEMENT_EX] >>
  drule_then strip_assume_tac
             cardinalTheory.disjoint_countable_decomposition>>
  ‘∀x. x ∈ s ⇒ ∃a. a ∈ A ∧ x ∈ a’ by (rw[] >> metis_tac[]) >>
  gs[SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] >>
  ‘∀a. a ∈ A ⇒ ∃d. d PERMUTES a ∧ ∀x. x ∈ a ⇒ d x ≠ x’
    by metis_tac[INF_COUNTABLE_DERANGEMENT_EX] >>
  gs[SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] >>
  rename [‘f _ ∈ A ∧ _ ∈ f _’, ‘g _ PERMUTES _’] >>
  qexists ‘λx. g (f x) x’ >>
  simp[BIJ_DEF,INJ_DEF,SURJ_DEF] >>
  rpt strip_tac
  >>~- ([‘g (f x) x ∈ s’], rw[] >> metis_tac[BIJ_DEF,INJ_DEF])
  >~ [‘g (f a) a = g (f b) b’] >- (Cases_on ‘f a = f b’
                                   >- (metis_tac[INJ_DEF,BIJ_DEF]) >>
                                   ‘a ∈ f a ∧ b ∈ f b ∧ f a ∈ A ∧ f b ∈ A’ by
                                     metis_tac[] >>
                                   ‘g (f a) a ∈ f a ∧ g (f b) b ∈ f b’ by
                                     metis_tac[INJ_DEF,BIJ_DEF] >>
                                   ‘DISJOINT (f a) (f b)’ by metis_tac[] >>
                                   metis_tac[DISJOINT_DEF,IN_INTER,NOT_IN_EMPTY]) >>
  ‘f x ∈ A’ by simp[] >>
  first_x_assum $ drule_then strip_assume_tac >>
  drule_then (qx_choose_then ‘gi’ strip_assume_tac) BIJ_INV >>
  qexists ‘gi x’ >> ‘gi x ∈ f x’ by metis_tac[BIJ_DEF,SURJ_DEF] >>
  conj_asm1_tac
  >- (rw[] >> metis_tac[]) >>
  ‘f (gi x) = f x’ suffices_by gs[] >>
  CCONTR_TAC >>
  ‘gi x ∈ f (gi x) ∧ DISJOINT (f x) (f (gi x))’ by metis_tac[] >>
  pop_assum $ mp_tac o SRULE [DISJOINT_DEF] >>
  simp[GSYM MEMBER_NOT_EMPTY] >> metis_tac[]
QED

(*
Theorem exercise_5_2_3_iv:
  has_fixed_points (finite_closed_topology X) ⇔ X ≠ ∅
Proof
  rw[has_fixed_points_def, prop_5_1_9, EQ_IMP_THM]
  >- (strip_tac >> gs[])
  >>
QED
*)

(*
finite_closed_topology
chap1Theory.finite_closed_topology_def
INSERT_DEF
has_fixed_points_def
continuousfn_def
topology
topology_tybij
istopology
topspace
*)
Theorem exercise_5_2_3_iv_bool:
  ¬has_fixed_points (finite_closed_topology {T;F})
Proof
  simp[chap1Theory.finite_closed_topology_def,ABSORPTION_RWT] >>
  simp[has_fixed_points_def,continuousfn_def] >>
  ‘∀A. open_in (topology {s | s ⊆ 𝟚}) A ⇔ A ⊆ 𝟚’ by (
    rw[] >> ‘istopology {s | s ⊆ 𝟚}’ suffices_by simp[topology_tybij] >>
    simp[istopology,SUBSET_DEF]) >>
  ‘topspace (topology {s | s ⊆ 𝟚}) = 𝟚’ by (
    rw[EXTENSION,topspace] >> qexists_tac ‘𝟚’ >> simp[]) >>
  simp[] >> qexists_tac ‘$¬’ >> metis_tac[]
QED

Theorem exercise_5_2_3_iv:
  has_fixed_points (finite_closed_topology A) ⇔ ∃a. A = {a}
Proof
  reverse eq_tac
  >- simp[PULL_EXISTS, has_fixed_points_def, continuousfn_def] >>
  simp[has_fixed_points_def, continuousfn_def] >> strip_tac >>
  CCONTR_TAC >> gs[] >>
  Cases_on ‘A = {}’ >- gvs[] >>
  ‘∃a b. a ≠ b ∧ a ∈ A ∧ b ∈ A’
    by (CCONTR_TAC >>
        ‘∀a b. a ∈ A ∧ b ∈ A ⇒ a = b’ by metis_tac[] >>
        qpat_x_assum ‘A ≠ ∅’ mp_tac >>
        simp[EXTENSION] >> rpt strip_tac >>
        qpat_x_assum ‘∀a. A ≠ {a}’ mp_tac >> simp[] >>
        qexists_tac ‘x’ >> simp[EXTENSION] >> metis_tac[]) >>
  drule_all_then (qx_choose_then ‘d’ strip_assume_tac)
                 DERANGEMENT_EX >>
  first_x_assum $ qspec_then ‘d’ mp_tac >> rw[] >>
  simp[]
  >- metis_tac[BIJ_DEF, INJ_DEF] >~
  [‘FINITE (A DIFF PREIMAGE d B ∩ A)’]
  >- (‘A DIFF PREIMAGE d B ∩ A = A DIFF PREIMAGE d B’
        by (simp[EXTENSION] >> metis_tac[]) >>
      simp[] >>
      ‘FINITE (A DIFF PREIMAGE d B)’
        suffices_by simp[] >>
      irule $ iffLR cardinalTheory.CARDEQ_FINITE >>
      first_assum $ irule_at Any >>
      simp[cardinalTheory.cardeq_def] >>
      irule $ iffLR BIJ_SYM >> qexists ‘d’ >>
      gs[BIJ_DEF, INJ_IFF, SURJ_DEF] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem exercise_5_2_3_v:
  has_fixed_points τ ∧ homeomorphism (τ,τ₁) (f,g) ⇒
  has_fixed_points τ₁
Proof
  rw[has_fixed_points_def] >>
  rename [‘continuousfn τ₁ τ₁ h’] >>
  ‘continuousfn τ τ (g o h o f)’
    by metis_tac[prop_5_1_11, prop_5_1_8] >>
  first_x_assum $ drule_then strip_assume_tac >>
  gs[] >> pop_assum (mp_tac o Q.AP_TERM ‘f’) >>
  ‘f x ∈ topspace τ₁’
    by metis_tac[homeomorphism, BIJ_DEF, INJ_DEF] >>
  ‘h (f x) ∈ topspace τ₁’
    by metis_tac[continuousfn_def] >>
  gs[prop_5_1_11] >> metis_tac[]
QED

(* Uof : ('a -> 'b) -> (('a -> bool) -> bool) -> ('b -> bool)

   Uof x::A. ....x...

*)

Theorem lemma:
  A ⊆ B ∧ C = D1 ∩ B ∧ C = D2 ∩ B ⇒
  D1 ∩ A = D2 ∩ A
Proof
  SET_TAC[]
QED

Theorem lemma2:
  A ⊆ B ∧ A ⊆ C ∧ A ≠ ∅ ∧ A ≠ B ∩ C ⇒
  ∃a. a ∈ B ∧ a ∈ C ∧ a ∉ A
Proof
  SET_TAC[]
QED


Theorem exercise_5_2_4:
  (∀j. j ∈ J ⇒ connected (subtopology τ $ A j) ∧ A j ⊆ topspace τ) ∧
  BIGINTER (IMAGE A J) ≠ ∅ ⇒
  connected (subtopology τ $ BIGUNION (IMAGE A J))
Proof
  rw[connected_def, TOPSPACE_SUBTOPOLOGY] >>
  reverse eq_tac
  >- (simp[DISJ_IMP_THM] >>
      simp[clopen_def, OPEN_IN_SUBTOPOLOGY, CLOSED_IN_SUBTOPOLOGY] >>
      strip_tac >> simp[PULL_EXISTS] >>
      rpt (irule_at Any EQ_REFL) >> simp[]) >>
  CCONTR_TAC >> gs[] >>
  ‘s ⊆ topspace τ ∩ BIGUNION (IMAGE A J)’
    by metis_tac[OPEN_IN_SUBSET, TOPSPACE_SUBTOPOLOGY, clopen_def] >>
  ‘∃a. a ∈ BIGINTER (IMAGE A J)’ by metis_tac[MEMBER_NOT_EMPTY] >>
  gs[PULL_EXISTS] >>
  ‘a ∈ topspace τ’ by (irule (iffLR SUBSET_DEF) >>
                       first_assum (irule_at Any o cj 2) >>
                       csimp[] >> CCONTR_TAC >>
                       ‘J = ∅’ by metis_tac[MEMBER_NOT_EMPTY] >>
                       gs[]) >>
  Cases_on ‘s ∩ BIGINTER (IMAGE A J) = ∅’
  >- (‘a ∉ s’ by (strip_tac >> qpat_x_assum ‘_ ∩ _ = ∅’ mp_tac >>
                  simp[Once EXTENSION] >> metis_tac[]) >>
      ‘∃b. b ∈ s ∧ b ∈ BIGUNION (IMAGE A J)’
        by metis_tac[SUBSET_DEF, MEMBER_NOT_EMPTY] >>
      gvs[] >> rename [‘j ∈ J’, ‘b ∈ A j’, ‘b ∈ s’, ‘a ∉ s’] >>
      ‘s ∩ A j ≠ topspace τ ∩ A j’
        by (simp[EXTENSION] >> metis_tac[]) >>
      ‘s ∩ A j ≠ ∅’ by metis_tac[MEMBER_NOT_EMPTY, IN_INTER] >>
      ‘¬clopen (subtopology τ (A j)) (s ∩ A j)’ by metis_tac[] >>
      pop_assum mp_tac >> ASM_REWRITE_TAC[clopen_def] >>
      qpat_x_assum ‘clopen _ _ ’ mp_tac >>
      simp[clopen_def, OPEN_IN_SUBTOPOLOGY, CLOSED_IN_SUBTOPOLOGY] >>
      simp[PULL_EXISTS] >> rpt strip_tac >>
      ‘BIGUNION (IMAGE A J) ∩ A j = A j ∧ A j ⊆ BIGUNION (IMAGE A J)’
        suffices_by (simp[GSYM INTER_ASSOC] >> metis_tac[lemma]) >>
      simp[INTER_SUBSET_EQN] >> simp[SUBSET_DEF, PULL_EXISTS] >> metis_tac[]) >>
  ‘∃b. b ∈ topspace τ ∧ b ∈ BIGUNION (IMAGE A J) ∧ b ∉ s’
    by metis_tac[lemma2] >>
  ‘∃j. j ∈ J ∧ b ∈ A j’ by gs[SF SFY_ss] >>
  ‘s ∩ A j ≠ ∅’
    by (qpat_x_assum ‘s ∩ _ ≠ _’ mp_tac >> ONCE_REWRITE_TAC[EXTENSION] >>
        simp[] >> metis_tac[]) >>
  ‘s ∩ A j ≠ topspace τ ∩ A j’
    by (simp[EXTENSION] >> qexists ‘b’ >> simp[]) >>
  ‘¬clopen (subtopology τ (A j)) (s ∩ A j)’ by metis_tac[] >>
  pop_assum mp_tac >> qpat_x_assum ‘clopen _ _’ mp_tac >>
  REWRITE_TAC[clopen_def] >> simp[OPEN_IN_SUBTOPOLOGY, CLOSED_IN_SUBTOPOLOGY] >>
  simp[PULL_EXISTS] >> rpt strip_tac >>
  ‘BIGUNION (IMAGE A J) ∩ A j = A j ∧ A j ⊆ BIGUNION (IMAGE A J)’
    suffices_by (simp[GSYM INTER_ASSOC] >> metis_tac[lemma]) >>
  simp[INTER_SUBSET_EQN] >> simp[SUBSET_DEF, PULL_EXISTS] >> metis_tac[]
QED

Theorem not_connected:
  ∀top. ¬connected top ⇔ ∃s. clopen top s ∧ s ≠ topspace top ∧ s ≠ ∅
Proof
  metis_tac[connected_def,clopen_topspace,clopen_EMPTY]
QED

Theorem CLOPEN_IN_SUBTOPOLOGY_IMP:
  ∀top A s. clopen top s ⇒ clopen (subtopology top A) (s ∩ A)
Proof
  metis_tac[clopen_def,OPEN_IN_SUBTOPOLOGY,CLOSED_IN_SUBTOPOLOGY]
QED

Theorem clopen_DIFF:
  clopen τ s ⇒ clopen τ (topspace τ DIFF s)
Proof
  simp[clopen_def,closed_in,DIFF_DIFF_SUBSET]      
QED

(*
clopen τ' t
clopen subtopology τ (closure τ A) t
*)

(*
Lemma: ¬connected τ ⇔ ∃s. clopen τ s ∧ s ≠ topspace τ ∧ s ≠ ∅
Lemma: clopen τ s ⇒ clopen (subtopology τ A) (s ∩ A)
  This actually needs a more congruence friendly version

Goal: connected (subtopology τ A) ∧ A ⊆ topspace τ ⇒ connected (subtopology τ (closure τ A))

Contrapositive: ¬connected (subtopology τ (closure τ A)) ⇒ ¬connected (subtopology τ A) ∧ A ⊆ topspace τ
  Have: clopen (subtopology τ (closure τ A)) s ∧ s ≠ (closure τ A) ∧ s ≠ ∅
  Need: ∃r. clopen (subtopology τ A) r ∧ r ≠ A ∧ r ≠ ∅

Sub-goal: ∃t. clopen (subtopology τ (closure τ A)) t ∧ t ≠ (closure τ A) ∧ t ≠ ∅ ∧ t ∩ A ≠ ∅
  Either t is s or (closure τ A) DIFF s

Witness: t ∩ A
  clopen (subtopology τ A) (t ∩ A): trivial from clopen (subtopology τ (closure τ A)) t
  t ∩ A ≠ ∅: trivial

Goal reduces to t ∩ A ≠ A.

Contradiction: suppose not
  So assume A ⊆ t

A ⊆ t
closure (subtopology τ (closure τ A)) A ⊆ closure (subtopology τ (closure τ A)) t
(closure τ A) ⊆ t   (since t is closed in (subtopology τ (closure τ A)))
contradicting t ≠ (closure τ A) and clopen (subtopology τ (closure τ A)) t
*)

Theorem exercise_5_2_5:
  connected (subtopology τ A) ∧ A ⊆ topspace τ ⇒
  connected (subtopology τ (closure τ A)) ∧
  ∀B. A ⊆ B ∧ B ⊆ closure τ A ⇒ connected (subtopology τ B)
Proof
  rw[]
  >- (Cases_on ‘closure τ A = A’ >> simp[] >>
      CCONTR_TAC >> qpat_x_assum ‘connected _’ mp_tac >>
      gs[not_connected] >> qabbrev_tac ‘τ' = (subtopology τ (closure τ A))’ >>
      ‘∃t. clopen τ' t ∧ t ≠ topspace τ' ∧ t ≠ ∅ ∧ t ∩ A ≠ ∅’ by (
        reverse $ Cases_on ‘s ∩ A = ∅’ >- metis_tac[] >>
        qexists_tac ‘topspace τ' DIFF s’ >>
        ‘s ⊆ topspace τ'’ by gs[clopen_def,OPEN_IN_SUBSET] >>
        rpt strip_tac
        >- simp[clopen_DIFF]
        >- (gs[X_DIFF_EQ_X] >>
            metis_tac[DISJOINT_ALT,SUBSET_DEF,GSYM MEMBER_NOT_EMPTY])
        >- (gs[EXTENSION,SUBSET_DEF] >> metis_tac[])
        >- (qpat_x_assum ‘_ = ∅’ mp_tac >>
            simp[EXTENSION] >>
            Cases_on ‘A = ∅’ >> gs[closure_EMPTY] >>
            gs[GSYM MEMBER_NOT_EMPTY] >>
            first_assum $ irule_at Any >>
            gs[Abbr ‘τ'’,TOPSPACE_SUBTOPOLOGY] >>
            metis_tac[SUBSET_closure,SUBSET_DEF,NOT_IN_EMPTY,IN_INTER])) >>
      first_assum $ irule_at Any >> strip_tac
      >- (drule_then (qspec_then ‘A’ mp_tac) CLOPEN_IN_SUBTOPOLOGY_IMP >>
          simp[Abbr ‘τ'’,SUBTOPOLOGY_SUBTOPOLOGY] >>
          ‘closure τ A ∩ A = A’ suffices_by simp[] >>
          simp[INTER_SUBSET_EQN]) >>
      simp[TOPSPACE_SUBTOPOLOGY,SUBSET_INTER2,INTER_SUBSET_EQN] >>
      strip_tac >>
      ‘t ⊆ topspace τ'’ by gs[clopen_def,OPEN_IN_SUBSET] >>
      drule_all_then assume_tac closure_monotone >>
      ‘closure τ' t = t’ by gs[clopen_def,closure_of_closed] >>
      ‘A ⊆ topspace τ'’
       by simp[Abbr‘τ'’,TOPSPACE_SUBTOPOLOGY] >> 
      ‘closure τ' A = topspace τ'’ by
        (irule $ iffLR dense_def >>
         simp[dense_nontrivial_inters] >>
         simp[Abbr‘τ'’,OPEN_IN_SUBTOPOLOGY,PULL_EXISTS] >>
         simp[GSYM INTER_ASSOC,SUBSET_INTER2] >>
         simp[closure_def] >> rpt strip_tac >>
         gs[GSYM MEMBER_NOT_EMPTY] (* 2 *)
         >- (pop_assum mp_tac >>
             metis_tac[MEMBER_NOT_EMPTY,IN_INTER]) >>
         gs[limpt_thm] >>
         metis_tac[MEMBER_NOT_EMPTY,IN_INTER])  >>
      gs[] >> metis_tac[SUBSET_ANTISYM]) >>
  cheat
QED

        
val _ = export_theory();
