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
        (qpat_x_assum ‘X ∩ (A ∪ B) = Y ∩ (A ∪ B)’ mp_tac >> simp[EXTENSION] >>
         metis_tac[]) >>
      ‘(X ∩ A = topspace τ ∩ A ∨ X ∩ A = {}) ∧
       (X ∩ B = topspace τ ∩ B ∨ X ∩ B = {})’
        by metis_tac[] >>
      gs[SUBSET_DEF,EXTENSION] >> metis_tac[])
  >- metis_tac[CLOSED_IN_TOPSPACE,OPEN_IN_TOPSPACE] >>
  metis_tac[OPEN_IN_EMPTY,CLOSED_IN_EMPTY,INTER_EMPTY]
QED


Theorem excercise_4_1_12:
  T1_space τ ⇒ T1_space (subtopology τ Y)
Proof
  fs[T1_space_def,CLOSED_IN_SUBTOPOLOGY,TOPSPACE_SUBTOPOLOGY] >>
  rw[] >> ntac 2 (first_assum (irule_at Any)) >>
  simp[EXTENSION] >> metis_tac[]
QED


Definition T2_space_def:
  T2_space τ ⇔ ∀a b. a ∈ topspace τ ∧ b ∈ topspace τ ∧ a ≠ b ⇒
               ∃A B. open_in τ A ∧ open_in τ B ∧ a ∈ A ∧ b ∈ B ∧ A ∩ B = ∅
End

Overload Hausdorff[inferior] = “T2_space”

Theorem excercise_4_1_13_ii:
  T2_space (discrete_topology X)
Proof
  rw[T2_space_def] >>
  rename1 ‘a ≠ b’ >>
  qexistsl_tac [‘{a}’,‘{b}’] >>
  rw[EXTENSION]
QED

Theorem excercise_4_1_13_iii:
  T2_space τ ⇒ T1_space τ
Proof
  rw[T2_space_def,T1_space_def,closed_in] >>
  ‘∃AS. topspace τ DIFF {x} = BIGUNION AS ∧ ∀A. A ∈ AS ⇒ open_in τ A’
    suffices_by simp[PULL_EXISTS,OPEN_IN_BIGUNION] >>
  ‘∀y. y ≠ x ∧ y ∈ topspace τ ⇒ ∃A. y ∈ A ∧ x ∉ A ∧ open_in τ A’
    suffices_by
      (rw[] >>
       pop_assum (strip_assume_tac o
                  SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM]) >>
       qexists_tac ‘{f y | y ∈ topspace τ ∧ y ≠ x}’ >> simp[Once EXTENSION] >>
       rpt strip_tac >> rw[PULL_EXISTS,EQ_IMP_THM] >>
       metis_tac[OPEN_IN_SUBSET,SUBSET_DEF]) >>
  rw[] >> first_x_assum drule_all >> rw[] >> gs[EXTENSION] >>
  metis_tac[]
QED

Theorem excercise_4_1_13_iv_a:
  T1_space (finite_closed_topology 𝕌(:num))
Proof
  simp[T1_space_def]
QED

Theorem excercise_4_1_13_iv_b:
  ¬T2_space (finite_closed_topology 𝕌(:num))
Proof
  simp[T2_space_def] >> qexistsl_tac [‘1’, ‘2’] >> simp[] >>
  rpt strip_tac >> Cases_on ‘1 ∈ A’ >> simp[] >>
  Cases_on ‘2 ∈ B’ >> simp[] >>
  simp[GSYM MEMBER_NOT_EMPTY, SF SFY_ss] >> CCONTR_TAC >>
  gs[] >> qabbrev_tac ‘A' = UNIV DIFF A’ >>
  qabbrev_tac ‘B' = UNIV DIFF B’ >>
  ‘FINITE (A' UNION B')’ by simp[] >>
  ‘A' ∪ B' = UNIV’ by
    (simp[EXTENSION, Abbr ‘A'’, Abbr ‘B'’] >>
     gs[EXTENSION]) >>
  pop_assum SUBST_ALL_TAC >>  gs[]
QED

Theorem exercise_4_1_13_v:
  T2_space τ ⇒ T2_space (subtopology τ X)
Proof
  simp[T2_space_def, TOPSPACE_SUBTOPOLOGY, OPEN_IN_SUBTOPOLOGY] >>
  rpt strip_tac >> simp[PULL_EXISTS] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  first_assum $ irule_at (Pat ‘_ ∈ _’) >>
  first_assum $ irule_at (Pat ‘_ ∈ _’) >> simp[] >>
  gs[EXTENSION] >> metis_tac[]
QED

Theorem exercise_4_1_13_vi:
  T2_space τ ∧ door_space τ ⇒
  (∀x y. limpt τ x (topspace τ) ∧ limpt τ y (topspace τ) ⇒ x = y) ∧
  (∀z. z ∈ topspace τ ∧ ¬limpt τ z (topspace τ) ⇒ open_in τ {z})
Proof
  simp[T2_space_def, door_space_def] >> strip_tac >>
  reverse conj_tac
  >- (simp[not_limpt_inter, SF CONJ_ss, PULL_EXISTS] >> rpt strip_tac
      >- (‘{z} = U’ suffices_by simp[] >>
          qpat_x_assum ‘_ ∩ _ = _’ mp_tac >>
          simp[EXTENSION] >> metis_tac[OPEN_IN_SUBSET, SUBSET_DEF]) >>
      gs[EXTENSION] >> metis_tac[]) >>
  CCONTR_TAC >> gs[] >> rename [‘l1 ≠ l2’] >>
  ‘l1 ∈ topspace τ ∧ l2 ∈ topspace τ’ by metis_tac[limpt_thm] >>
  first_assum $ drule_all_then $
    qx_choosel_then [‘O1’, ‘O2’] strip_assume_tac >>
  ‘¬open_in τ {l1} ∧ ¬open_in τ {l2}’
    by (gs[limpt_thm] >> metis_tac[IN_INSERT, NOT_IN_EMPTY]) >>
  ‘∃R1. R1 ≠ ∅ ∧ l1 ∉ R1 ∧ O1 = l1 INSERT R1’
    by (qexists_tac ‘O1 DELETE l1’ >> simp[] >> metis_tac[]) >>
  ‘∃R2. R2 ≠ ∅ ∧ l2 ∉ R2 ∧ O2 = l2 INSERT R2’
    by (qexists_tac ‘O2 DELETE l2’ >> simp[] >> metis_tac[]) >>
  gvs[] >>
  Cases_on ‘open_in τ (l2 INSERT R1)’
  >- (‘open_in τ ((l2 INSERT R1) ∩ (l2 INSERT R2))’
        by simp[OPEN_IN_INTER] >>
      ‘(l2 INSERT R1) ∩ (l2 INSERT R2) = {l2}’
        by (gs[EXTENSION] >> metis_tac[]) >>
      gvs[]) >>
  ‘l2 INSERT R1 ⊆ topspace τ’
    by metis_tac[OPEN_IN_SUBSET, SUBSET_DEF, IN_INSERT] >>
  ‘closed_in τ (l2 INSERT R1)’ by metis_tac[] >>
  qabbrev_tac ‘Q = topspace τ DIFF (l2 INSERT R1)’ >>
  ‘open_in τ Q’ by gs[closed_in] >>
  ‘open_in τ (Q ∩ (l1 INSERT R1))’ by simp[OPEN_IN_INTER] >>
  ‘Q ∩ (l1 INSERT R1) = {l1}’ by (gs[EXTENSION, Abbr‘Q’] >> metis_tac[]) >>
  gs[]
QED

Theorem corollary_model:
  istopology { s | 0 ∈ s ∧ FINITE (COMPL s) ∨ 0 ∉ s }
Proof
  simp[istopology] >> rw[] >> simp[]
  >- (simp[] >> gs[COMPL_DEF] >>
      ‘UNIV DIFF (s ∩ t) = (UNIV DIFF s) ∪ (UNIV DIFF t)’ suffices_by simp[] >>
      simp[EXTENSION]) >>
  gs[COMPL_DEF] >> Cases_on ‘∀s. s ∈ k ⇒ 0 ∉ s’ >> gs[]
  >- metis_tac[] >>
  gs[SUBSET_DEF] >> first_x_assum drule >> simp[] >> strip_tac >> disj1_tac >>
  conj_tac >- metis_tac[] >>
  irule SUBSET_FINITE_I >> first_assum $ irule_at Any >>
  simp[SUBSET_DEF] >> metis_tac[]
QED

Definition weird_def:
  weird = topology {s | 0 ∈ s ∧ FINITE (COMPL s) ∨ 0 ∉ s }
End

Theorem open_in_weird:
  open_in weird s ⇔ 0 ∈ s ∧ FINITE (COMPL s) ∨ 0 ∉ s
Proof
  simp[weird_def, topology_tybij |> cj 2 |> iffLR, corollary_model]
QED

Theorem topspace_weird:
  topspace weird = UNIV
Proof
  simp[topspace, Once EXTENSION, open_in_weird] >> gen_tac >>
  qexists_tac ‘UNIV’ >> simp[COMPL_DEF]
QED

Theorem weird_T2:
  T2_space weird
Proof
  simp[T2_space_def, open_in_weird, topspace_weird] >>
  rpt strip_tac >>
  wlog_tac ‘b ≠ 0’ [‘a’, ‘b’] >- (gvs[] >> metis_tac[INTER_COMM]) >>
  Cases_on ‘a = 0’
  >- (qexistsl_tac [‘UNIV DELETE b’, ‘{b}’] >>
      simp[COMPL_DEF, DIFF_DIFF_SUBSET, DELETE_DEF] >>
      simp[EXTENSION]) >>
  qexistsl_tac [‘{a}’, ‘{b}’] >> simp[] >> simp[EXTENSION]
QED

Theorem weird_door:
  door_space weird
Proof
  simp[door_space_def, open_in_weird, topspace_weird, closed_in, COMPL_DEF,
       DIFF_DIFF_SUBSET] >>
  metis_tac[]
QED

Theorem limpt_weird:
  limpt weird x (topspace weird) ⇔ x = 0
Proof
  ‘limpt weird 0 (topspace weird)’
    suffices_by metis_tac[exercise_4_1_13_vi, weird_door, weird_T2] >>
  simp[limpt_thm, open_in_weird, topspace_weird, SF CONJ_ss, COMPL_DEF] >>
  rpt strip_tac >>
  ‘INFINITE U’ by metis_tac[FINITE_DIFF_down, INFINITE_NUM_UNIV] >>
  ‘INFINITE (U DELETE 0)’ by simp[] >>
  drule INFINITE_INHAB >> simp[]
QED

Theorem exercise_4_1_14:
  second_countable t ⇒
  second_countable (subtopology t Y)
Proof
  rw[second_countable_def] >>
  irule_at Any example_4_1_4 >>
  first_assum $ irule_at Any >>
  `{b ∩ Y | b ∈ B} = IMAGE (λx. x ∩ Y) B`
    suffices_by simp[image_countable] >>
  rw[EXTENSION]
QED

Definition regular_space_def:
  regular_space t ⇔
    ∀A x.
      closed_in t A ∧
      x ∈ topspace t ∧
      x ∉ A ⇒
      ∃U V.
        open_in t U ∧
        open_in t V ∧
        x ∈ U ∧
        A ⊆ V ∧
        U ∩ V = ∅
End

Definition T3_space_def:
  T3_space t ⇔ regular_space t ∧ T1_space t
End

Theorem exercise_4_1_17_i:
  ∀A t. regular_space t ⇒ regular_space (subtopology t A)
Proof
  rw[regular_space_def] >>
  gvs[CLOSED_IN_SUBTOPOLOGY, TOPSPACE_SUBTOPOLOGY,
      OPEN_IN_SUBTOPOLOGY, PULL_EXISTS] >>
  rename[`closedSets top A`, `A ∩ Y`] >>
  first_x_assum drule_all >> rw[] >>
  qexistsl_tac [`U`, `V`] >> rw[]
  >- metis_tac[SUBSET_DEF, IN_INTER]
  >> metis_tac[INTER_COMM, INTER_ASSOC, INTER_EMPTY]
QED

Theorem exercise_4_1_17_iii:
  T3_space t ⇒ T2_space t
Proof
  rw[T3_space_def, T2_space_def,
     regular_space_def, T1_space_def] >>
  `closedSets t {a}` by metis_tac[] >>
  `b ∉ {a}` by simp[] >>
  last_x_assum drule_all >> rw[] >>
  metis_tac[INTER_COMM]
QED


Definition homeomorphism:
  homeomorphism (s,t) (f,g) ⇔
    BIJ f (topspace s) (topspace t) ∧
    BIJ g (topspace t) (topspace s) ∧
    (∀a. a ∈ topspace s ⇒ g (f a) = a) ∧
    (∀b. b ∈ topspace t ⇒ f (g b) = b) ∧
    (∀V. open_in t V ⇒ open_in s (IMAGE g V)) ∧
    (∀U. open_in s U ⇒ open_in t (IMAGE f U))
End

Theorem homeomorphism_SYM :
 homeomorphism (s,t) (f,g) ⇔ homeomorphism (t,s) (g,f)
Proof
simp[homeomorphism] >> metis_tac[]
QED

Theorem homeomorphism_BIJ0[local] :
 homeomorphism (s,t) (f,g) ⇒
 BIJ f (topspace s) (topspace t)
Proof
  metis_tac[homeomorphism]
QED

Theorem homeomorphism_BIJ :
 homeomorphism (s,t) (f,g) ⇒
 BIJ f (topspace s) (topspace t) ∧
 BIJ g (topspace t) (topspace s)
Proof
 metis_tac[homeomorphism_SYM,homeomorphism_BIJ0]
QED

Theorem homeomorphism_TRANS:
  homeomorphism (s,t) (f,g) ∧ homeomorphism (t,u) (h,j) ⇒
  homeomorphism (s,u) (h o f, g o j)
Proof
  rw[homeomorphism, GSYM IMAGE_IMAGE]
  >- metis_tac[BIJ_COMPOSE]
  >- metis_tac[BIJ_COMPOSE]
  >- (‘f a ∈ topspace t’ suffices_by simp[] >>
      metis_tac[BIJ_DEF, SURJ_DEF])
  >- (‘j b ∈ topspace t’ suffices_by simp[] >>
      metis_tac[BIJ_DEF, SURJ_DEF])
QED

Theorem homeomorphism_REFL:
  homeomorphism (s,s) (I,I)
Proof
  rw[BIJ_DEF, SURJ_DEF, INJ_DEF, homeomorphism]
QED

Theorem homeomorphism_same_domain:
  homeomorphism (t1, t2) (f, g) ∧ (∀x. x ∈ topspace t1 ⇒ f' x = f x)  ⇒
  homeomorphism (t1, t2) (f', g)
Proof
  rw[homeomorphism]
  >- (gs[BIJ_DEF, INJ_IFF, SURJ_DEF] >> simp[SF CONJ_ss])
  >- gs[BIJ_DEF, INJ_IFF, SURJ_DEF]
  >- (‘IMAGE f' U = IMAGE f U’ suffices_by simp[] >>
      irule IMAGE_CONG >> rw[] >> last_x_assum irule >>
      metis_tac[OPEN_IN_SUBSET, SUBSET_DEF])
QED

Theorem exercise4_2_6i:
  let fs = {f | ∃g. homeomorphism (t, t) (f, g) ∧ ∀ x. x ∉ topspace t ⇒ f x = x} in
    ∃e. e ∈ fs ∧ (∀f. f ∈ fs ⇒ f = f o e) ∧
        (∀ f. f ∈ fs ⇒ ∃ g. g ∈ fs ∧ f o g = e) ∧
        (∀f g. f ∈ fs ∧ g ∈ fs ⇒ f o g ∈ fs)
Proof
  rw[] >> qexists_tac ‘I’ >> rw[]
  >- metis_tac[homeomorphism_REFL]
  >- (qexists_tac ‘λx. if x ∈ topspace t then LINV f (topspace t) x else x’ >>
      rw[]
      >- (qexists_tac ‘f’ >>
          dxrule_then assume_tac (iffLR homeomorphism_SYM) >>
          drule_then irule homeomorphism_same_domain >> rw[] >>
          gs[homeomorphism, BIJ_DEF] >> metis_tac[LINV_DEF])
      >- (rw[FUN_EQ_THM] >> rw[] >> gs[homeomorphism] >>
          metis_tac[BIJ_LINV_INV])
     )
  >- (simp[] >> metis_tac[homeomorphism_TRANS])
QED


Theorem exercise_4_2_7i:
 homeomorphism (t1,t2) (f,g) ∧
 T0_space t1 ⇒ T0_space t2
Proof
 rw[T0_space_def,homeomorphism] >>
 ‘g a ∈ topspace t1 ∧ g b ∈ topspace t1 ∧ g a ≠ g b’
 by metis_tac[INJ_DEF,BIJ_DEF] >>
 first_x_assum $ drule_all_then strip_assume_tac
 >- (* 2 *)
 (qexists_tac ‘IMAGE f s’ >> simp[] >> disj1_tac >>
  rw[] (* 2 *)
  >- metis_tac[] >>
  metis_tac[OPEN_IN_SUBSET,SUBSET_DEF]) >>
 qexists_tac ‘IMAGE f s’ >> simp[] >> disj2_tac >>
 rw[] (* 2 *)
 >- metis_tac[] >>
 metis_tac[OPEN_IN_SUBSET,SUBSET_DEF]
QED

Theorem T1_space_alt:
 T1_space t ⇔
 ∀a b. a ∈ topspace t ∧ b ∈ topspace t ∧
       a ≠ b ⇒
       ∃s1 s2. open_in t s1 ∧ open_in t s2 ∧
               a ∈ s1 ∧ b ∉ s1 ∧ b ∈ s2 ∧ a ∉ s2
Proof
 rw[T1_space_def,EQ_IMP_THM] (* 2 *)
 >- (qexistsl_tac
    [‘(topspace t) DIFF {b}’,‘(topspace t) DIFF {a}’] >>
    simp[] >> gs[closed_in]) >>
 simp[closed_in] >>
 ‘∀y. y ≠ x ∧ y ∈ topspace t ⇒ ∃s. open_in t s ∧
  y ∈ s ∧ x ∉ s’
  by metis_tac[] >>
 gs[SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] >>
 rename [‘open_in t (c _)’,‘_ ∈ c _’] >>
 ‘(topspace t DIFF {x}) =
  BIGUNION (IMAGE c (topspace t DIFF {x}))’
  by (simp[Once EXTENSION,PULL_EXISTS] >>
    metis_tac[OPEN_IN_SUBSET,SUBSET_DEF]) >>
 pop_assum SUBST1_TAC >>
 irule OPEN_IN_BIGUNION >> simp[] >> metis_tac[]
QED

Theorem homeomorphism_fun:
    homeomorphism (s,t) (f,g) ⇒
        (∀x. x ∈ topspace s ⇒ f x ∈ topspace t) ∧
        (∀y. y ∈ topspace t ⇒ g y ∈ topspace s)
Proof
    rw[homeomorphism,BIJ_ALT,FUNSET]
QED

Theorem homeomorphism_closed_in:
    homeomorphism (s,t) (f,g) ⇒
        (∀U. closed_in s U ⇒ closed_in t (IMAGE f U)) ∧
        (∀V. closed_in t V ⇒ closed_in s (IMAGE g V))
Proof
    rw[homeomorphism,closed_in]
    >- (‘topspace t = IMAGE f (topspace s)’ by simp[BIJ_IMAGE] >>
        pop_assum SUBST1_TAC >> simp[IMAGE_SUBSET])
    >- (first_x_assum $ dxrule >> qmatch_abbrev_tac ‘_ _ s1 ⇒ _ _ s2’ >>
        ‘s1 = s2’ suffices_by simp[] >> UNABBREV_ALL_TAC >>
        rw[EXTENSION,IN_IMAGE] >> eq_tac >> rw[]
        >- fs[BIJ_ALT,FUNSET]
        >- (fs[BIJ_DEF,INJ_DEF] >> rename [‘f x = f y’] >>
            CCONTR_TAC >> fs[] >> ‘x ∈ topspace s’ by fs[SUBSET_DEF] >>
            qpat_x_assum ‘∀x y. _’ $ dxrule_all_then assume_tac >> fs[])
        >- (qexists_tac ‘g x’ >> simp[] >> fs[BIJ_ALT,FUNSET]))
    >- (‘topspace s = IMAGE g (topspace t)’ by simp[BIJ_IMAGE] >>
        pop_assum SUBST1_TAC >> simp[IMAGE_SUBSET])
    >- (first_x_assum $ dxrule >> qmatch_abbrev_tac ‘_ _ s1 ⇒ _ _ s2’ >>
        ‘s1 = s2’ suffices_by simp[] >> UNABBREV_ALL_TAC >>
        rw[EXTENSION,IN_IMAGE] >> eq_tac >> rw[]
        >- fs[BIJ_ALT,FUNSET]
        >- (fs[BIJ_DEF,INJ_DEF] >> rename [‘g x = g y’] >>
            CCONTR_TAC >> fs[] >> ‘x ∈ topspace t’ by fs[SUBSET_DEF] >>
            qpat_x_assum ‘∀x y. _’ $ dxrule_all_then assume_tac >> fs[])
        >- (qexists_tac ‘f x’ >> simp[] >> fs[BIJ_ALT,FUNSET]))
QED

Theorem exercise_4_2_7ii:
    homeomorphism (s,t) (f,g) ∧ T1_space s ⇒ T1_space t
Proof
    rw[T1_space_def] >>
    ‘g x ∈ topspace s’ by fs[homeomorphism,BIJ_ALT,FUNSET] >>
    first_x_assum $ dxrule_then assume_tac >>
    drule_all $ cj 1 homeomorphism_closed_in >>
    gs[homeomorphism]
QED

Theorem in_open_in_topspace:
    x ∈ U ∧ open_in s U ⇒ x ∈ topspace s
Proof
    rw[topspace] >> qexists_tac ‘U’ >> simp[]
QED

Theorem exercise_4_2_7iii:
    homeomorphism (s,t) (f,g) ∧ T2_space s ⇒ T2_space t
Proof
    rw[T2_space_def] >>
    ‘g a ∈ topspace s ∧ g b ∈ topspace s’ by fs[homeomorphism,BIJ_ALT,FUNSET] >>
    ‘g a ≠ g b’ by (fs[homeomorphism,BIJ_DEF,INJ_DEF] >> CCONTR_TAC >>
        ‘g a = g b’ by fs[] >>
        qpat_x_assum ‘∀x y. _’ $ dxrule_all_then assume_tac >> fs[]) >>
    first_x_assum $ dxrule_all_then assume_tac >> fs[] >>
    qexistsl_tac [‘IMAGE f A’,‘IMAGE f B’] >>
    NTAC 2 $ irule_at Any $ cj 6 $ iffLR homeomorphism >>
    qexistsl_tac [‘s’,‘s’,‘g’,‘g’] >> simp[Excl "IN_IMAGE"] >>
    NTAC 2 (dxrule_then assume_tac IMAGE_IN >>
    pop_assum $ qspec_then ‘f’ mp_tac) >>
    simp[iffLR homeomorphism,SF SFY_ss,Excl "IN_IMAGE"] >>
    NTAC 2 $ DISCH_THEN kall_tac >>
    pop_assum mp_tac >> CONV_TAC CONTRAPOS_CONV >> rw[GSYM MEMBER_NOT_EMPTY] >>
    rename [‘f x = f y’] >> qexists_tac ‘x’ >>
    ‘x = y’ suffices_by simp[] >> fs[homeomorphism,BIJ_DEF,INJ_DEF] >>
    first_x_assum irule >> simp[in_open_in_topspace,SF SFY_ss]
QED

(* second_countable_def *)
Theorem exercise_4_2_7iv:
    homeomorphism (τ₁,τ₂) (f,g) ∧ second_countable τ₁ ⇒ second_countable τ₂
Proof
    rw[second_countable_def] >>
    qexists_tac ‘IMAGE (IMAGE f) B’ >>
    simp[image_countable] >> gs[basis_def,PULL_EXISTS] >>
    conj_tac >- fs[homeomorphism] >> rw[] >>
    ‘open_in τ₁ (IMAGE g s)’ by fs[homeomorphism] >>
    first_x_assum $ dxrule_then strip_assume_tac >>
    qexists_tac ‘IMAGE (IMAGE f) u’ >> simp[IMAGE_SUBSET] >>
    pop_assum (mp_tac o Q.AP_TERM ‘IMAGE f’) >>
    simp[IMAGE_BIGUNION,IMAGE_IMAGE] >>
    DISCH_THEN $ SUBST1_TAC o SYM >> rw[EXTENSION] >>
    gs[homeomorphism,in_open_in_topspace,SF CONJ_ss,SF SFY_ss]
QED

(*
separable_def
dense_def
closure_def
limpt
neigh
*)

Theorem homeomorphism_INJ:
  homeomorphism (τ₁,τ₂) (f,g) ⇒
  (∀a b.
    a ∈ topspace τ₁ ∧ b ∈ topspace τ₁ ⇒
    (f a = f b ⇔ a = b)) ∧
  (∀a b.
    a ∈ topspace τ₂ ∧ b ∈ topspace τ₂ ⇒
    (g a = g b ⇔ a = b))
Proof
  rw[] >> metis_tac[homeomorphism, BIJ_DEF, INJ_DEF]
QED

Theorem homeomorphism_limpt:
  homeomorphism (τ₁,τ₂) (f,g) ∧ limpt τ₁ a A ⇒
  limpt τ₂ (f a) (IMAGE f A)
Proof
  rw[limpt_thm]
  >- (drule homeomorphism_fun >> rw[])
  >> rw[PULL_EXISTS] >>
  `open_in τ₁ (IMAGE g U)` by metis_tac[homeomorphism] >>
  first_x_assum drule >> rw[PULL_EXISTS] >>
  `a = g (f a)` by metis_tac[homeomorphism] >>
  first_x_assum drule >> rw[] >>
  rename1 `g b ≠ g (f a)` >>
  qexists_tac `g b` >> rw[]
  >- metis_tac[OPEN_IN_SUBSET, homeomorphism, SUBSET_DEF]
  >> qpat_x_assum `a = g (_ _)` (ASSUME_TAC o GSYM) >>
  gs[] >>
  `g b ∈ topspace τ₁`
    suffices_by metis_tac[homeomorphism_INJ] >>
  metis_tac[homeomorphism_fun, SUBSET_DEF, OPEN_IN_SUBSET]
QED

Theorem homeomorphism_closure:
  homeomorphism (τ₁,τ₂) (f,g) ∧ A ⊆ topspace τ₁ ⇒
  closure τ₂ (IMAGE f A) = IMAGE f (closure τ₁ A)
Proof
  rw[closure_def, EXTENSION] >> eq_tac >> rw[]
  >- metis_tac[]
  >- (dxrule $ iffLR homeomorphism_SYM >> rw[] >>
      drule homeomorphism_limpt >> rw[] >>
      first_x_assum drule >> rw[] >>
      qexists_tac `g x` >> rw[]
      >- metis_tac[homeomorphism, limpt_thm]
      >> `IMAGE g (IMAGE f A) = A`
            suffices_by metis_tac[] >>
      rw[EXTENSION, PULL_EXISTS] >>
      metis_tac[homeomorphism, SUBSET_DEF])
  >- metis_tac[]
  >> metis_tac[homeomorphism_limpt]
QED

Theorem exercise_4_2_7v:
  homeomorphism (τ₁,τ₂) (f,g) ∧ separable τ₁ ⇒
  separable τ₂
Proof
  rw[separable_def] >>
  qexists_tac `IMAGE f A` >> rw[]
  >- (drule homeomorphism_fun >> rw[] >>
      gs[SUBSET_DEF, PULL_EXISTS])
  >- (fs[dense_def] >>
      drule_all homeomorphism_closure >> rw[] >>
      rw[EXTENSION] >>
      metis_tac[homeomorphism_fun, homeomorphism])
  >> metis_tac[cardinalTheory.COUNTABLE_IMAGE]
QED



val _ = export_theory();

