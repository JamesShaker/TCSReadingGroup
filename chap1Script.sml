open HolKernel Parse boolLib bossLib;
open combinTheory
     listTheory
     mp_then
     nlistTheory
     numpairTheory
     pred_setTheory
     relationTheory
     rich_listTheory;

val _ = new_theory "chap1";

(* a finite automaton is a 5-tuple of
     Q : set of states
     A : alphabet - set of characters
     δ : transition function
          Q × A → Q
     q0 : start state
     C : final states

  Subject to constraints:
     - Q finite,
     - A finite,
     - C ⊆ Q
     - q0 ∈ Q
*)

Type state  = “:num”
Type symbol = “:num”


(* Definition 1.5 *)
Datatype:
  fa = <|
    Q : state set ;
    A : symbol set ;
    tf : state -> (symbol -> state)
          (* or state # symbol -> state,
             encoding Q * A -> Q *) ;
    q0 : state ;
    C : state set
  |>
End

Definition wfFA_def:
  wfFA a ⇔
    FINITE a.Q ∧
    FINITE a.A ∧
    a.C ⊆ a.Q  ∧
    a.q0 ∈ a.Q ∧
    (∀q c.
      c ∈ a.A ∧ q ∈ a.Q ⇒ a.tf q c ∈ a.Q) ∧
    (* if you apply the transition function to a state in
       the machine's state set, and a character in the
       machine's alphabet, then you'd better stay in the
       set of machine states *)
    0 ∈ a.Q ∧
    0 ∉ a.C ∧
    0 ≠ a.q0 ∧
    (∀q c. c ∉ a.A ⇒ (a.tf q c = 0)) ∧
    (∀c. a.tf 0 c = 0)
End

(* Note that the same automaton can be encoded as two different
   fa values because the two values can have tf functions that
   differ on values of q and a outside of the expected domain
*)


(*
                                           /-----------\
                                           v           |
   --> ( 1 )  --a-->  (( 2 ))  --a,b-->  ( 4 )  --a,b -'
         |                                 ^
         b                                 |
         |                                 |
         \- - - - - - - - - - -- - - - - - /
       ( 3 )


*)

Definition example_def:
  example = <| Q := {0;1;2;3;4}; A := { 1 (* a *); 2 (* b *) };
               tf := (λq. case q of
                          |  1 => (λc. if c = 1 then 2 else
                                       if c = 2 then 3 else 0)
                          |  2 => (λc. if (c = 1) \/ (c = 2) then 4
                                       else 0)
                          |  3 => (λc. if (c = 1) \/ (c = 2) then 4
                                       else 0)
                          |  4 => (λc. if (c = 1) \/ (c = 2) then 4
                                       else 0)
                          | _ => \c.0 ) ;
               q0 := 1;
               C := {2} |>
End

(* prove that example is well-formed *)
Theorem example_wellformed:
  wfFA example
Proof
  simp[wfFA_def, example_def]>>
  rpt strip_tac (* generates 8 subgoals *) >>
  simp[] (* 9 *)
  >- rw[] >> rfs[]
QED

Type sipser_string = “:symbol list”
Type language = “:sipser_string set”

Definition runMachine_def[simp]:
  (runMachine a q [] = q)  ∧
  (runMachine a q (c::cs) = runMachine a (a.tf q c) cs)
End

Definition accepts_def:
  accepts a cs ⇔ runMachine a a.q0 cs ∈ a.C
End

Theorem example_acceptsA = EVAL “accepts example [1]”;
Theorem example_doesnt_acceptB = EVAL “accepts example [2]”;
Theorem example_doesnt_acceptAB = EVAL “accepts example [1;2]”;

Definition Sipser_Accepts_def:
  Sipser_Accepts A cs ⇔
    ∃ss : state list.
      ss ≠ [] ∧
      (LENGTH ss = LENGTH cs + 1) ∧
      (HD ss = A.q0) ∧
      (∀n. n < LENGTH ss - 1 ⇒
           (A.tf (EL n ss) (EL n cs) = EL (n + 1) ss)) ∧
      LAST ss ∈ A.C ∧
      wfFA A
End

Theorem Sipser_Accepts_NoZero:
  Sipser_Accepts A cs ⇔
    ∃ss : state list.
      ss ≠ [] ∧
      (∀s. MEM s ss ⇒ s ≠ 0) ∧
      (LENGTH ss = LENGTH cs + 1) ∧
      (HD ss = A.q0) ∧
      (∀n. n < LENGTH ss - 1 ⇒
           (A.tf (EL n ss) (EL n cs) = EL (n + 1) ss)) ∧
      LAST ss ∈ A.C ∧
      wfFA A
Proof
  reverse (rw[EQ_IMP_THM])
  >- metis_tac[Sipser_Accepts_def]
  >- (fs[Sipser_Accepts_def] >>
      qexists_tac ‘ss’ >>
      rw[] >>
      ‘∀ss cs. LAST ss ≠ 0 ∧
               LENGTH ss = LENGTH cs + 1 ∧
               (∀n. n < LENGTH ss - 1 ⇒
                    A.tf (EL n ss) (EL n cs) =
                    EL (n + 1) ss) ⇒
              ¬(MEM 0 ss)’
        suffices_by metis_tac[wfFA_def] >>
      ntac 5 (last_x_assum (K ALL_TAC)) >>
      Induct_on ‘ss’ >> simp[arithmeticTheory.ADD1] >>
      rw[]
      >> (Cases_on ‘ss’ >> fs[] >>
          Cases_on ‘cs’ >> fs[] >>
          rename [‘LAST (s1::st) ≠ 0’,‘EL _ (s0::s1::st)’,
                  ‘LENGTH st = LENGTH ct’,‘EL _ (c0::ct)’] >>
          last_x_assum (qspec_then ‘ct’ assume_tac) >>
          rfs[arithmeticTheory.ADD1] >>
          pop_assum mp_tac >>
          impl_tac
          >- (rw[] >>
              first_x_assum (qspec_then ‘n + 1’ mp_tac) >>
              simp[rich_listTheory.EL_CONS,
                   DECIDE “PRE n = n - 1”])
          >- (strip_tac >> first_x_assum (qspec_then ‘0’ mp_tac) >>
              simp[] >> metis_tac[wfFA_def])))
QED

Theorem sipser_rm:
∀ss input.
   (∀n. n < LENGTH input ⇒
        (A.tf (EL n ss) (EL n input) = EL (n + 1) ss)) ∧
   (LENGTH input + 1 = LENGTH ss)  ⇒
   (runMachine A (HD ss) input = LAST ss)
Proof
  Induct_on ‘input’ >>
  rw[] >>
  Cases_on ‘ss’ >>
  fs[] >>
  simp[listTheory.LAST_DEF] >>
  rw[] >>
  fs[indexedListsTheory.LT_SUC, DISJ_IMP_THM, FORALL_AND_THM,
     PULL_EXISTS, arithmeticTheory.ADD_CLAUSES]
QED

Definition buildstates_def[simp]:
  (buildstates A q [] = [q]) ∧
  (buildstates A q (c::cs) = q :: buildstates A (A.tf q c) cs)
End

Theorem LENGTH_buildstates[simp]:
  ∀q inp. LENGTH (buildstates A q inp) = LENGTH inp + 1
Proof
  Induct_on ‘inp’ >>
  simp[]
QED

Theorem HD_buildstates[simp]:
  HD (buildstates A q inp) = q
Proof
  Cases_on ‘inp’ >>
  simp[]
QED

Theorem buildstates_EQ_NIL[simp]:
  buildstates A q inp ≠ []
Proof
  Cases_on ‘inp’ >>
  simp[]
QED

Theorem LAST_buildstates[simp]:
  ∀q inp. LAST (buildstates A q inp) = runMachine A q inp
Proof
  Induct_on ‘inp’ >>
  simp[runMachine_def] >>
  simp[listTheory.LAST_DEF]
QED

Theorem buildstates_transition:
  ∀n q0 i.
    n < LENGTH i ⇒
    (A.tf (EL n (buildstates A q0 i)) (EL n i) =
     EL (n + 1) (buildstates A q0 i))
Proof
  Induct_on ‘i’ >>
  simp[] >>
  rw[] >>
  Cases_on ‘n’ >>
  fs[] >>
  simp[GSYM arithmeticTheory.ADD1]
QED

Theorem runMachine_0_sticks:
  wfFA A ⇒ runMachine A 0 cs = 0
Proof
  strip_tac >> Induct_on ‘cs’ >> simp[] >>
  fs[wfFA_def]
QED

Theorem wfFA_accepts_characters_ok:
  wfFA A ∧ accepts A cs ∧ MEM c cs ⇒ c ∈ A.A
Proof
  simp[accepts_def] >>
  ‘wfFA A ⇒ ∀q c. q ∈ A.Q ∧ runMachine A q cs ∈ A.C ∧ MEM c cs ⇒ c ∈ A.A’
    suffices_by metis_tac[wfFA_def] >>
  strip_tac >> Induct_on ‘cs’ >> simp[] >> rw[]
  >- (spose_not_then assume_tac >>
      ‘A.tf q c = 0’ by metis_tac[wfFA_def] >> fs[] >>
      rfs[runMachine_0_sticks] >> metis_tac[wfFA_def])
  >- (‘h ∈ A.A’ suffices_by metis_tac[wfFA_def] >>
      spose_not_then assume_tac >>
      ‘A.tf q h = 0’ by metis_tac[wfFA_def] >> fs[] >>
      rfs[runMachine_0_sticks] >> metis_tac[wfFA_def])
QED

Theorem Sipser_Accepts_runMachine_coincide:
  ∀A cs. wfFA A ⇒ (Sipser_Accepts A cs = accepts A cs)
Proof
  simp[FUN_EQ_THM, Sipser_Accepts_def, accepts_def, EQ_IMP_THM,
       PULL_EXISTS] >>
  rw[]
  >- (rfs[] >>
      metis_tac[sipser_rm])
  >- (rename [‘runMachine A _ input’] >>
      qexists_tac ‘buildstates A A.q0 input’ >>
      simp[] >>
      metis_tac[buildstates_transition])
QED

Theorem Sipser_Accepts_runMachine_coincide_thm:
  ∀A cs. Sipser_Accepts A cs ⇔ wfFA A ∧ accepts A cs
Proof
  metis_tac[Sipser_Accepts_runMachine_coincide,Sipser_Accepts_def]
QED

(* Just prior to 1.16 *)
Definition recogLangD_def:
  recogLangD D = {w | Sipser_Accepts D w}
End

(* Definition 1.16 *)
Definition regularLanguage_def:
  regularLanguage l ⇔ ∃M. wfFA M ∧ recogLangD M = l
End

(* Definition 1.23 *)
(* The Regular Operations *)
(* Union is already defined (set union...) *)

Definition concat_def:
  concat lA lB = {x ++ y | x ∈ lA ∧ y ∈ lB}
End


Definition star_def:
  star l = {FLAT ls | ∀s. MEM s ls ⇒ s ∈ l}
End

Theorem empty_in_star:
  ∀ l. [] ∈ star l
Proof
  rw [star_def] >>
  qexists_tac ‘[]’ >>
  rw[]
QED

Definition machine_union_def:
  machine_union M1 M2 =
    <|Q  := {npair r1 r2 | r1 ∈ M1.Q ∧ r2 ∈ M2.Q };
      A  := M1.A ∪ M2.A;
      tf := λs c. npair (M1.tf (nfst s) c)
                        (M2.tf (nsnd s) c);
      q0 := npair M1.q0 M2.q0;
      C  := {npair r1 r2 | (r1 ∈ M1.C ∧ r2 ∈ M2.Q) ∨
                           (r1 ∈ M1.Q ∧ r2 ∈ M2.C)};
    |>
End


(* Theorem 1.25 *)
Theorem wfFA_machine_union :
  ∀M1 M2. wfFA M1 ∧ wfFA M2 ⇒ wfFA (machine_union M1 M2)
Proof
  rw[wfFA_def,machine_union_def] (* 11 *) >> simp[]
  >- (qmatch_abbrev_tac ‘FINITE s’ >>
      ‘s = IMAGE (UNCURRY npair) (M1.Q CROSS M2.Q)’ suffices_by simp[] >>
      simp[Abbr‘s’, EXTENSION, pairTheory.EXISTS_PROD])
  >- (simp[SUBSET_DEF,PULL_EXISTS] >> metis_tac[SUBSET_DEF])
  >- (Cases_on ‘c ∈ M2.A’ >> simp[])
  >- metis_tac[]
QED

Theorem regular_closed_under_union:
  ∀ lA lB. regularLanguage lA ∧
           regularLanguage lB ⇒
           regularLanguage (lA ∪ lB)
Proof
  rw [regularLanguage_def] >>
  rename [‘recogLangD M1 ∪ recogLangD M2’] >>
  qexists_tac ‘machine_union M1 M2’ >>
  rw [recogLangD_def, EXTENSION,
      Sipser_Accepts_runMachine_coincide_thm,
      wfFA_machine_union] >>
  qabbrev_tac ‘MU = machine_union M1 M2’ >>
  rw[accepts_def] >>
  ‘(MU.A = M1.A ∪ M2.A) ∧ (MU.q0 = npair M1.q0 M2.q0)’
    by rw[machine_union_def, Abbr ‘MU’] >>
  simp[] >>
  ‘∀ q1 q2. q1 ∈ M1.Q ∧ q2 ∈ M2.Q
    ⇒ (runMachine MU (q1 ⊗ q2) x ∈ MU.C ⇔
      runMachine M1 q1 x ∈ M1.C ∨ runMachine M2 q2 x ∈ M2.C)’
    suffices_by (rpt strip_tac >>
                 metis_tac[wfFA_def]) >>
  Induct_on ‘x’
  >- (rw[Abbr ‘MU’, runMachine_def,machine_union_def])
  >- (rw[runMachine_def, DISJ_IMP_THM, FORALL_AND_THM] >>
      ‘MU.tf (npair q1 q2) h = npair (M1.tf q1 h) (M2.tf q2 h)’
        by rw[Abbr ‘MU’, machine_union_def] >>
      first_x_assum (fn x => SUBST_TAC [x]) >>
      ‘M1.tf q1 h ∈ M1.Q ∧ M2.tf q2 h ∈ M2.Q’
        suffices_by metis_tac[] >>
      metis_tac[wfFA_def])
QED

Datatype:
  nfa = <|
    Q : state set ;
    A : symbol set ;
    tf : state -> (symbol option -> state set);
    q0 : state ;
    C : state set
  |>
End

Definition wfNFA_def:
  wfNFA a ⇔
    FINITE a.Q ∧
    FINITE a.A ∧
    a.C ⊆ a.Q  ∧
    a.q0 ∈ a.Q ∧
    (∀q c. c ∈ a.A ∧ q ∈ a.Q ⇒ a.tf q (SOME c) ⊆ a.Q) ∧
    (∀q.   q ∈ a.Q ⇒ a.tf q NONE ⊆ a.Q) ∧
    (∀q c. c ∉ a.A ⇒ a.tf q (SOME c) = ∅)
End


Definition strip_option_def[simp]:
  (strip_option [] = []) ∧
  (strip_option (NONE :: t) = strip_option t) ∧
  (strip_option (SOME c :: t) = c :: strip_option t)
End

Theorem strip_MAP_SOME[simp]:
  strip_option (MAP SOME x) = x
Proof
  Induct_on ‘x’ >> simp[]
QED

Definition Sipser_ND_Accepts_def:
  Sipser_ND_Accepts A cs ⇔
    ∃ss : state list cs':(symbol option) list.
      ss ≠ [] ∧
      (strip_option cs' = cs) ∧
      (LENGTH ss = LENGTH cs' + 1) ∧
      (HD ss = A.q0) ∧
      (∀n. n < LENGTH ss - 1 ⇒
           EL (n + 1) ss ∈ A.tf (EL n ss) (EL n cs')) ∧
      LAST ss ∈ A.C ∧
      (∀c. MEM c cs ⇒ c ∈ A.A)
End

Definition recogLangN_def:
  recogLangN N = {w | Sipser_ND_Accepts N w}
End


Definition e_closure_def:
  e_closure a Q = {s | ∃q. q ∈ Q ∧  RTC (λs0 s. s ∈ a.tf s0 NONE) q s}
End

val _ = temp_overload_on ("E",“e_closure”);

val _ = temp_overload_on ("enc", “λs. nlist_of (SET_TO_LIST s)”);
val _ = temp_overload_on ("dec", “λs. set (listOfN s)”);

Theorem dec_enc_iden[simp]:
  ∀s. FINITE s ⇒ dec (enc s) = s
Proof
  rw[listOfN_nlist,SET_TO_LIST_INV]
QED

(*
Theorem enc_inj:
  INJ enc (λx. FINITE x) (𝕌 (: num))
Proof
  ‘INJ (nlist_of o SET_TO_LIST) (λx. FINITE x) (𝕌 (: num))’
    suffices_by rw[o_DEF] >>
  irule INJ_COMPOSE >>
  qexists_tac ‘𝕌 (: num list)’ >>
  rw [INJ_DEF]
QED


Theorem enc_infin:
  ∀s. enc s ≠ nlist_of ARB ⇒ FINITE s
Proof
  rpt strip_tac >>
  fs[SET_TO_LIST_primitive_def] >>
  qabbrev_tac ‘P = (@X. WF X ∧ ∀Y. FINITE Y ∧ Y ≠ ∅ ⇒ X (REST Y) Y)’ >>
  qabbrev_tac ‘M = (λSET_TO_LIST a.
               if FINITE a then
                 if a = ∅ then [] else CHOICE a::SET_TO_LIST (REST a)
               else ARB)’ >>
  fs[]

  CCONTR_TAC >>

  fs[]
  ‘WF R’
    by cheat >>
  Q.ISPECL_THEN [‘R’,‘M’] strip_assume_tac WFREC_THM >>
  rfs[] >>
  first_x_assum (qspec_then ‘s’ assume_tac)
  rw[WFREC_THM]

  ‘SET_TO_LIST s = ARB’
    suffices_by simp[nlist_of_def]
  rw[SET_TO_LIST_primitive_def] >>

QED
*)
Definition NFA2DFA_def:
  NFA2DFA a =
    <|Q  := {enc s| s ⊆ a.Q};
      A  := a.A;
      tf := λs c. enc (E a {s' | ∃s0. s0 ∈ dec s ∧ s' ∈ a.tf s0 (SOME c)});
      q0 := enc (E a {a.q0});
      C := {enc s |s ⊆ a.Q ∧ ∃c. c ∈ s ∧ c ∈ a.C} |>
End


Theorem e_in_states:
  (∀q. q ∈ a.Q ⇒ a.tf q NONE ⊆ a.Q) ⇒
  s ⊆ a.Q ⇒ E a s ⊆ a.Q
Proof
  strip_tac >>
  simp[e_closure_def,PULL_EXISTS,SUBSET_DEF] >>
  ‘∀x0 x. (λs0 s. s ∈ a.tf s0 NONE)^* x0 x ⇒ x0 ∈ a.Q ⇒ x ∈ a.Q’
    suffices_by metis_tac[] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >> rw[] >>
  first_x_assum drule >> simp[SUBSET_DEF]
QED

Theorem nlist_of_11[simp]:
  (nlist_of x = nlist_of y) ⇔ (x = y)
Proof
  metis_tac[listOfN_nlist]
QED

Theorem nlist_of_EQ_0[simp]:
  (nlist_of l = 0 ⇔ l = []) ∧
  (0 = nlist_of l ⇔ l = [])
Proof
  metis_tac[nlist_of_11, nlist_of_def]
QED

Theorem SET_TO_LIST_EQ_NIL[simp]:
  FINITE s ⇒
  (SET_TO_LIST s = [] ⇔ s = ∅) ∧
  ([] = SET_TO_LIST s ⇔ s = ∅)
Proof
  rw[EQ_IMP_THM] >>
  metis_tac[listTheory.SET_TO_LIST_INV, listTheory.LIST_TO_SET_THM]
QED

Theorem enc_EQ_0[simp]:
  FINITE s ⇒ (enc s = 0 ⇔ s = ∅) ∧ (0 = enc s ⇔ s = ∅)
Proof
  simp[]
QED

Theorem wfFA_NFA2DFA:
  wfNFA a ⇒ wfFA (NFA2DFA a)
Proof
  fs[wfNFA_def,wfFA_def,NFA2DFA_def] >> rw[]
  >- (‘{enc s | s ⊆ a.Q} = IMAGE enc (POW a.Q)’ by
        fs[EXTENSION,IN_POW] >> simp[FINITE_POW] )
  >- (rw[SUBSET_DEF,PULL_EXISTS] >> metis_tac[])
  >- (qexists_tac ‘E a {a.q0}’ >>
      simp[e_in_states] )
  >- (qmatch_abbrev_tac ‘∃s. SET_TO_LIST eas = SET_TO_LIST s ∧ s ⊆ a.Q’ >>
      qexists_tac ‘eas’ >> simp[Abbr ‘eas’] >> irule e_in_states >>
      rw[] >> ‘FINITE s’ by metis_tac[SUBSET_FINITE_I] >>
      simp[SUBSET_DEF,PULL_EXISTS,listOfN_nlist] >>
      metis_tac[SUBSET_DEF] )
  >- (qexists_tac ‘∅’ >> simp[])
  >- (Cases_on ‘s ⊆ a.Q’ >> simp[] >>
      ‘FINITE s’ by metis_tac[SUBSET_FINITE] >>
      simp[] >>
      Cases_on ‘s = ∅’ >> simp[])
  >- (‘FINITE (E a {a.q0}) ∧ E a {a.q0} ≠ ∅’ suffices_by simp[] >>
      conj_tac
      >- (‘E a {a.q0} ⊆ a.Q’ suffices_by metis_tac[SUBSET_FINITE] >>
          irule e_in_states >> simp[])
      >- (simp[e_closure_def, EXTENSION] >> qexists_tac ‘a.q0’ >>
          simp[])) >>
  ‘E a ∅ = ∅’ suffices_by simp[] >>
  simp[e_closure_def]
QED

Definition DFA2NFA_def:
  DFA2NFA a = <|Q  := a.Q;
                A  := a.A;
                tf := λs copt. case copt of
                                  NONE => {}
                                | SOME c =>
                                    if a.tf s c = 0 then ∅
                                    else {a.tf s c};
                q0 := a.q0;
                C := a.C |>
End

(* also need: wfNFA (DFA2NFA a) *)
Theorem wfNFA_DFA2NFA:
  ∀D. wfFA D ⇒ wfNFA (DFA2NFA D)
Proof
  rw[wfFA_def,wfNFA_def,DFA2NFA_def] >>
  rw[]
QED

Theorem strip_option_length:
  ¬MEM NONE l ⇒ LENGTH (strip_option l) = LENGTH l
Proof
  Induct_on ‘l’ >> rw[] >> fs[] >> Cases_on ‘h’ >> simp[] >> fs[]
QED

Theorem EL_strip_option:
  ∀n. ¬MEM NONE l ∧ n < LENGTH l ⇒ EL n l = SOME (EL n (strip_option l))
Proof
  Induct_on ‘l’ >> simp[] >> Cases >> simp[] >>
  Cases >> simp[]
QED

Theorem DFA_SUBSET_NFA:
  wfFA a ⇒ (Sipser_ND_Accepts (DFA2NFA a) cs ⇔ Sipser_Accepts a cs)
Proof
  rw[] >> reverse eq_tac
  >- (rw[Sipser_ND_Accepts_def,Sipser_Accepts_NoZero, DFA2NFA_def] >>
      map_every qexists_tac [‘ss’,‘MAP SOME cs’] >> rw[]
      >- (fs[listTheory.EL_MAP] >>
          ‘EL (n + 1) ss ≠ 0’
            suffices_by rw[] >>
          metis_tac[MEM_EL,DECIDE“(n < x) ∧ (y = x + 1) ⇒ (n + 1 < y)”])
      >- (‘Sipser_Accepts a cs’ by metis_tac[Sipser_Accepts_def] >>
          fs[Sipser_Accepts_runMachine_coincide_thm] >>
          metis_tac[wfFA_accepts_characters_ok])) >>
  rw[Sipser_ND_Accepts_def,Sipser_Accepts_NoZero, DFA2NFA_def] >>
  rename [‘LENGTH ss = LENGTH cs + 1’, ‘LAST ss ∈ A.C’] >>
  qexists_tac ‘ss’ >>
  ‘¬MEM NONE cs’ by
     (rw[MEM_EL] >> Cases_on ‘n < LENGTH cs’ >> simp[] >> strip_tac >>
      rename [‘EL n cs’] >> pop_assum (assume_tac o GSYM) >>
      last_x_assum (qspec_then ‘n’ mp_tac) >> simp[]) >>
  reverse (rw[strip_option_length])
  >- (rename [‘n < LENGTH cs’] >> last_x_assum (qspec_then‘n’ mp_tac) >>
      simp[EL_strip_option] >> rw[])
  >- (rw[MEM_EL] >>
      Cases_on ‘n < LENGTH cs + 1’ >>
      simp[] >>
      qpat_x_assum ‘LENGTH ss = _’ (assume_tac o GSYM) >>
      fs[] >> Cases_on ‘n’
      >- fs[EL,wfFA_def] >>
      rename1 ‘0 ≠ EL (SUC n) ss’ >>
      last_x_assum (qspec_then ‘n’ mp_tac) >>
      simp[] >> Cases_on ‘EL n cs’ >> simp[] >>
      rw[arithmeticTheory.ADD1])
QED

Theorem MEM_listOfN_enc[simp]:
  FINITE s ⇒ (MEM x (listOfN (enc s)) ⇔ x ∈ s)
Proof
  simp[listOfN_nlist]
QED

Theorem e_closure_safe:
  wfNFA a ∧ s0 ⊆ a.Q ⇒ E a s0 ⊆ a.Q
Proof
  strip_tac >> simp[e_closure_def, SUBSET_DEF, PULL_EXISTS] >>
  ‘∀s0 s. (λq0 q. q ∈ a.tf q0 NONE)^* s0 s ⇒ (s0 ∈ a.Q ⇒ s ∈ a.Q)’
    suffices_by metis_tac[SUBSET_DEF] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >> simp[] >> rw[] >>
  fs[wfNFA_def] >> metis_tac[SUBSET_DEF]
QED

Theorem IN_eclosure_originator:
  x ∈ E a s ⇒ ∃x0. x0 ∈ s ∧ (λs0 s. s ∈ a.tf s0 NONE)^* x0 x
Proof
  simp[e_closure_def]
QED

Theorem IN_eclosure_originator_rev:
  (∃x0. x0 ∈ s ∧ (λs0 s. s ∈ a.tf s0 NONE)^* x0 x) ⇒ x ∈ E a s
Proof
  simp[e_closure_def]
QED

Theorem nlist_of_11[simp]:
  (nlist_of l1 = nlist_of l2) ⇔ (l1 = l2)
Proof
  qid_spec_tac ‘l2’ >> Induct_on ‘l1’ >> simp[] >>
  Cases_on ‘l2’ >> simp[]
QED

Theorem SET_TO_LIST_11[simp]:
  ∀s1 s2. FINITE s1 ∧ FINITE s2 ⇒ (SET_TO_LIST s1 = SET_TO_LIST s2 ⇔ s1 = s2)
Proof
  metis_tac[listTheory.SET_TO_LIST_INV]
QED

Theorem enc_11[simp]:
  FINITE s1 ∧ FINITE s2 ⇒ ((enc s1 = enc s2) ⇔ (s1 = s2))
Proof
  simp[]
QED

Theorem NFA2DFA_1step:
  wfNFA a ∧ s0 ⊆ a.Q ∧ c ∈ a.A ⇒
  (((NFA2DFA a).tf (enc s0) c = q) ⇔
   ∃s. (q = enc s) ∧ s ⊆ a.Q ∧
      ∀nq. nq ∈ s ⇔
           ∃nq0. nq0 ∈ s0 ∧ nq ∈ E a (a.tf nq0 (SOME c)))
Proof
  simp[NFA2DFA_def] >> strip_tac >> eq_tac >> rw[]
  >- (qho_match_abbrev_tac ‘∃s. enc X = enc s ∧ _ s’ >> qexists_tac ‘X’ >>
      simp[] >> rw[Abbr‘X’]
      >- (‘FINITE s0’ by metis_tac[wfNFA_def, SUBSET_FINITE_I] >> simp[] >>
          irule e_closure_safe >> simp[SUBSET_DEF, PULL_EXISTS] >>
          fs[wfNFA_def] >> metis_tac[SUBSET_DEF]) >>
      ‘FINITE s0’ by metis_tac[wfNFA_def, SUBSET_FINITE_I] >> fs[] >>
      fs[e_closure_def, PULL_EXISTS] >> metis_tac[]) >>
  ‘FINITE s0’ by metis_tac[wfNFA_def, SUBSET_FINITE_I] >> simp[] >>
  AP_TERM_TAC >> fs[e_closure_def, EXTENSION, PULL_EXISTS] >>
  metis_tac[]
QED

Inductive NF_transition:
  (∀q0. NF_transition a q0 [] q0) ∧
  (∀q0 q1 q c cs.
     q1 ∈ a.tf q0 c ∧ NF_transition a q1 cs q ∧ (∀c0. c = SOME c0 ⇒ c0 ∈ a.A)
    ⇒
     NF_transition a q0 (c::cs) q)
End

Theorem E_FINITE:
  wfNFA N ∧ s ⊆ N.Q ⇒ FINITE (E N s)
Proof
  rw[] >> drule_all (GEN_ALL e_closure_safe) >> strip_tac >>
  irule SUBSET_FINITE_I >> qexists_tac ‘N.Q’ >> fs[wfNFA_def]
QED

Theorem Sipser_ND_Accepts_NF_transition:
  Sipser_ND_Accepts a cs ⇔
  ∃q n nlist.
     LENGTH nlist = LENGTH cs ∧
     NF_transition a a.q0
       (REPLICATE n NONE ++
        FLAT (MAP (λ(c,n). SOME c :: REPLICATE n NONE) (ZIP (cs,nlist))))
     q ∧ q ∈ a.C
Proof
  simp[Sipser_ND_Accepts_def] >> qspec_tac(‘a.q0’, ‘s0’) >> rw[] >>
  eq_tac >> rw[]
  >- (rpt (pop_assum mp_tac) >> map_every qid_spec_tac [‘ss’, ‘s0’] >>
      Induct_on ‘cs'’ >> simp[]
      >- (Cases >> simp[] >> rw[] >>
          map_every qexists_tac [‘h’, ‘0’] >>
          simp[NF_transition_rules]) >>
      rw[] >> Cases_on ‘ss’ >> fs[] >>
      ‘t ≠ []’ by (strip_tac >> fs[]) >>
      ‘LENGTH t = LENGTH cs' + 1’ by fs[arithmeticTheory.ADD1] >>
      fs[indexedListsTheory.LT_SUC, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS,
         arithmeticTheory.ADD_CLAUSES] >>
      ‘∀x. LAST (x :: t) = LAST t’ by simp[listTheory.LAST_CONS_cond] >> fs[] >>
      rename [‘HD ss ∈ A.tf s0 copt’] >> Cases_on ‘copt’ >> fs[]>>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac ‘q’
      >- (map_every qexists_tac [‘SUC n’ , ‘nlist’] >> simp[] >>
          metis_tac[NF_transition_rules,optionTheory.NOT_NONE_SOME]) >>
      map_every qexists_tac [‘0’, ‘n::nlist’] >> simp[] >>
      metis_tac[NF_transition_rules,optionTheory.SOME_11]) >>
  rpt (pop_assum mp_tac) >>
  qho_match_abbrev_tac ‘P ⇒ Q ⇒ R q cs s0’ >>
  ‘∀q0 csoptl q.
      NF_transition a q0 csoptl q ⇒
      ∀cs n nlist.
        LENGTH nlist = LENGTH cs ∧
        csoptl =
          REPLICATE n NONE ++
          FLAT (MAP (λ(c,n). SOME c :: REPLICATE n NONE) (ZIP(cs,nlist))) ⇒
        R q cs q0’ suffices_by metis_tac[] >>
   simp[Abbr‘R’] >> markerLib.UNABBREV_ALL_TAC >>
   Induct_on ‘NF_transition’ >> simp[] >> rw[]
   >- (fs[rich_listTheory.REPLICATE_NIL, listTheory.FLAT_EQ_NIL] >>
       fs[listTheory.EVERY_MEM, listTheory.MEM_MAP, PULL_EXISTS,
          pairTheory.FORALL_PROD] >>
       rename [‘ZIP(cs,nlist)’] >>
       ‘cs = []’
         by (Cases_on ‘cs’ >> fs[] >> Cases_on ‘nlist’ >> fs[] >>
             metis_tac[]) >>
       map_every qexists_tac [‘[q0]’,‘[]’] >> simp[]) >>
   rename[‘q1 ∈ a.tf a0 copt’,‘LENGTH nlist = LENGTH cs’,‘REPLICATE n’,
          ‘NF_transition a q1 csoptl q’] >>
   Cases_on ‘copt’
   >- ((* nfa made an ε transition *)
       ‘∃m. n = SUC m’
         by (Cases_on ‘n’ >> fs[] >>
             map_every Cases_on [‘cs’, ‘nlist’] >> fs[]) >>
       fs[] >> first_x_assum (drule_then (qspec_then ‘m’ mp_tac)) >>
       simp[] >> strip_tac >>
       rename [‘strip_option IHcs = cs’, ‘HD IHss = q1’] >>
       map_every qexists_tac [‘a0 :: IHss’, ‘NONE :: IHcs’] >>
       simp[listTheory.LAST_CONS_cond] >> qx_gen_tac ‘N’ >> strip_tac >>
       Cases_on ‘N’ >> simp[] >> rename [‘SUC N0 < LENGTH IHcs + 1’] >>
       simp[arithmeticTheory.ADD_CLAUSES]) >>
   (* copt = SOME ?; nfa made a "real" transition *)
   rename [‘SOME c:: _ = _’] >> ‘n = 0’ by (Cases_on ‘n’ >> fs[]) >>
   fs[] >>
   qabbrev_tac
    ‘build =
       λn (cs:num list) (ns:num list).
         REPLICATE n NONE ++
         FLAT (MAP (λ(c,n). SOME c :: REPLICATE n NONE) (ZIP(cs,ns)))’ >>
   fs[] >>
   Cases_on ‘cs’ >> fs[] >- (rw[] >> fs[]) >>
   rename [‘ZIP (c1::cs,_)’] >>
   Cases_on ‘nlist’ >> fs[] >> rw[] >>
   rename [‘NF_transition a q1 (build n cs ns) q’] >>
   first_x_assum (drule_then (qspec_then ‘n’ mp_tac)) >> simp[] >>
   strip_tac >> rename [‘strip_option IHcs = cs’, ‘IHss ≠ []’] >>
   map_every qexists_tac [‘a0::IHss’, ‘SOME c :: IHcs’] >>
   simp[listTheory.LAST_CONS_cond] >> rw[]

   >- (rename [‘N<LENGTH _ + 1’] >>
       Cases_on ‘N’ >> simp[] >> rename [‘SUC N0 < LENGTH IHcs + 1’] >>
       simp[arithmeticTheory.ADD_CLAUSES])
   >- (fs[])
   >- (metis_tac[])
QED

Theorem E_SUBSET:
  x ∈ Q ⇒ x ∈ E a Q
Proof
  simp[e_closure_def] >> metis_tac[relationTheory.RTC_RULES]
QED

Theorem E_IDEMPOTENT[simp]:
  E a (E a Q) = E a Q
Proof
  simp[e_closure_def, EXTENSION, PULL_EXISTS] >>
  metis_tac[relationTheory.RTC_CASES_RTC_TWICE]
QED


Theorem NF_transition_NFA2DFA:
  wfNFA a ⇒
  ∀q0 cs q.
     NF_transition a q0 cs q ⇒
     (∀c. MEM (SOME c) cs ⇒ c ∈ a.A) ⇒
     ∀Q0.
       q0 ∈ Q0 ∧ Q0 ⊆ a.Q ⇒
       ∃Q. enc Q = runMachine (NFA2DFA a) (enc (E a Q0)) (strip_option cs) ∧
           q ∈ Q ∧ Q ⊆ a.Q
Proof
  strip_tac >>
  Induct_on ‘NF_transition’ >> rw[] >- metis_tac[E_SUBSET,e_closure_safe] >>
  rename [‘q1 ∈ a.tf q0 copt’] >> Cases_on ‘copt’ >> simp[]
  >- (fs[] >> first_x_assum (qspec_then ‘E a Q0’ mp_tac) >> simp[] >>
      disch_then irule >> conj_tac
      >- (simp[e_closure_def] >> qexists_tac ‘q0’ >>
          simp[relationTheory.RTC_SINGLE]) >>
      simp[e_closure_safe]) >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >> rename [‘q1 ∈ a.tf q0 (SOME c)’] >>
  ‘∃Q1. q1 ∈ Q1 ∧ Q1 ⊆ a.Q ∧ (NFA2DFA a).tf (enc (E a Q0)) c = enc (E a Q1)’
     suffices_by metis_tac[] >>
  simp[NFA2DFA_def] >>
  qexists_tac ‘{q | ∃q0'. q0' ∈ E a Q0 ∧ q ∈ a.tf q0' (SOME c)}’ >> simp[]>>
  rpt conj_tac
  >- metis_tac[E_SUBSET]
  >- (fs[wfNFA_def, SUBSET_DEF, PULL_EXISTS] >>
      metis_tac[e_closure_safe, SUBSET_DEF, wfNFA_def]) >>
  AP_TERM_TAC >> simp[EXTENSION] >>
  ‘FINITE (E a Q0)’
    by metis_tac[wfNFA_def, e_closure_safe, SUBSET_FINITE_I] >>
  simp[MEM_listOfN_enc]
QED

Theorem MEM_REPLICATE_CORR[simp]:
  MEM x (REPLICATE n y) ⇔ 0 < n ∧ x = y
Proof
  Induct_on ‘n’ >> fs[] >> metis_tac[]
QED

Theorem strip_option_append[simp]:
  strip_option (a++b) = strip_option a ++ strip_option b
Proof
  Induct_on ‘a’ >> fs[] >> Cases >> simp[]
QED

Theorem strip_option_replicate_none[simp]:
  strip_option (REPLICATE n NONE) = []
Proof
  Induct_on ‘n’ >> simp[]
QED

Theorem strip_option_flat:
  strip_option (FLAT l) = FLAT (MAP strip_option l)
Proof
  Induct_on ‘l’ >> simp[]
QED

Theorem fst_list_lem:
  (λ(c,n). [c]) = (λx. [x]) o FST
Proof
  simp[FUN_EQ_THM,pairTheory.FORALL_PROD]
QED

Theorem flat_map_sing[simp]:
  FLAT (MAP (λx. [x]) l) = l
Proof
  Induct_on‘l’ >> simp[]
QED

Theorem NFA2DFA_q0:
  (NFA2DFA a).q0 = enc (E a {a.q0})
Proof
  simp[NFA2DFA_def]
QED

Theorem NFA2DFA_C:
  (NFA2DFA a).C = {enc s | s ⊆ a.Q ∧ ∃c. c ∈ s ∧ c ∈ a.C}
Proof
  simp[NFA2DFA_def]
QED

Theorem nf_transition_okay:
  ∀q0 copts q. NF_transition a q0 copts q ⇒ ∀c. MEM (SOME c) copts ⇒ c ∈ a.A
Proof
  Induct_on‘NF_transition’ >> simp[] >> metis_tac[optionTheory.SOME_11]
QED

Theorem RTC_LIST:
  ∀x y. RTC R x y ⇒
        ∃l. l ≠ [] ∧ HD l = x ∧ LAST l = y ∧
            ∀i. i < LENGTH l - 1 ⇒ R (EL i l) (EL (i + 1) l)
Proof
  Induct_on ‘RTC’ >> rw[]
  >- (rename [‘HD _ = a’] >> qexists_tac ‘[a]’ >> simp[]) >>
  rename [‘R a (HD l0)’] >> qexists_tac ‘a::l0’ >> simp[] >>
  conj_tac >- (Cases_on ‘l0’ >> fs[])>>
  Cases >> simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem E_closure_NF_transition:
  ∀q0 q. q ∈ E N {q0} ⇒ ∃n. NF_transition N q0 (REPLICATE n NONE) q
Proof
  rw[] >> drule IN_eclosure_originator >> simp[] >> Induct_on ‘RTC’ >> rw[]
  >- (qexists_tac ‘0’ >> simp[NF_transition_rules]) >>
  rename [‘NF_transition N _ (REPLICATE m NONE) _’] >>
  qexists_tac ‘SUC m’ >>
  simp[] >> metis_tac[NF_transition_rules, TypeBase.distinct_of “:α option”]
QED

val _ = overload_on("munge", “λn cs nlist. REPLICATE n NONE ++ FLAT (MAP (λ(c,n). SOME c :: REPLICATE n NONE) (ZIP (cs,nlist)))”)

Theorem NF_transition_prepend_NONEs:
  ∀n0 n cs nlist.
    NF_transition N q0 (REPLICATE n0 NONE) q1 ∧
    NF_transition N q1 (munge n cs nlist) q2 ⇒
    NF_transition N q0 (munge (n0 + n) cs nlist) q2
Proof
  Induct_on ‘NF_transition’ >> rw[rich_listTheory.REPLICATE_NIL] >>
  rename [‘REPLICATE n0 NONE = none1::nones’] >>
  Cases_on ‘n0’ >> fs[] >> rw[] >>
  rename [‘REPLICATE _ NONE = REPLICATE nn NONE’] >>
  first_x_assum (qspec_then ‘nn’ mp_tac) >> simp[] >>
  disch_then (drule_then assume_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  metis_tac[NF_transition_rules, TypeBase.distinct_of “:α option”]
QED

Theorem NFA_SUBSET_DFA:
  wfNFA N ⇒ (Sipser_Accepts (NFA2DFA N) cs ⇔ Sipser_ND_Accepts N cs)
Proof
  strip_tac >> reverse eq_tac
  >- (rw[Sipser_ND_Accepts_NF_transition, Sipser_Accepts_runMachine_coincide,
         accepts_def,wfFA_NFA2DFA] >>
      drule_then (drule_then strip_assume_tac) NF_transition_NFA2DFA >>
      rfs[MEM_FLAT,PULL_EXISTS,MEM_MAP,MEM_ZIP,strip_option_flat,MAP_MAP_o,
          pairTheory.o_UNCURRY_R,
          combinTheory.o_ABS_R,fst_list_lem,MAP_ZIP,NFA2DFA_C,NFA2DFA_q0] >>
      qabbrev_tac‘
        s = REPLICATE n NONE ⧺
            FLAT (MAP (λ(c,n). SOME c::REPLICATE n NONE) (ZIP (cs,nlist)))
      ’ >>
      ‘∀c. MEM (SOME c) s ⇒ c ∈ N.A’ by metis_tac[nf_transition_okay] >>
      ‘(∀n'. n' < LENGTH cs ⇒ EL n' cs ∈ N.A)’
        by (rw[] >>
            ‘MEM (SOME (EL n' cs)) s’
              by (fs[Abbr‘s’] >>
                  ‘MEM (EL n' cs) cs’ by fs[rich_listTheory.EL_MEM] >>
                  fs[MEM_FLAT] >>
                  qexists_tac
                    ‘(SOME (EL n' cs))::(REPLICATE (EL n' nlist) NONE)’ >>
                  fs[MEM_MAP] >>
                  qexists_tac‘(EL n' cs,EL n' nlist)’ >> fs[MEM_ZIP] >>
                  metis_tac[]) >>
            fs[]) >> fs[] >>
      ‘N.q0 ∈ {N.q0} ∧ {N.q0} ⊆ N.Q’ suffices_by metis_tac[] >> fs[wfNFA_def])>>
  rw[Sipser_Accepts_runMachine_coincide, Sipser_ND_Accepts_NF_transition,
     wfFA_NFA2DFA, accepts_def] >>
  pop_assum mp_tac >>
  ‘∀s. s ⊆ N.Q ∧
       runMachine (NFA2DFA N) (enc s) cs ∈ (NFA2DFA N).C ⇒
       ∃nq0 nq n nlist.
           LENGTH nlist = LENGTH cs ∧ nq0 ∈ s ∧
           NF_transition N nq0 (REPLICATE n NONE ++
                                FLAT (MAP (λ(c,n). SOME c :: REPLICATE n NONE)
                                          (ZIP (cs, nlist))))
                           nq ∧ nq ∈ N.C’
     suffices_by (rpt strip_tac >>
                  first_x_assum (qspec_then ‘E N {N.q0}’ mp_tac) >>
                  impl_tac
                  >- (‘{N.q0} ⊆ N.Q’ by fs[wfNFA_def] >> simp[e_closure_safe] >>
                      ‘enc (E N {N.q0}) = (NFA2DFA N).q0’ suffices_by simp[] >>
                      simp[NFA2DFA_def]) >>
                  rw[] >>
                  drule_then(qx_choose_then ‘n0’ assume_tac)
                     E_closure_NF_transition >>
                  drule_all NF_transition_prepend_NONEs >> metis_tac[]) >>
  Induct_on ‘cs’ >> simp[]
  >- (simp[NFA2DFA_def, PULL_EXISTS] >> rw[] >>
      rename [‘SET_TO_LIST s1 = SET_TO_LIST s2’] >>
      ‘FINITE s1 ∧ FINITE s2’ by metis_tac[wfNFA_def, SUBSET_FINITE] >>
      fs[SET_TO_LIST_11] >> rw[] >>
      map_every qexists_tac [‘c’, ‘c’, ‘0’] >> simp[NF_transition_rules]) >>
  rw[] >> rename [‘(NFA2DFA N).tf (enc s) c0’] >>
  ‘FINITE s’ by metis_tac[wfNFA_def, SUBSET_FINITE] >>
  ‘∃s'. (NFA2DFA N).tf (enc s) c0 = enc s' ∧ s' ⊆ N.Q’
    by (simp[NFA2DFA_def] >>
        qmatch_abbrev_tac
          ‘∃s'. SET_TO_LIST (E N ss) = SET_TO_LIST s' ∧ s' ⊆ N.Q’ >>
        ‘ss ⊆ N.Q’ suffices_by metis_tac[e_closure_safe] >>
        simp[Abbr‘ss’, SUBSET_DEF, PULL_EXISTS] >>
        fs[wfNFA_def] >> Cases_on ‘c0 ∈ N.A’ >- metis_tac[SUBSET_DEF] >>
        first_assum (pop_assum o mp_then Any mp_tac) >> simp[]) >>
  fs[] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qpat_x_assum ‘_.tf (enc s) _ = _’ mp_tac >>
  simp[NFA2DFA_def] >>
  ‘FINITE s'’ by metis_tac[wfNFA_def, SUBSET_FINITE] >>
  qmatch_abbrev_tac ‘SET_TO_LIST ss = SET_TO_LIST _ ⇒ _’ >>
  ‘FINITE ss’
    by (simp[Abbr‘ss’] >> irule E_FINITE >> simp[] >>
        simp[SUBSET_DEF, PULL_EXISTS] >> fs[wfNFA_def] >>
        Cases_on ‘c0 ∈ N.A’ >- metis_tac[SUBSET_DEF] >>
        first_assum (pop_assum o mp_then Any mp_tac) >> simp[]) >>
  simp[SET_TO_LIST_11] >> simp[Abbr‘ss’] >> rw[] >>
  drule IN_eclosure_originator >> simp[PULL_EXISTS] >> rw[] >>
  rename [‘nq1 ∈ N.tf nq0 (SOME c0)’, ‘nq0 ∈ s’, ‘RTC _ nq1 nq2’] >>
  qexists_tac ‘nq0’ >> qexists_tac ‘nq’ >> qexists_tac ‘0’ >>
  ‘nq2 ∈ E N {nq1}’
    by (irule IN_eclosure_originator_rev >>
        simp[]) >>
  drule_then (qx_choose_then ‘nn’ assume_tac) E_closure_NF_transition >>
  qexists_tac ‘(nn+n)::nlist’ >> simp[] >>
  irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >> simp[] >>
  reverse conj_tac
  >- metis_tac[NF_transition_prepend_NONEs,arithmeticTheory.ADD_COMM] >>
  CCONTR_TAC >>
  ‘N.tf nq0 (SOME c0) = ∅’
    suffices_by metis_tac[NOT_IN_EMPTY] >>
  fs[wfNFA_def]
QED

Theorem thm_1_39:
  (∃D. wfFA D ∧ recogLangD D = l) ⇔ (∃N. wfNFA N ∧ recogLangN N = l)
Proof
  rw[] >> eq_tac >> rw[recogLangD_def,recogLangN_def]
  >- (simp[EXTENSION] >> qexists_tac ‘DFA2NFA D’ >>
      metis_tac[DFA_SUBSET_NFA,wfNFA_DFA2NFA])
  >- (simp[EXTENSION] >> qexists_tac ‘NFA2DFA N’ >>
      metis_tac[NFA_SUBSET_DFA,wfFA_NFA2DFA])
QED

Theorem regularLanguage_NFA_thm:
  ∀L.
    regularLanguage L ⇔ ∃M. wfNFA M ∧ recogLangN M = L
Proof
  metis_tac[regularLanguage_def,thm_1_39]
QED

Definition machine_link_def:
  machine_link N1 N2 =
    <|Q  := {npair 0 r1 | r1 ∈ N1.Q} ∪
            {npair 1 r2 | r2 ∈ N2.Q};
      A  := N1.A ∪ N2.A;
      tf := λs copt.
              if nfst s = 0 then
                let
                  frs = {npair 0 s' | s' ∈ N1.tf (nsnd s) copt}
                in
                  if nsnd s ∈ N1.C ∧ copt = NONE then
                    frs ∪ {npair 1 N2.q0}
                  else
                    frs
              else
                {npair 1 s' | s' ∈ N2.tf (nsnd s) copt};
      q0 := npair 0 N1.q0;
      C  := {npair 1 r2 | r2 ∈ N2.C };
    |>
End

Theorem machine_link_q0[simp]:
  (machine_link N1 N2).q0 = 0 ⊗ N1.q0
Proof
  simp[machine_link_def]
QED

Theorem wfNFA_machine_link:
  ∀N1 N2.
    wfNFA N1 ∧ wfNFA N2 ⇒
    wfNFA (machine_link N1 N2)
Proof
  rw[wfNFA_def,machine_link_def]
  >- (qmatch_abbrev_tac ‘FINITE s’ >>
      ‘s = IMAGE (npair 0) N1.Q’
        suffices_by metis_tac[IMAGE_FINITE] >>
      simp[EXTENSION,Abbr ‘s’])
  >- (qmatch_abbrev_tac ‘FINITE s’ >>
      ‘s = IMAGE (npair 1) N2.Q’
        suffices_by metis_tac[IMAGE_FINITE] >>
      simp[EXTENSION,Abbr ‘s’]) >>
  simp[SUBSET_DEF,PULL_EXISTS] >> rw[] >>
  metis_tac[SUBSET_DEF,NOT_IN_EMPTY]
QED

Theorem machine_link_tf0:
  (machine_link N1 N2).tf (0 ⊗ n1) c =
   if n1 ∈ N1.C ∧ c = NONE then
      {0 ⊗ n | n ∈ N1.tf n1 NONE} ∪ {1 ⊗ N2.q0}
    else {0 ⊗ n | n ∈ N1.tf n1 c}
Proof
  simp[machine_link_def]
QED

Theorem machine_link_A:
  (machine_link N1 N2).A = N1.A ∪ N2.A
Proof
  simp[machine_link_def]
QED

Theorem machine_link_C[simp]:
  (machine_link N1 N2).C = { 1 ⊗ n | n ∈ N2.C }
Proof
  simp[machine_link_def]
QED

Theorem NF_transition_link2_E:
  ∀q1 n. NF_transition (machine_link N1 N2) (1 ⊗ q1) ts n ⇒
         ∃q2. n = 1 ⊗ q2
Proof
  Induct_on ‘NF_transition’ >> simp[] >> rw[] >> first_x_assum irule >>
  qpat_x_assum ‘_ ∈ _.tf _ _’ mp_tac >> simp[machine_link_def] >>
  simp[PULL_EXISTS]
QED

Theorem NF_transition_link21_impossible[simp]:
  ¬NF_transition (machine_link N1 N2) (1 ⊗ q1) ts (0 ⊗ q2)
Proof
  strip_tac >> drule NF_transition_link2_E >> simp[]
QED

Theorem NF_transition_machine_link1[simp]:
  wfNFA N1 ⇒
  (NF_transition (machine_link N1 N2) (0 ⊗ q1) ts (0 ⊗ q2) ⇔
   NF_transition N1 q1 ts q2)
Proof
  strip_tac >> eq_tac
  >- (map_every qid_spec_tac [‘q1’, ‘q2’] >> Induct_on ‘NF_transition’ >>
      rw[] >> fs[NF_transition_rules] >>
      qpat_x_assum ‘_ ∈ _.tf _ _’ mp_tac >>
      rw[machine_link_def] >> fs[] >>
      irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >>
      fs[machine_link_A] >> fs[wfNFA_def] >>
      metis_tac[NF_transition_rules, NOT_IN_EMPTY]) >>
  Induct_on ‘NF_transition’ >> simp[NF_transition_rules] >> rw[] >>
  irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >>
  simp[machine_link_A] >> goal_assum (first_assum o mp_then Any mp_tac) >>
  simp[machine_link_def] >>
  asm_simp_tac (srw_ss() ++ boolSimps.COND_elim_ss)[] >> metis_tac[]
QED

Theorem NF_transition_machine_link2[simp]:
  wfNFA N2 ⇒
  (NF_transition (machine_link N1 N2) (1 ⊗ q1) ts (1 ⊗ q2) ⇔
   NF_transition N2 q1 ts q2)
Proof
  strip_tac >> eq_tac
  >- (map_every qid_spec_tac [‘q1’, ‘q2’] >> Induct_on ‘NF_transition’ >>
      rw[] >> fs[NF_transition_rules] >>
      qpat_x_assum ‘_ ∈ _.tf _ _’ mp_tac >>
      rw[machine_link_def] >> fs[] >>
      irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >>
      fs[machine_link_A] >> fs[wfNFA_def] >>
      metis_tac[NF_transition_rules, NOT_IN_EMPTY]) >>
  Induct_on ‘NF_transition’ >> simp[NF_transition_rules] >> rw[] >>
  irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >>
  simp[machine_link_A] >> goal_assum (first_assum o mp_then Any mp_tac) >>
  simp[machine_link_def]
QED


Theorem NF_transition_machine_link_shift12:
  wfNFA N1 ∧ wfNFA N2 ∧
  NF_transition (machine_link N1 N2) q0 ts q ∧
  q0 ∈ { 0 ⊗ n1 | n1 ∈ N1.Q } ∧ q ∈ { 1 ⊗ n2 | n2 ∈ N2.Q }
⇒
  ∃q1 ts1 ts2.
    q1 ∈ N1.C ∧ (* q2 = 1 ⊗ N2.q0 *)
    NF_transition N1 (nsnd q0) ts1 q1 ∧
    NF_transition N2 N2.q0 ts2 (nsnd q) ∧
    ts = ts1 ++ [NONE] ++ ts2
Proof
  Induct_on ‘NF_transition’ >> rw[]
  >- (qspec_then ‘q0’ strip_assume_tac npair_cases >> simp[] >>
      rename [‘q0 = m ⊗ n’] >> Cases_on ‘m = 0’ >> simp[]) >>
  fs[PULL_EXISTS] >>
  rename [‘NF_transition _ q1 ts (1 ⊗ n2)’] >>
  qpat_x_assum ‘_ ∈ _.tf _ _’ mp_tac >>
  rw[machine_link_def] >> fs[]
  >- (rename [‘n1' ∈ N1.tf n1 _’] >>
      ‘n1' ∈ N1.Q’ by metis_tac[wfNFA_def, SUBSET_DEF] >>
      fs[] >>
      rename [‘ts = ts1 ++ [NONE] ++ ts2’, ‘NF_transition N1 n1' ts1 q1’,
              ‘NF_transition N2 N2.q0 ts2 n2’] >>
      ‘NF_transition N1 n1 (NONE::ts1) q1’
         by metis_tac[NF_transition_rules, optionTheory.NOT_SOME_NONE] >>
      map_every qexists_tac [‘q1’, ‘NONE::ts1’, ‘ts2’] >> simp[])
  >- (goal_assum drule >> qexists_tac ‘[]’ >> simp[NF_transition_rules])
  >- (rename [‘n1' ∈ N1.tf n1 _’] >>
      ‘n1' ∈ N1.Q’ by metis_tac[wfNFA_def, SUBSET_DEF, NOT_IN_EMPTY,
                                optionTheory.option_CASES] >> fs[] >>
      goal_assum (first_assum o mp_then (Pos (el 3)) mp_tac) >>
      rename [‘ts = ts1 ++ [NONE] ++ ts2’, ‘NF_transition N1 n1' ts1 q1’,
              ‘NF_transition N2 N2.q0 ts2 n2’] >>
      ‘NF_transition N1 n1 (c::ts1) q1’
         by (irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >>
             reverse conj_tac >- metis_tac[] >> fs[machine_link_A] >>
             metis_tac[wfNFA_def, NOT_IN_EMPTY]) >>
      metis_tac[APPEND])
  >- (rename [‘n1' ∈ N1.tf n1 _’] >>
      ‘n1' ∈ N1.Q’ by metis_tac[wfNFA_def, SUBSET_DEF, NOT_IN_EMPTY,
                                optionTheory.option_CASES] >> fs[] >>
      goal_assum (first_assum o mp_then (Pos (el 3)) mp_tac) >>
      rename [‘ts = ts1 ++ [NONE] ++ ts2’, ‘NF_transition N1 n1' ts1 q1’,
              ‘NF_transition N2 N2.q0 ts2 n2’] >>
      ‘NF_transition N1 n1 (c::ts1) q1’
         by (irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >>
             reverse conj_tac >- metis_tac[] >> fs[machine_link_A] >>
             metis_tac[wfNFA_def, NOT_IN_EMPTY]) >>
      metis_tac[APPEND])
QED


Theorem munge_exists:
!ts. ?n x nlist.
  ts = munge n x nlist /\ LENGTH x = LENGTH nlist
Proof
Induct_on `ts` >> simp[REPLICATE_NIL,FLAT_EQ_NIL,EVERY_MAP] (* 2 *)
>- (map_every qexists_tac [`[]`,`[]`] >> simp[]) >>
strip_tac >> fs[] >> Cases_on `h` (* 2 *)
>- (map_every qexists_tac [`SUC n`,`x`,`nlist`] >> simp[]) >>
rename [‘SOME c :: munge n cs nlist’] >> 
map_every qexists_tac [`0`,`c :: cs`,`n:: nlist`] >>
simp[]
QED

Theorem strip_option_munge:
!s ns. LENGTH s = LENGTH ns ==> 
    strip_option (FLAT (MAP (λ(c,n). SOME c::REPLICATE n NONE) (ZIP (s,ns)))) = s
Proof
Induct_on `s` >> simp[] >>
rw[] >> Cases_on `ns` >> fs[]
QED

Theorem NF_transition_concat:
  NF_transition m q0 ts1 q1 ∧ NF_transition m q1 ts2 q2 
==> 
  NF_transition m q0 (ts1 ++ ts2) q2
Proof 
  Induct_on `NF_transition` >> rw[] >> fs[] >> 
  metis_tac[NF_transition_rules]
QED

Theorem munge_middle_none:
∀ x1 nlist1 x2 nlist2. 
LENGTH nlist1 = LENGTH x1 ∧ LENGTH nlist2 = LENGTH x2 
==> 
munge n1 x1 nlist1 ⧺ NONE::munge n2 x2 nlist2 = 
  if x1 = [] then munge (n1+n2+1) x2 nlist2
    else munge n1 (x1 ⧺ x2) (FRONT nlist1 ++ (LAST nlist1+1+n2::nlist2))
Proof 
  ho_match_mp_tac SNOC_INDUCT >> rw[Excl"APPEND_ASSOC"] 
  >- (Induct_on `n1` >> rw[GSYM arithmeticTheory.ADD1] >> rw[arithmeticTheory.ADD_CLAUSES])
  >> cheat
QED 

(* UP TO HERE *)
Theorem thm_1_47:
  ∀L1 L2.
    regularLanguage L1 ∧ regularLanguage L2 ⇒
    regularLanguage (concat L1 L2)
Proof
  rw[regularLanguage_NFA_thm] >>
  rename1 ‘recogLangN _ = concat (_ N1) (_ N2)’ >>
  qexists_tac ‘machine_link N1 N2’ >>
  rw[wfNFA_machine_link,EXTENSION,concat_def, recogLangN_def,
     Sipser_ND_Accepts_NF_transition, EQ_IMP_THM]
  >- (rename [‘LENGTH epslist = LENGTH s’,
              ‘NF_transition (machine_link N1 N2) _ (munge eps0 _ _)’] >>
      drule_then (drule_then drule) NF_transition_machine_link_shift12 >>
      simp[] >> impl_tac >- metis_tac[wfNFA_def, SUBSET_DEF] >>
      strip_tac >> 
      rename [‘munge _ _ _ = ts1 ⧺ [NONE] ⧺ ts2’,
              ‘NF_transition _ _ _ (1 *, n)’] >>
      simp[PULL_EXISTS] >> 
      qspec_then `ts1` (qx_choosel_then [`n1`,`s1`,`nlist1`] strip_assume_tac) munge_exists >>
      qspec_then `ts2` (qx_choosel_then [`n2`,`s2`,`nlist2`] strip_assume_tac) munge_exists >> rw[] >>
      goal_assum (first_assum o mp_then (Pos (el 3)) mp_tac) >>
      simp[] >> 
      goal_assum (first_assum o mp_then (Pos (el 3)) mp_tac) >> 
      simp[] >>
      first_x_assum (mp_tac o AP_TERM ``strip_option: num option list -> num list``) >>
      simp[strip_option_munge]) 
  >>  simp[PULL_EXISTS]
  >>  rename [`machine_link N1 N2`, `NF_transition N1 _ (munge n1 x1 nlist1) q1`,
  `NF_transition N2 _ (munge n2 x2 nlist2) q2`]
  >>  `NF_transition (machine_link N1 N2) (0 ⊗ N1.q0) (munge n1 x1 nlist1) (0 ⊗ q1)` 
    by simp[]
  >>  `NF_transition (machine_link N1 N2) (1 ⊗ N2.q0) (munge n2 x2 nlist2) (1 ⊗ q2)` 
    by simp[]
  >>  `NF_transition (machine_link N1 N2) (0 ⊗ q1) (NONE::munge n2 x2 nlist2) (1 ⊗ q2)` 
    by (irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >> simp[] >> qexists_tac `1 ⊗ N2.q0`
          >> simp[] >> simp[machine_link_def])
  >>  drule_all NF_transition_concat >> 
 cheat
QED

val _ = export_theory();
