open HolKernel Parse boolLib bossLib;
open pred_setTheory;
open numpairTheory;
open nlistTheory;
open listTheory;

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

val _ = type_abbrev("state", “:num”);
val _ = type_abbrev("symbol", “:num”);


(* Definition 1.5 *)
val _ = Datatype‘
  fa = <|
    Q : state set ;
    A : symbol set ;
    tf : state -> (symbol -> state)
          (* or state # symbol -> state,
             encoding Q * A -> Q *) ;
    q0 : state ;
    C : state set
  |>
’;

val wfFA_def = Define‘
  wfFA a ⇔
    FINITE a.Q ∧
    FINITE a.A ∧
    a.C ⊆ a.Q  ∧
    a.q0 ∈ a.Q ∧
    (∀q c.
      c ∈ a.A ∧ q ∈ a.Q ⇒ a.tf q c ∈ a.Q) /\
    (* if you apply the transition function to a state in
       the machine's state set, and a character in the
       machine's alphabet, then you'd better stay in the
       set of machine states *)
    0 ∈ a.Q /\
    0 ∉ a.C /\
    0 ≠ a.q0 /\
    (∀q c. c ∉ a.A ⇒ (a.tf q c = 0)) ∧
    (∀c. a.tf 0 c = 0)
’;

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

val example_def = Define‘
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
’;

(* prove that example is well-formed *)
Theorem example_wellformed:
  wfFA example
Proof
  simp[wfFA_def, example_def]>>
  rpt strip_tac (* generates 8 subgoals *) >>
  simp[] (* 9 *)
  >- rw[] >> rfs[]
QED

val _ = type_abbrev("sipser_string", “:symbol list”);
val _ = type_abbrev("language", “:sipser_string set”);

val runMachine_def = Define‘
  (runMachine a q [] = q)  ∧
  (runMachine a q (c::cs) = runMachine a (a.tf q c) cs)
’;

val _ = export_rewrites ["runMachine_def"];

val accepts_def = Define‘
  accepts a cs ⇔ runMachine a a.q0 cs ∈ a.C
’;

Theorem example_acceptsA = EVAL “accepts example [1]”;
Theorem example_doesnt_acceptB = EVAL “accepts example [2]”;
Theorem example_doesnt_acceptAB = EVAL “accepts example [1;2]”;

val Sipser_Accepts_def = Define‘
  Sipser_Accepts A cs ⇔
    ∃ss : state list.
      ss ≠ [] ∧
      (LENGTH ss = LENGTH cs + 1) ∧
      (HD ss = A.q0) ∧
      (∀n. n < LENGTH ss - 1 ⇒
           (A.tf (EL n ss) (EL n cs) = EL (n + 1) ss)) ∧
      LAST ss ∈ A.C ∧
      wfFA A
’;

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

val buildstates_def = Define‘
  (buildstates A q [] = [q]) ∧
  (buildstates A q (c::cs) = q :: buildstates A (A.tf q c) cs)
’;

val _ = export_rewrites ["buildstates_def"];

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
val recogLang_def = Define‘
  recogLang M = {w | Sipser_Accepts M w}
’;

(* Definition 1.16 *)
val regularLanguage_def = Define‘
  regularLanguage l ⇔ ∃M. wfFA M /\ (recogLang M = l)
’;

(* Definition 1.23 *)
(* The Regular Operations *)
(* Union is already defined (set union...) *)

val concat_def = Define‘
  concat lA lB = {x ++ y | x ∈ lA ∧ y ∈ lB}
’;


val star_def = Define ‘
  star l = {FLAT ls | ∀s. MEM s ls ⇒ s ∈ l}
’;

Theorem empty_in_star:
  ∀ l. [] ∈ star l
Proof
  rw [star_def] >>
  qexists_tac ‘[]’ >>
  rw[]
QED

val machine_union_def = Define‘
  machine_union M1 M2 =
    <|Q  := {npair r1 r2 | r1 ∈ M1.Q ∧ r2 ∈ M2.Q };
      A  := M1.A ∪ M2.A;
      tf := λs c. npair (M1.tf (nfst s) c)
                        (M2.tf (nsnd s) c);
      q0 := npair M1.q0 M2.q0;
      C  := {npair r1 r2 | (r1 ∈ M1.C /\ r2 ∈ M2.Q) \/
                           (r1 ∈ M1.Q /\ r2 ∈ M2.C)};
    |>
’;


(* Theorem 1.25 *)
Theorem wfFA_machine_union :
  !M1 M2. wfFA M1 /\ wfFA M2 ==> wfFA (machine_union M1 M2)
Proof
  rw[wfFA_def,machine_union_def] (* 11 *) >> simp[]
  >- (qmatch_abbrev_tac ‘FINITE s’ >>
      ‘s = IMAGE (UNCURRY npair) (M1.Q CROSS M2.Q)’ suffices_by simp[] >>
      simp[Abbr‘s’, EXTENSION, pairTheory.EXISTS_PROD])
  >- (simp[SUBSET_DEF,PULL_EXISTS] >> metis_tac[SUBSET_DEF])
  >- (Cases_on `c IN M2.A` >> simp[])
  >- metis_tac[]
QED

Theorem regular_closed_under_union:
  ∀ lA lB. regularLanguage lA ∧
           regularLanguage lB ⇒
           regularLanguage (lA ∪ lB)
Proof
  rw [regularLanguage_def] >>
  rename [‘recogLang M1 ∪ recogLang M2’] >>
  qexists_tac ‘machine_union M1 M2’ >>
  rw [recogLang_def, EXTENSION,
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

val _ = Datatype‘
  nfa = <|
    Q : state set ;
    A : symbol set ;
    tf : state -> (symbol option -> state set);
    q0 : state ;
    C : state set
  |>
’;

val wfNFA_def = Define‘
  wfNFA a ⇔
    FINITE a.Q ∧
    FINITE a.A ∧
    a.C ⊆ a.Q  ∧
    a.q0 ∈ a.Q ∧
    (∀q c. c ∈ a.A ∧ q ∈ a.Q ⇒ a.tf q (SOME c) ⊆ a.Q) ∧
    (∀q.   q ∈ a.Q ⇒ a.tf q NONE ⊆ a.Q) ∧
    (∀q c. c ∉ a.A ⇒ a.tf q (SOME c) = ∅)
’;


Definition strip_option_def[simp]:
  (strip_option [] = []) /\
  (strip_option (NONE :: t) = strip_option t) /\
  (strip_option (SOME c :: t) = c :: strip_option t)
End

Theorem strip_MAP_SOME[simp]:
  strip_option (MAP SOME x) = x
Proof
  Induct_on`x` >> simp[]
QED

val Sipser_ND_Accepts_def = Define‘
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
’;

val e_closure_def = Define‘
  e_closure a Q = {s | ∃q. q ∈ Q ∧  RTC (λs0 s. s ∈ a.tf s0 NONE) q s}
’;

val _ = temp_overload_on ("E",“e_closure”);

val _ = temp_overload_on ("enc", “λs. nlist_of (SET_TO_LIST s)”);
val _ = temp_overload_on ("dec", “λs. set (listOfN s)”);
open combinTheory;
open relationTheory;

(*Theorem enc_inj:
  INJ enc (λx. FINITE x) (𝕌 (: num))
Proof
  ‘INJ (nlist_of o SET_TO_LIST) (λx. FINITE x) (𝕌 (: num))’
    suffices_by rw[o_DEF] >>
  irule INJ_COMPOSE >>
  qexists_tac ‘𝕌 (: num list)’ >>
  rw [INJ_DEF]
QED

Theorem dec_enc_iden:
  ∀s. FINITE s ⇒ dec (enc s) = s
Proof
  rw[listOfN_nlist,SET_TO_LIST_INV]
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
val NFA2DFA_def = Define‘
  NFA2DFA a =
    <|Q  := {enc s| s SUBSET a.Q};
      A  := a.A;
      tf := λs c. enc (E a {s' | ∃s0. s0 ∈ dec s ∧ s' ∈ a.tf s0 (SOME c)});
      q0 := enc (E a {a.q0});
      C := {enc s |s ⊆ a.Q ∧ ∃c. c ∈ s ∧ c ∈ a.C} |>
’;


Theorem e_in_states:
  (∀q. q ∈ a.Q ⇒ a.tf q NONE ⊆ a.Q) ==>
  s SUBSET a.Q ==> E a s SUBSET a.Q
Proof
  strip_tac >>
  simp[e_closure_def,PULL_EXISTS,SUBSET_DEF] >>
  `∀x0 x. (λs0 s. s ∈ a.tf s0 NONE)^* x0 x ⇒ x0∈a.Q ⇒ x ∈ a.Q`
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

Theorem wf_NFA2DFA:
  wfNFA a ==> wfFA (NFA2DFA a)
Proof
  fs[wfNFA_def,wfFA_def,NFA2DFA_def] >> rw[]
  >- (`{enc s | s ⊆ a.Q} = IMAGE enc (POW a.Q)` by
        fs[EXTENSION,IN_POW] >> simp[FINITE_POW] )
  >- (rw[SUBSET_DEF,PULL_EXISTS] >> metis_tac[])
  >- (qexists_tac`E a {a.q0}` >>
      simp[e_in_states] )
  >- (qmatch_abbrev_tac`
        ∃s. SET_TO_LIST eas = SET_TO_LIST s ∧ s SUBSET a.Q
      ` >>
      qexists_tac`eas` >> simp[Abbr`eas`] >> irule e_in_states >>
      rw[] >> `FINITE s` by metis_tac[SUBSET_FINITE_I] >>
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
                tf := λs copt. case copt of NONE => {}
                                          | SOME c => {a.tf s c};
                q0 := a.q0;
                C := a.C |>
End

Theorem strip_option_length:
  ¬MEM NONE l ==> LENGTH (strip_option l) = LENGTH l
Proof
  Induct_on`l` >> rw[] >> fs[] >> Cases_on ‘h’ >> simp[] >> fs[]
QED

Theorem EL_strip_option:
  ∀n. ¬MEM NONE l ∧ n < LENGTH l ⇒ EL n l = SOME (EL n (strip_option l))
Proof
  Induct_on ‘l’ >> simp[] >> Cases >> simp[] >>
  Cases >> simp[]
QED

Theorem DFA_SUBSET_NFA:
  wfFA a ==> (Sipser_ND_Accepts (DFA2NFA a) cs <=> Sipser_Accepts a cs)
Proof
  rw[] >> reverse eq_tac
  >- (rw[Sipser_ND_Accepts_def,Sipser_Accepts_def, DFA2NFA_def] >>
      map_every qexists_tac [`ss`,`MAP SOME cs`] >> rw[]
      >- fs[listTheory.EL_MAP]
      >- (‘Sipser_Accepts a cs’ by metis_tac[Sipser_Accepts_def] >>
          fs[Sipser_Accepts_runMachine_coincide_thm] >>
          metis_tac[wfFA_accepts_characters_ok])) >>
  rw[Sipser_ND_Accepts_def,Sipser_Accepts_def, DFA2NFA_def] >>
  rename [‘LENGTH ss = LENGTH cs + 1’, ‘LAST ss ∈ A.C’] >>
  qexists_tac`ss` >>
  ‘¬MEM NONE cs’ by
     (rw[MEM_EL] >> Cases_on ‘n < LENGTH cs’ >> simp[] >> strip_tac >>
      rename [‘EL n cs’] >> pop_assum (assume_tac o GSYM) >>
      last_x_assum (qspec_then ‘n’ mp_tac) >> simp[]) >>
  rw[strip_option_length] >>
  rename [‘n < LENGTH cs’] >> last_x_assum (qspec_then‘n’ mp_tac) >>
  simp[EL_strip_option]
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

val (NF_transition_rules, NF_transition_ind, NF_transition_cases) = Hol_reln‘
  (∀q0. NF_transition a q0 [] q0) ∧
  (∀q0 q1 q c cs.
     q1 ∈ a.tf q0 c ∧ NF_transition a q1 cs q ∧ (∀c0. c = SOME c0 ==> c0 ∈ a.A)
    ⇒
     NF_transition a q0 (c::cs) q)
’;

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
  >- (rpt (pop_assum mp_tac) >> map_every qid_spec_tac [`ss`, `s0`] >>
      Induct_on `cs'` >> simp[]
      >- (Cases >> simp[] >> rw[] >>
          map_every qexists_tac [‘h’, ‘0’] >>
          simp[NF_transition_rules]) >>
      rw[] >> Cases_on ‘ss’ >> fs[] >>
      ‘t ≠ []’ by (strip_tac >> fs[]) >>
      ‘LENGTH t = LENGTH cs' + 1’ by fs[arithmeticTheory.ADD1] >>
      fs[indexedListsTheory.LT_SUC, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS,
         arithmeticTheory.ADD_CLAUSES] >>
      ‘∀x. LAST (x :: t) = LAST t’ by simp[listTheory.LAST_CONS_cond] >> fs[] >>
      rename [‘HD ss ∈ A.tf s0 copt’] >> Cases_on`copt` >> fs[]>>
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
  MEM x (REPLICATE n y) <=> 0<n ∧ x=y
Proof
  Induct_on`n` >> fs[] >> metis_tac[]
QED

Theorem strip_option_append[simp]:
  strip_option (a++b) = (strip_option a) ++ strip_option b
Proof
  Induct_on`a` >> fs[] >> Cases >> simp[]
QED

Theorem strip_option_replicate_none[simp]:
  strip_option (REPLICATE n NONE) = []
Proof
  Induct_on`n` >> simp[]
QED

Theorem strip_option_flat:
  strip_option (FLAT l) = FLAT (MAP strip_option l)
Proof
  Induct_on`l` >> simp[]
QED

Theorem fst_list_lem:
  (λ(c,n). [c]) = (λx. [x]) o FST
Proof
  simp[FUN_EQ_THM,pairTheory.FORALL_PROD]
QED

Theorem flat_map_sing[simp]:
  FLAT (MAP (λx. [x]) l) = l
Proof
  Induct_on`l` >> simp[]
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

Theorem nf_trasition_okay:
  ∀q0 copts q. NF_transition a q0 copts q ==> ∀c. MEM (SOME c) copts ==> c ∈ a.A
Proof
  Induct_on`NF_transition` >> simp[] >> metis_tac[optionTheory.SOME_11]
QED

(* Up to here *)
Theorem NFA_SUBSET_DFA:
  wfNFA N ⇒ (Sipser_Accepts (NFA2DFA N) cs ⇔ Sipser_ND_Accepts N cs)
Proof
  strip_tac >> reverse eq_tac
  >- (rw[Sipser_ND_Accepts_NF_transition, Sipser_Accepts_runMachine_coincide,accepts_def,wf_NFA2DFA] >>
      drule_then (drule_then strip_assume_tac) NF_transition_NFA2DFA >>
      rfs[MEM_FLAT,PULL_EXISTS,MEM_MAP,MEM_ZIP,strip_option_flat,MAP_MAP_o,pairTheory.o_UNCURRY_R,
          combinTheory.o_ABS_R,fst_list_lem,MAP_ZIP,NFA2DFA_C,NFA2DFA_q0] >>
      qabbrev_tac`
        s= (REPLICATE n NONE ⧺
            FLAT (MAP (λ(c,n). SOME c::REPLICATE n NONE) (ZIP (cs,nlist))))
      ` >>
      `∀c. MEM (SOME c) s ==> c ∈ N.A` by metis_tac[nf_trasition_okay] >>
      `(∀n'. n' < LENGTH cs ⇒ EL n' cs ∈ N.A)` by (rw[] >>
        `MEM (SOME (EL n' cs)) s` by
        (fs[Abbr`s`] >> `MEM (EL n' cs) cs` by fs[rich_listTheory.EL_MEM] >>
           fs[MEM_FLAT] >> qexists_tac`(SOME (EL n' cs))::(REPLICATE (EL n' nlist) NONE)` >> fs[MEM_MAP] >>
           qexists_tac`(EL n' cs,EL n' nlist)` >> fs[MEM_ZIP] >>metis_tac[] ) >>
        fs[]  ) >> fs[] >>
      `N.q0 ∈ {N.q0} ∧ {N.q0} ⊆ N.Q` suffices_by metis_tac[] >> fs[wfNFA_def]) >>
  rw[Sipser_Accepts_def, Sipser_ND_Accepts_def] >> (* use NFA2DFA_1step *)
  cheat
QED

(* also need: wfNFA (DFA2NFA a) *)


Theorem chap1_final:
  {l | ∃M. wfFA M ∧ (recogLang M = l) } =
  {l | ∃N. wfNFA N ∧ ({w | Sipser_ND_Accepts N w} = l)}
Proof
  fs[Once EXTENSION] >> rw[] >> eq_tac >> rw[recogLang_def]
  >- (simp[EXTENSION] >> cheat )
  >- cheat
QED


val _ = export_theory();
