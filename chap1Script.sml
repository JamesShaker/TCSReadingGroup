open HolKernel Parse boolLib bossLib;

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
    ∀q c.
      c ∈ a.A ∧ q ∈ a.Q ⇒ a.tf q c ∈ a.Q
    (* if you apply the transition function to a state in
       the machine's state set, and a character in the
       machine's alphabet, then you'd better stay in the
       set of machine states *)
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
  example = <| Q := {1;2;3;4}; A := { 1 (* a *); 2 (* b *) };
               tf := (λq. case q of
                          |  1 => (λc. if c = 1 then 2 else
                                       if c = 2 then 3 else ARB)
                          |  2 => (λc. 4)
                          |  3 => (λc. 4)
                          |  4 => (λc. 4)) ;
               q0 := 1;
               C := {2} |>
’;

(* prove that example is well-formed *)
Theorem example_wellformed:
  wfFA example
Proof
  simp[wfFA_def, example_def]>>
  rpt strip_tac (* generates 8 subgoals *) >>
  simp[]
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
      LAST ss ∈ A.C
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

Theorem Sipser_Accepts_runMachine_coincide:
  Sipser_Accepts = accepts
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

(* Just prior to 1.16 *)
val recogLang_def = Define‘
  recogLang M = {w | accepts M w}
’;

(* Definition 1.16 *)
val regularLanguage_def = Define‘
  regularLanguage l ⇔ ∃M. recogLang M = l
’;

(* Definition 1.23 *)
(* The Regular Operations *)
open pred_setTheory;
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

open numpairTheory;

val machine_union_def = Define‘
  machine_union M1 M2 =
    <|Q  := {npair r1 r2 | r1 ∈ M1.Q ∧ r2 ∈ M2.Q };
      A  := M1.A ∪ M2.A;
      tf := λs c. npair (M1.tf (nfst s) c)
                        (M2.tf (nsnd s) c);
      q0 := npair M1.q0 M2.q0;
      C  := {npair r1 r2 | r1 ∈ M1.C ∨ r2 ∈ M2.C };
    |>
’;

(* Theorem 1.25 *)
Theorem regular_closed_under_union:
  ∀ lA lB. regularLanguage lA ∧
           regularLanguage lB ⇒
           regularLanguage (lA ∪ lB)
Proof
  rw [regularLanguage_def] >>
  rename [‘recogLang M1 ∪ recogLang M2’] >>
  qexists_tac ‘machine_union M1 M2’ >>
  rw [recogLang_def, EXTENSION, accepts_def] >>
  qabbrev_tac ‘MU = machine_union M1 M2’ >>
  ‘∀ q1 q2. runMachine MU (npair q1 q2) x ∈ MU.C
            ⇔ runMachine M1 q1 x ∈ M1.C ∨
              runMachine M2 q2 x ∈ M2.C’
    suffices_by (‘MU.q0 = npair M1.q0 M2.q0’
                    suffices_by rw[] >>
                  rw[Abbr ‘MU’, machine_union_def]) >>
  Induct_on ‘x’
  >- rw[Abbr ‘MU’, runMachine_def,machine_union_def]
  >- (rw[runMachine_def] >>
      ‘MU.tf (npair q1 q2) h = npair (M1.tf q1 h) (M2.tf q2 h)’
        suffices_by simp[] >>
      rw[Abbr ‘MU’, machine_union_def])
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
    (∀q.   q ∈ a.Q ⇒ a.tf q NONE ⊆ a.Q)
’;


val strip_option_def = Define‘
  (strip_option [] = []) /\
  (strip_option (NONE :: t) = strip_option t) /\
  (strip_option (SOME c :: t) = c :: strip_option t)
’;

val Sipser_ND_Accepts_def = Define‘
  Sipser_ND_Accepts A cs ⇔
    ∃ss : state list cs':(symbol option) list.
      ss ≠ [] ∧
      (strip_option cs' = cs) ∧
      (LENGTH ss = LENGTH cs' + 1) ∧
      (HD ss = A.q0) ∧
      (∀n. n < LENGTH ss - 1 ⇒
           EL (n + 1) ss ∈ A.tf (EL n ss) (EL n cs')) ∧
      LAST ss ∈ A.C
’;

val e_closure_def = Define‘
  e_closure a Q = {s | ∃q. q ∈ Q ∧  RTC (λs0 s. s ∈ a.tf s0 NONE) q s}
’;

val _ = temp_overload_on ("E",“e_closure”);

open nlistTheory;
val _ = temp_overload_on ("enc", “λs. nlist_of (SET_TO_LIST s)”);
val _ = temp_overload_on ("dec", “λs. set (listOfN s)”);

val NFA2DFA_def = Define‘
  NFA2DFA a =
    <|Q  := {enc s| s ⊆ a.Q};
      A  := a.A;
      tf := λs c. enc (E a {s' | ∃s0. s0 ∈ dec s ∧ s' ∈ a.tf s0 (SOME c)});
      q0 := enc (E a {a.q0});
      C := {enc s |s ⊆ a.Q ∧ ∃c. c ∈ s ∧ c ∈ a.C} |>
’;

val _ = export_theory();
