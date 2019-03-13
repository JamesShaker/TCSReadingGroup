open HolKernel Parse boolLib bossLib;

val _ = new_theory "chap1";

(* a finite automaton is a 5-tuple of
     Q : set of states
     A : alphabet (* set of characters *)
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

val _ = type_abbrev("state", ``:num``);
val _ = type_abbrev("symbol", ``:num``);


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

val wfFA_def = Define`
  wfFA a <=>
    FINITE a.Q ∧ (* or /\ *)
    FINITE a.A ∧
    a.C ⊆ a.Q ∧ (* or SUBSET *)
    a.q0 ∈ a.Q (* or IN *) ∧


    ∀ (* ! *) q c.
      c ∈ a.A ∧ q ∈ a.Q ⇒ (* ==> *) a.tf q c ∈ a.Q
    (* if you apply the transition function to a state in
       the machine's state set, and a character in the
       machine's alphabet, then you'd better stay in the
       set of machine states *)
`;

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

val example_def = Define`
  example = <| Q := {1;2;3;4}; A := { 1 (* a *); 2 (* b *) };
               tf := (λq. case q of
                          |  1 => (λc. if c = 1 then 2 else
                                       if c = 2 then 3 else ARB)
                          |  2 => (λc. 4)
                          |  3 => (λc. 4)
                          |  4 => (λc. 4)) ;
               q0 := 1;
               C := {2} |>
`;

(* prove that example is well-formed *)
Theorem example_wellformed:
  wfFA example
Proof
  simp[wfFA_def, example_def]>>
  rpt strip_tac (* generates 8 subgoals *) >>
  simp[]
QED

val _ = type_abbrev("sipser_string", ``:symbol list``);
val _ = type_abbrev("language", ``:sipser_string set``);

val runMachine_def = Define`
  (runMachine a q [] = q)  ∧
  (runMachine a q (c::cs) = runMachine a (a.tf q c) cs)
`;

val accepts_def = Define`
  accepts a cs <=> runMachine a a.q0 cs ∈ a.C
`;

Theorem example_acceptsA = EVAL ``accepts example [1]``
Theorem example_doesnt_acceptB = EVAL ``accepts example [2]``
Theorem example_doesnt_acceptAB = EVAL ``accepts example [1;2]``

val Sipser_Accepts_def = Define`
  Sipser_Accepts A cs ⇔
    ∃ss : state list.
      ss ≠ (* <> *) [] ∧
      (HD ss = A.q0) ∧
      (∀n. n < LENGTH ss - 1 ⇒
           (A.tf (EL n ss) (EL n cs) = EL (n + 1) ss)) ∧
      LAST ss ∈ A.C
`;

(* store_thm *)
Theorem Sipser_Accepts_A:
  Sipser_Accepts example [1]
Proof
  ...
QED


val _ = export_theory();
