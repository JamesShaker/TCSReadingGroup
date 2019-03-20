Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat fintype finset.
Require Lists.List.
Require Lists.ListSet.

Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.

Module First.

  Import List.
  Import ListNotations.
  
  Section Verification.
    (* State is finite type. I am wondering if writing 
       Variable S : finType would make it more prettier *)
    Variable S : Type.
    Variable All_s : list S.
    Hypothesis Hsfin : forall (s : S), In s All_s.
    Hypothesis Hsdec : forall (c d : S), {c = d} + {c <> d}.
    
    (* Alphabet is finite type. *)
    Variable A : Type.
    Variable All_a : list A.
    Hypothesis Hafin : forall (a : A), In a All_a.
    Hypothesis Hadec : forall (c d : A), {c = d} + {c <> d}.
    
    (* It seems good idea to represent set as a function *)
    (* Definition from Sipser. The underlying data structure of set is 
       list *)
    (*
    Record Automata :=
      {
        Qs : ListSet.set S;
        Al : ListSet.set A;
        Tf : S -> A -> S;
        q : S;
        Hq : ListSet.set_In q Qs;
        Fs : ListSet.set S;
        Hf : forall x, ListSet.set_In x Fs -> ListSet.set_In x Qs
      }. *)

    Record Automata :=
      {
        Qs : pred S;
        Al : pred A;
        Tf : S -> A -> S;
        q : S;
        Hq : Qs q = true;
        Fs : pred S;
        Hf : forall x, Fs x = true  -> Qs x = true
      }. 

    (* word is list of alphabets *)
    Definition word := list A.

    (* machine m runs on word w with starting state s*)
    Fixpoint  run_machine (m : Automata) (s : S) (w : word) :=
      match w with
      | [] => s
      | h :: t => run_machine m (Tf m s h) t
      end.
    

    Definition fold_machine (m : Automata) (s : S) (w : word) :=
      fold_left (fun x y => Tf m x y) w s.
    
    
   (* Both definition are same. The advantage of fold_left is 
      getting support from library *)
    Lemma run_machine_Equi_fold_machine :
      forall (w : word) (s : S) (m : Automata),
        run_machine m s w = fold_machine m s w.
    Proof.
      unfold run_machine, fold_machine.
      refine (fix Fn w :=
                match w with
                | [] => _
                | h :: t => _
                end).
      + cbn; auto.
      + cbn in *.
        intros s m. rewrite Fn.
        auto.
    Qed.
    
    
    (* machine m accpet a word if it ends up final state *)
    (* This would work with set version of state 
    Definition machine_accpet (m : Automata) (w : word) :=
      let s := fold_machine m (q m) w in
      (* we need decidable equality on states *)
      match in_dec Hsdec s (Fs m) with
      | left _ => true
      | right _ => false
      end. *)

    Definition machine_accept (m : Automata) (w : word) :=
      Fs m (fold_machine m (q m) w).
    
    
    (* sipser accept. A machine m accetps word w if there exists
       sequence of states such that first element is starting state, 
       last element is in final state *)
    (* The reason I defined it this way because it captures 
       the automata which has just one state and it's accepting state *)
    (*
    Definition sipser_accept (m : Automata) (w : word) :=
      existsT (r : list S), r = (q m) :: seq.scanl (Tf m) (q m) w /\
                            In (seq.last (q m) (seq.scanl (Tf m) (q m) w))
                               (Fs m). *)
    
    Definition sipser_accept (m : Automata) (w : word) :=
      existsT (r : list S),
      r = (q m) :: seq.scanl (Tf m) (q m) w /\
       (Fs m) (seq.last (q m) (seq.scanl (Tf m) (q m) w)) = true.
    
     
     (*
       In (fold_machine m (q m) w) (Fs m)
       ============================
       In (seq.last (q m) (seq.scanl (Tf m) (q m) w)) (Fs m) *)
    (*  
    Lemma sipser_accept_more_general :
      forall w s m fs, In (fold_machine m s w) fs <->
                  In (seq.last s (seq.scanl (Tf m) s w)) fs.
    Proof.
      induction w.
      + firstorder.
      + cbn. intros s m fs.
        split; intro Hs; apply IHw; auto.
    Qed. *)

    Lemma sipser_accept_more_general :
      forall w s m, Fs m (fold_machine m s w) = true <->
               Fs m (seq.last s (seq.scanl (Tf m) s w)) = true.
    Proof.
      induction w.
      + firstorder.
      + cbn. intros s m. 
        split; intro Hs; apply IHw; auto.
    Qed.
   
   
    (* 
    Lemma machine_accept_Eqv_sipser_accept :
      forall (w : word) (m : Automata),
        machine_accpet m w = true -> sipser_accept m w.
    Proof.
      unfold machine_accpet, sipser_accept.  
      intros w m.  
      refine (match in_dec
                      Hsdec
                      (fold_machine m (q m) w) (Fs m) with
              | left _ => fun H => _
              | right _ => fun H => _
              end);
        swap 1 2; try (inversion H); clear H. (* get rid of false assumption *)
      exists ((q m) :: seq.scanl (Tf m) (q m) w).
      split; auto.
      (* I need a more generalized version of assumption i *)
      apply sipser_accept_more_general. auto.
    Qed. *)

    Lemma machine_accept_Eqv_sipser_accept :
      forall (w : word) (m : Automata),
        machine_accept m w = true -> sipser_accept m w.
    Proof.
      unfold machine_accept, sipser_accept.
      intros w m H.
      exists ((q m) :: seq.scanl (Tf m) (q m) w).
      split; auto. 
      (* I need a more generalized version of assumption i *)
      apply sipser_accept_more_general. auto.
    Qed.

    (* The reason I can't use bi-implication in above proof is
       sipser_accept is computational. 
       If you feed it the machine m, and word w, then it would 
       give you list of intermediate states which satisfy the 
       sipser property. It could be written as pure Prop 
       if you don't need it as computational *)

   (*
    Lemma sipser_accept_Eqv_machine_accept :
      forall (w : word) (m : Automata),
        sipser_accept m w -> machine_accpet m w = true.
    Proof.
      unfold sipser_accept, machine_accpet.
      intros w m [r [Hf1 Hf2]].
      refine (match in_dec
                      Hsdec
                     (fold_machine m (q m) w) (Fs m) with
              | left _ =>  _
              | right _ =>  _
              end); try auto.
      apply sipser_accept_more_general in Hf2.
      congruence.
    Qed. *)

    Lemma sipser_accept_Eqv_machine_accept :
      forall (w : word) (m : Automata),
        sipser_accept m w -> machine_accept m w = true.
    Proof.
      unfold sipser_accept, machine_accept.
      intros w m [r [Hf1 Hf2]].
      apply sipser_accept_more_general. auto.
    Qed.

    
    (*  Langauge is predicate over Prop *)
    Definition language := pred word.

    (* a machine m recognizes a langauge l if machine accepts 
       every word in langauge *)
    Definition machine_recog_langauge (m : Automata) (l : language) :=
      forall w, l w -> machine_accept m w = true.

    
    (* A language l is regular if there exists a machine which 
       recognizes it *)
    Definition regular_language (l : language) :=
      existsT (m : Automata), machine_recog_langauge m l.

    
    (* decidability of words *)
    Lemma dec_word : forall w1 w2 : word, {w1 = w2} + {w1 <> w2}.
    Proof.
      intros w1 w2.
      pose proof (list_eq_dec Hadec w1 w2); try assumption.
    Qed.

    (* Now the question is, can we write boolean decision 
       procedure to decide if a language is regular or not ?. 
       Pumping Lemma because non-regular langauges are not 
       pumpable. *)
    (*
    Lemma regular_language_dec :
      forall (l : language), regular_language l +
                        ~regular_language l. *)

    
   
   

  End Verification.

  (* This works with list version 
  Section Ex1.
    (* Example from James code *)
    Inductive st : Type := s1 | s2 | s3 | s4.
    Definition qs := [s1; s2; s3; s4].
    
    Inductive abet : Type := a | b.
    Definition als := [a; b].
    
    Definition trans_fn (s : st) (alpha : abet) :=
      match s, alpha with
      | s1, a => s2
      | s1, b => s3
      | s2, _ => s4
      | s3, _ => s4
      | s4, _ => s4
      end.
    
    (* starting state s1 is in qs *)
    Lemma Inq : In s1 qs.
    Proof. firstorder. Qed.

    (* accepting state s2 in  qs *)
    Lemma hf : forall x, In x [s2] -> In x qs.
    Proof. firstorder. Qed.
  
    Definition att :=
      Build_Automata _ _ qs als trans_fn s1 Inq [s2] hf.

    Lemma state_eq_dec : forall (c d : st), {c = d} + {c <> d}.
      refine (fun c d =>
                match c,d  with
                | s1, s1 => left _
                | s2, s2 => left _
                | s3, s3 => left _
                | s4, s4 => left _
                | _, _ => right _
                end); try (intro H; inversion H); try auto.
    Defined. 


    Eval vm_compute in machine_accpet _ state_eq_dec _ att [a]. (* accpet *)
    Eval vm_compute in machine_accpet _ state_eq_dec _ att [b]. (* false *)
    Eval vm_compute in machine_accpet _ state_eq_dec _ att [a; b]. (* false *)
    Eval vm_compute in seq.scanl (Tf _ _ att) (q _ _ att) [a; b].
    
  End Ex1. *)
  

  Section Ex2.
    (* Example from James code *)
    Inductive st : Type := s1 | s2 | s3 | s4.
    Lemma Hsdec :
      forall (c d : st) , {c = d} + {c <> d}.
    Proof.
      intros a b;
        repeat destruct a; 
        repeat (destruct b) || (right; discriminate) ||(left; trivial).
    Defined.    

    Definition qs x :=
      match Hsdec x s1 with
      | left _ => true
      | right _ =>
        match Hsdec x s2 with
        | left _ => true
        | right _ =>
          match Hsdec x s3 with
          | left _ => true
          | right _ =>
            match Hsdec x s4 with
            | left _ => true
            | right _ => false
            end
          end
        end
      end.      
 
    
    
    Inductive abet : Type := a | b.
    Lemma Hadec :
      forall (c d : abet), {c = d} + {c <> d}.
    Proof.
      intros c d;
        repeat destruct c; 
        repeat (destruct d) || (right; discriminate) ||(left; trivial).
    Defined.
    
      
    Definition als x :=
      match Hadec x a with
      | left _ => true
      | right _ =>
        match Hadec x b with
        | left _ => true
        | right _ => false
        end
      end.
        
    
    Definition trans_fn (s : st) (alpha : abet) :=
      match s, alpha with
      | s1, a => s2
      | s1, b => s3
      | s2, _ => s4
      | s3, _ => s4
      | s4, _ => s4
      end.
    
    (* starting state s1 is in qs *)
    Lemma Inq : qs s1 = true.
    Proof. auto.  Qed.
    

    Definition accepting x :=
      match Hsdec x s2 with
      | left _ => true
      | right _ => false
      end.
    
    (* accepting state s2 in  qs *)
    Lemma hf : forall x, accepting x = true -> qs x = true.
    Proof. unfold accepting.
           intros. destruct x; try auto.
    Qed.
    
  
    Definition att :=
      Build_Automata _ _ qs als trans_fn s1 Inq accepting hf.

    Check machine_accept.
    Eval vm_compute in machine_accept _ _ att [a]. (* accpet *)
    Eval vm_compute in machine_accept _ _ att [b]. (* false *)
    Eval vm_compute in machine_accept _ _ att [a; b]. (* false *)
    Eval vm_compute in seq.scanl (Tf _ _ att) (q _ _ att) [a; b].

    End Ex2.

End First.
  
    

  
  

    
  
  