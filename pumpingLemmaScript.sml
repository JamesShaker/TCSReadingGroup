open HolKernel Parse boolLib bossLib;
open combinTheory
     listTheory
     mp_then
     nlistTheory
     numpairTheory
     pred_setTheory
     relationTheory
     rich_listTheory
     chap1Theory;

val _ = new_theory "pumpingLemma";

Definition exp_def:
  (exp s 0 = []) ∧
  (exp s (SUC n) = s ++ (exp s n))
End

Theorem wfFA_remain_Q:
  ∀M. wfFA M ⇒
    ∀ss.
      (∀n. n < LENGTH ss - 1 ⇒
          ∃c. 
            M.tf (EL n ss) c = (EL (SUC n) ss)) ∧
      HD ss ∈ M.Q ⇒
      (∀e. MEM e ss ⇒ e ∈ M.Q)
Proof
 ntac 2 strip_tac >>
 Induct_on ‘ss’ >> simp[DISJ_IMP_THM,FORALL_AND_THM] >>
 rw[] >>
 first_x_assum irule >>
 rw[]
 >- (first_x_assum (qspec_then ‘SUC n’ assume_tac) >>
     rfs[] >> metis_tac[])
 >- (first_x_assum (qspec_then ‘0’ assume_tac) >>
     Cases_on ‘ss’ >> fs[wfFA_def] >>
     metis_tac[])
QED


Theorem pumpingLemma:
  ∀l. regularLanguage l ⇒
		∃p.∀s.
      s ∈ l ∧ LENGTH s ≥ p ⇒
      ∃x y z.
        s = x ++ y ++ z ∧
        ∀i.
          (x ++ exp y i ++ z) ∈ l
Proof
  (* We decided this should be changed to use runMachine and
     GENLIST instead of Sipser_Accepts in the assumptions *)
  rw[regularLanguage_def,recogLangD_def] >>
  qexists_tac ‘SUC (CARD(M.Q))’ >>
  rw[] >>
  RULE_ASSUM_TAC (REWRITE_RULE [Sipser_Accepts_def]) >>
  fs[] >>
  ‘∃ n m. n < m ∧ EL n ss = EL m ss’
    by (‘¬INJ (λx. EL x ss) (count (LENGTH ss)) M.Q’
          suffices_by (rw[INJ_IFF]
                       >- (metis_tac[wfFA_def,wfFA_remain_Q,MEM_EL,
                                     arithmeticTheory.ADD1]) >>
                       rename[‘EL i ss = EL j ss ⇔ i = j’] >>
                       ‘i ≠ j’ by metis_tac[] >>
                       fs[] >>
                       metis_tac[DECIDE ``a ≠ b ⇒ a < b ∨ b < a``]) >>
        irule PHP >>
        simp[] >> fs[wfFA_def]) >>
  map_every qexists_tac [‘TAKE n s’,‘DROP n (TAKE m s)’,‘DROP m s’] >>
  simp[Sipser_Accepts_runMachine_coincide,accepts_def,runMachine_append] >>
  cheat
QED

val _ = export_theory();

