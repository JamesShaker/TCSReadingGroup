open HolKernel Parse boolLib bossLib;
open chap4Theory pred_setTheory topologyTheory realTheory;
open chap2_instancesTheory chap4_instancesTheory chap5Theory realLib;

val _ = new_theory "chap5_instances";

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss]

(*
continuousfn_def
open_in_euclidean
*)

Theorem lemma_5_1_1:
      continuousfn euclidean euclidean f ⇔
        ∀a e.
          0 < e ⇒
          ∃d. 0 < d ∧
              ∀x. a − d < x ∧ x < a + d ⇒ f a − e < f x ∧ f x < f a + e
Proof
    rw[continuousfn_def,EQ_IMP_THM]
    >- (‘open_in euclidean (ival (f a - e) (f a + e))’ by simp[] >>
        first_x_assum $ dxrule_then assume_tac >>
        gs[open_in_euclidean] >>
        first_x_assum $ qspec_then ‘a’ mp_tac >>
        simp[ival_def,SUBSET_DEF] >> rw[] >>
        rename [‘c1 < a’,‘a < c2’] >>
        qexists_tac ‘min (a - c1) (c2 - a)’ >> rw[min_def]) >>
    gs[open_in_euclidean] >>
    qx_gen_tac ‘a’ >> strip_tac >>
    first_x_assum dxrule >>
    simp[ival_def,SUBSET_DEF] >>
    rw[] >> rename [‘c1 < f a’,‘f a < c2’] >>
    first_x_assum $ qspecl_then [‘a’,‘min (f a - c1) (c2 - f a)’] mp_tac >>
    rw[min_def,REAL_SUB_SUB2,REAL_SUB_ADD2] >>
    qexistsl_tac [‘a - d’,‘a + d’] >> simp[] >>
    rw[] >> first_x_assum irule >>
    first_x_assum $ drule_all >> simp[]
QED

(* Example_5_1_6 *)

Theorem FINITE_closed:
  FINITE s ⇒ closed_in euclidean s
Proof
  strip_tac >> 
  ‘s = BIGUNION {{a} | a IN s}’
    by simp[Once EXTENSION,PULL_EXISTS] >>
  pop_assum SUBST1_TAC >>
  irule_at Any CLOSED_IN_BIGUNION >>
  strip_tac (* 2 *)
  >- simp[PULL_EXISTS] >>
  ‘{{a} | a ∈ s} = IMAGE (\a. {a}) s’
    by simp[Once EXTENSION] >>
  simp[]
QED          
        
    
Theorem exercise_5_1_10_i:
 finer euclidean (finite_closed_topology UNIV)
Proof 
  simp[DISJ_IMP_THM,finer_def,OPEN_IN_EMPTY] >>
  rw[] >> drule_then assume_tac FINITE_closed >>
  gs[closed_in,COMPL_COMPL_applied]
QED

        
    
  
val _ = export_theory();

