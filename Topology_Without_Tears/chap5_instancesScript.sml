open HolKernel Parse boolLib bossLib;
open chap4Theory pred_setTheory topologyTheory;
open chap4_instancesTheory chap5Theory realLib;

val _ = new_theory "chap5_instances";
 
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

