open HolKernel Parse boolLib bossLib;

open numpairTheory

open combinTheory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;
open numpairTheory;

open listTheory;
open rich_listTheory;

val _ = new_theory "nlist";


val _ = ParseExtras.tight_equality()

val nlist_of_def = Define`
  (nlist_of [] = 0) ∧
  (nlist_of (h::t) = ncons h (nlist_of t))
`;



val _ = export_rewrites ["nlist_of_def"]



val nhd_def = Define`nhd nl = nfst (nl - 1)`



val ntl_def = Define`ntl nlist = nsnd (nlist - 1)`



val ndrop_def = Define`
  (ndrop 0 nlist = nlist) ∧
  (ndrop (SUC n) nlist = ntl (ndrop n nlist))
`;



val nel_def = Define`nel n nlist = nhd (ndrop n nlist)`



val nhd_thm = store_thm(
  "nhd_thm[simp]",
  ``nhd (ncons h t) = h``,
  SRW_TAC [][ncons_def, nhd_def]);



val ntl_thm = store_thm(
  "ntl_thm[simp]",
  ``ntl (ncons h t) = t``,
  simp[ncons_def, ntl_def])



val listOfN_lemma = store_thm(
"listOfN_lemma",
``!n. n > 0 ==> ntl n < n``,
rw[ntl_def]>>
Induct_on `n`
>- (strip_tac >> fs[])
>- rw[nsnd_def]
);



val listOfN_def = tDefine "listOfN" `listOfN n = if n = 0 then [] else nhd n :: listOfN (ntl n)` (WF_REL_TAC `$<` >> simp[listOfN_lemma])



val nlast_def = tDefine "nlast" `
nlast l = if l = 0 then 0 else if ntl l = 0 then nhd l else nlast (ntl l)` (WF_REL_TAC `$<` >> simp[ntl_def] >> rpt strip_tac >> `nsnd (l - 1) <= l - 1` by simp[nsnd_le] >> simp[]);



val nfront_def = tDefine "nfront" `
nfront l = if l = 0 then 0 else if ntl l = 0 then 0 else ncons (nhd l) (nfront (ntl l))` (WF_REL_TAC `$<` >> simp[ntl_def] >> rpt strip_tac >> `nsnd (l - 1) <= l - 1` by simp[nsnd_le] >> simp[]); 

val ncons_nhd_ntl = store_thm(
"ncons_nhd_ntl",
``!l. l <> 0 ==> ncons (nhd l) (ntl l) = l``,
Cases_on `l` >- simp[]
>- (simp[ncons_def,nhd_def,ntl_def])
);


val ntl_zero_empty_OR_ncons = store_thm(
"ntl_zero_empty_OR_ncons",
``ntl l = 0 <=> l = 0 \/ ?x. l = ncons x 0``,
eq_tac
>- (rpt strip_tac
  >> `l <> 0 ==> ∃x. l = ncons x 0` suffices_by metis_tac[]
  >> metis_tac[ncons_nhd_ntl]
)
>- (rw[]
  >- EVAL_TAC
  >- rw[ntl_def]
)
);


val listOfN_empty = store_thm(
"listOfN_empty[simp]",
``(listOfN l = [] <=> l = 0) /\ ([] = listOfN l <=> l = 0)``,
`listOfN l = [] <=> l = 0` suffices_by metis_tac[]
>> eq_tac >-
(`¬(l = 0) ==> ¬(listOfN l = [])` suffices_by metis_tac[] >>
rw[Once listOfN_def])
>- (simp[Once listOfN_def]));
;



val listOfN_nlist = store_thm(
"listOfN_nlist",
``!l. listOfN (nlist_of l) = l``,
Induct_on `l` >> simp[nlist_of_def] >>
simp[Once listOfN_def]);



val listOfN_SURJ = store_thm(
"listOfN_SURJ",
``!l. ?n. listOfN n = l``,
Induct_on `l` >- (qexists_tac `0` >> rw[Once listOfN_def])
>- (rpt strip_tac >> rw[] >> qexists_tac `nlist_of (h::listOfN n)` >> rw[listOfN_nlist]
)
);



val listOfN_INJ = store_thm(
"listOfN_INJ[simp]",
``!l1 l2. listOfN l1 = listOfN l2 <=> l1 = l2``,
simp[EQ_IMP_THM] >> completeInduct_on `l1`
>> ONCE_REWRITE_TAC[listOfN_def] >> rw[]
>> `?h1 t1. l1 = ncons h1 t1` by metis_tac[nlist_cases]
>> `?h2 t2. l2 = ncons h2 t2` by metis_tac[nlist_cases]
>> fs[]
>> first_x_assum irule >> simp[]
>> simp[ncons_def]
>> metis_tac[nsnd_le,nsnd_npair, DECIDE ``x <= y <=> x < y + 1``]);



val LENGTH_empty = store_thm(
"LENGTH_empty[simp]",
``LENGTH (listOfN l) = 0 <=> l = 0``,
eq_tac >> simp[Once listOfN_def]);



val listOfN_zero = store_thm(
"listOfN_zero[simp]",
``listOfN 0 = []``, simp[Once listOfN_def]);



val listOfN_CONS = store_thm(
"listOfN_CONS[simp]",
``(listOfN n = h :: t) <=> (?tn. n = ncons h tn /\ listOfN tn = t)``,
simp[Once listOfN_def,SimpLHS] >> rw[] >> simp[nhd_def,ntl_def,ncons_def]
>> eq_tac >> rw[]
>> rw[]);



val listOfN_ncons = store_thm(
"listOfN_ncons[simp]",
``listOfN (ncons h t) = h :: listOfN t``,
simp[Once listOfN_def,SimpLHS]);



val nlist_listOfN = store_thm(
"nlist_listOfN[simp]",
``!l. nlist_of (listOfN l) = l``,
Induct_on `listOfN l`
>> simp[]
>> rw[]
>> simp[]);



val nlast_ncons = store_thm(
"nlast_ncons[simp]",
``nlast (ncons h tn) = if tn = 0 then h else nlast tn``,
simp[SimpLHS,Once nlast_def]);



val ntl_zero = store_thm(
"ntl_zero[simp]",
``ntl 0 = 0``,
EVAL_TAC);



val ndrop_zero = store_thm(
"ndrop_zero[simp]",
``!n. ndrop n 0 = 0``,
Induct_on `n` >> simp[ndrop_def] >> EVAL_TAC);



val ntl_ndrop = store_thm(
"ntl_ndrop",
``!l. ntl (ndrop n l) = ndrop n (ntl l)``,
Induct_on `n`
>> simp[ndrop_def]);



val nlast_nel = store_thm(
"nlast_nel",
``!l. nlast l = nel (LENGTH (listOfN l) - 1) l``,
simp[nel_def] >> Induct_on `listOfN l` >> simp[]
>- (simp[nhd_def,ndrop_def,Once nlast_def] >> EVAL_TAC)
>> rw[] >> simp[] >> rw[] >> simp[ndrop_def]
>> `?h0 t0. tn = ncons h0 t0` by metis_tac[nlist_cases]
>> simp[ndrop_def,ntl_ndrop]);

val nhd_nfront = store_thm(
"nhd_nfront",
``!l. l <> 0 /\ ntl l <> 0 ==> nhd l = nhd (nfront l)``,
Induct_on `listOfN l`
>- (metis_tac[listOfN_empty])
>- (fs[Once nfront_def]));

val LENGTH_ntl_one = store_thm(
"LENGTH_ntl_one",
``LENGTH (listOfN l) = 1 ==> ntl l = 0``,
simp[Once listOfN_def] >> rw[]);



val ncons_x_0_LENGTH_1 = store_thm(
"ncons_x_0_LENGTH_1",
``LENGTH (listOfN l) = 1 <=> ?x. l = ncons x 0``,
eq_tac
>- (rpt strip_tac
  >> `ntl l = 0` by rw[LENGTH_ntl_one]
  >> Cases_on `l = 0`
    >- (`LENGTH (listOfN l) = 0` by simp[] >> simp[])
    >- metis_tac[ntl_zero_empty_OR_ncons])
>- (simp[Once listOfN_def] >> rw[] >> metis_tac[ntl_zero_empty_OR_ncons]));


val LENGTH_ncons = store_thm(
"LENGTH_ncons",
``LENGTH (listOfN (ncons x h)) = LENGTH (listOfN h) + 1``,
Induct_on `listOfN h`
>> simp[Once listOfN_def] >> rw[]);



val ntl_ncons_zero = store_thm(
"ntl_ncons_zero",
``ntl (ncons h tn) = 0 <=> tn = 0``,
eq_tac >> simp[]);



val LENGTH_nfront = store_thm(
"LENGTH_nfront",
``t <> 0 ==> LENGTH (listOfN (nfront t)) + 1 = LENGTH (listOfN t)``,
Induct_on `listOfN t`
>- simp[]
>- (simp[Once nfront_def,LENGTH_ncons] >> rw[]
  >- (simp[] >> metis_tac[ntl_ncons_zero])
  >- (`tn <> 0` by metis_tac[ntl_ncons_zero]
    >> `listOfN tn = listOfN tn` by metis_tac[]
    >> `LENGTH (listOfN (nfront tn)) + 1 = LENGTH (listOfN tn)` by metis_tac[]
    >> simp[])
  )
);



val ndrop_nsingl = store_thm(
"ndrop_nsingl",
``m <> 0 ==> ndrop m (ncons x 0) = 0``,
`m >= 1 ==> ndrop m (ncons x 0) = 0` suffices_by simp[DECIDE ``x <> 0 <=> x >= 1``]
>> rpt strip_tac >> completeInduct_on `m` >> rpt strip_tac
>> Cases_on `m = 1`
  >- (`m = SUC 0` by simp[]
    >> rw[] >> `ntl (ndrop 0 (ncons x 0)) = 0` suffices_by metis_tac[ndrop_def]
    >> simp[ndrop_def])
  >- (`m > 0` by simp[] >> `m = SUC (m - 1)` by simp[]
    >> `m - 1 < m` by simp[]
    >> `m >= 2` by simp[]
    >> `m - 1 >= 1` by simp[]
    >> `ndrop (m - 1) (ncons x 0) = 0` by simp[]
    >> `ntl (ndrop (m - 1) (ncons x 0)) = 0` suffices_by metis_tac[ndrop_def]
    >> simp[])
    );



val nfront_nsingl = store_thm(
"nfront_nsingl",
``nfront (ncons x 0) = 0``,
simp[ntl_thm,Once nfront_def]);



val nfront_thm = store_thm(
"nfront_thm",
``nfront 0 = 0 /\
nfront (ncons h t) = if t = 0 then 0 else ncons h (nfront t)``,
ONCE_REWRITE_TAC [nfront_def] >> simp[] >> rw[]
>> simp[SimpLHS,Once nfront_def]);



val nel_nfront = store_thm(
"nel_nfront",
``!t. m < LENGTH (listOfN (nfront t)) ==> nel m (nfront t) = nel m t``,
simp[nel_def] >> Induct_on `m` >> simp[ndrop_def]
>> gen_tac
>> qspec_then `t` STRUCT_CASES_TAC nlist_cases >> simp[nfront_thm] >> rw[] >> simp[ntl_ndrop]);



val nsnoc_cases = store_thm(
"nsnoc_cases",
``!t. t = 0 \/
?f l. t = napp f (ncons l 0)``,
completeInduct_on `t` >>
qspec_then `t` FULL_STRUCT_CASES_TAC nlist_cases
>> simp[]
>> rename [`ncons h t`]
>> `t < ncons h t` by (EVAL_TAC >> simp[])
>> first_x_assum drule >> rw[]
>- (map_every qexists_tac [`0`,`h`] >> simp[])
>> map_every qexists_tac [`ncons h f`,`l`] >> simp[]);



val nhd_napp = store_thm(
"nhd_napp",
``!l1 l2. l1 <> 0 ==> nhd (napp l1 l2) = nhd l1``,
rpt strip_tac >> Induct_on `listOfN l1` >- simp[]
>> rw[] >> rw[napp_thm]);



val nel_nfront = store_thm(
"nel_nfront",
``!t. m < LENGTH (listOfN (nfront t)) ==> nel m (nfront t) = nel m t``,
simp[nel_def] >> Induct_on `m` >> simp[ndrop_def]
>> gen_tac
>> qspec_then `t` STRUCT_CASES_TAC nlist_cases >> simp[nfront_thm] >> rw[] >> simp[ntl_ndrop]);



val nel_napp = store_thm(
"nel_napp",
``!l1 l2. n < LENGTH (listOfN l1) ==> nel n (napp l1 l2) = nel n l1``,
simp[nel_def] >> Induct_on `n` >> simp[ndrop_def]
>- (rpt gen_tac
>> qspec_then `l1` STRUCT_CASES_TAC nlist_cases
  >- simp[]
  >- simp[napp_thm])
>- (rpt gen_tac
>> qspec_then `l1` STRUCT_CASES_TAC nlist_cases
  >- simp[]
  >- (simp[napp_thm] >> simp[ntl_ndrop])));



val LENGTH_nonzero = store_thm(
"LENGTH_nonzero",
``(l <> 0 <=> LENGTH (listOfN l) > 0) /\ (LENGTH (listOfN l) > 0 <=> l <> 0)``,
`l <> 0 <=> LENGTH (listOfN l) > 0` suffices_by metis_tac[]
>> eq_tac >> simp[Once listOfN_def] >> rw[]);


val LENGTH_le_napp = store_thm(
"LENGTH_le_napp",
``!l1 l2. LENGTH (listOfN l1) <= LENGTH (listOfN (napp l1 l2))``,
rpt gen_tac
>> Induct_on `listOfN l1`
  >- (ONCE_REWRITE_TAC [listOfN_def,napp_thm] >> rw[])
  >- (rw[Once napp_thm]
    >> `napp (ncons h tn) l2 = ncons h (napp tn l2)` by simp[napp_thm]
    >> `LENGTH (listOfN (ncons h tn)) ≤ LENGTH (listOfN (ncons h (napp tn l2)))` suffices_by simp[]
    >> rw[LENGTH_ncons]));

val napp_eq_0 = Q.store_thm(
  "napp_eq_0[simp]",
  `(napp x y = 0) <=> (x = 0 /\ y = 0)`,
  qspec_then `x` STRUCT_CASES_TAC nlist_cases >>
  simp[napp_thm]); 

val nfront_napp_sing = Q.store_thm(
  "nfront_napp_sing",
  `nfront (napp pfx (ncons e 0)) = pfx`,
  completeInduct_on `pfx` >>
  qspec_then `pfx` FULL_STRUCT_CASES_TAC nlist_cases
  >- simp[nfront_thm] >>
  simp[nfront_thm] >> pop_assum irule >>
  simp[ncons_def, npair_def]);

val lt_ncons = Q.store_thm(
  "lt_ncons",
  `t < ncons h t`,
  simp[ncons_def, npair_def]);

val nlen_napp = Q.store_thm(
  "nlen_napp[simp]",
  `nlen (napp x y) = nlen x + nlen y`,
  completeInduct_on `x` >>
  qspec_then `x` FULL_STRUCT_CASES_TAC nlist_cases >>
  simp[lt_ncons]);

val LENGTH_listOfN_nlen = Q.store_thm(
  "LENGTH_listOfN_nlen[simp]",
  `!n. LENGTH (listOfN n) = nlen n`,
  ho_match_mp_tac nlist_ind >> simp[]);

val ncons_napp = store_thm(
"ncons_napp",
``ncons h t = napp (nlist_of [h]) t``,
simp[nlist_of_def]);


val nlen_nnil = store_thm(
"nlen_nnil[simp]",
``!x. nlen x = 0 <=> x = 0``,
gen_tac >> eq_tac 
>> `LENGTH (listOfN x) = nlen x` by metis_tac[LENGTH_listOfN_nlen]
>> strip_tac >> metis_tac[LENGTH_empty]);


val nel_napp2 = Q.store_thm(
  "nel_napp2",
  `!y n x. nlen x <= n ==> (nel n (napp x y) = nel (n - nlen x) y)`,
  Induct_on `n`
  >- (rpt strip_tac >> `nlen x = 0` by fs[] >> `x = 0` by fs[nlen_nnil] >> rw[napp_thm])
  >- (rpt strip_tac >> qspec_then `x` FULL_STRUCT_CASES_TAC nlist_cases
    >- (`nlen 0 = 0` by EVAL_TAC >> rw[napp_thm])
    >- (fs[nel_def,ndrop_def] >> rw[ntl_ndrop]
      >> `SUC n = n + 1` by simp[]
      >> `nlen t + 1 = 1 + nlen t` by simp[]
      >> `SUC n - (nlen t + 1) = (n + 1) - (nlen t + 1)` by metis_tac[]
      >> `_ = (n + 1) - (1 + nlen t)` by metis_tac[]
      >> `_ = ((n + 1) - 1) - nlen t` by fs[]
      >> `_ = n - nlen t` by fs[] >> rw[])));



val nel_ncons_nonzero = Q.store_thm(
  "nel_ncons_nonzero",
  `0 < n ==> (nel n (ncons h t) = nel (n - 1) t)`,
  rpt strip_tac >>
  `ncons h t = napp (nlist_of [h]) t` by simp[Once ncons_napp] >>
  `nlen (nlist_of [h]) = 1` by simp[nlen_def] >>
  `1 <= n` by simp[] >>
  metis_tac[nel_napp2]);



val npair_le = store_thm(
"npair_le",
``npair n n1 < npair n n2 ==> n1 < n2``,
rpt strip_tac >> fs[npair_def] >> SPOSE_NOT_THEN ASSUME_TAC
>> `n1 >= n2` by simp[]
>> `n + n1 >= n + n2` by simp[]
>> `n + n2 <= n + n1` by simp[]
>> `tri (n + n2) <= tri (n + n1)` by metis_tac[tri_LE]
>> `n2 <= n1` by simp[]
>> `n2 + tri (n + n2) ≤ n1 + tri (n + n1)` by simp[]
>> fs[]);


val le_npair = store_thm(
"le_npair",
``n1 < n2 ==> !n. npair n n1 < npair n n2``,
rpt strip_tac >> simp[npair_def] >>
`n + n1 < n + n2` by simp[] >>
`tri (n + n1) < tri (n + n2)` by simp[tri_LT] >> simp[]);




val napp_nsnoc_le = store_thm(
"napp_nsnoc_le",
``!l. l < napp l (ncons x 0)``,
ho_match_mp_tac nlist_ind >>
rpt strip_tac
>- (simp[napp_thm] >> simp[ncons_def])
>- (simp[napp_thm] >> simp[ncons_def] >>
`(x ⊗ 0 + 1) = ncons x 0` by simp[ncons_def] >> rw[] >> metis_tac[le_npair]));


val napp_sing_eq = store_thm(
"napp_sing_eq",
``napp l1 (ncons l 0) = ncons x 0 ==> l1 = 0``,
qspec_then `l1` STRUCT_CASES_TAC nlist_cases
>- metis_tac[]
>- (rpt strip_tac >> fs[napp_thm]));

val nel_nhd = store_thm(
"nel_nhd",
``nel 0 l = nhd l``,
simp[nel_def,ndrop_def]);



val nel_eq_nlist = store_thm(
"nel_eq_nlist",
``!l1. (!l2. LENGTH (listOfN l1) = LENGTH (listOfN l2) ==>
(!m. m < LENGTH (listOfN l1) ==> nel m l1 = nel m l2) ==> l1 = l2)``,
ho_match_mp_tac nlist_ind >> rpt strip_tac
>- (`LENGTH (listOfN 0) = 0` by EVAL_TAC >> metis_tac[LENGTH_empty])
>- (qspec_then `l2` FULL_STRUCT_CASES_TAC nlist_cases
  >- (`LENGTH (listOfN 0) = 0` by EVAL_TAC >> metis_tac[LENGTH_empty])
  >- (`h = h' /\ l1 = t` suffices_by rw[] >> rw[]
    >- (`nel 0 (ncons h l1) = h` by simp[nel_nhd,nhd_thm]
      >> `nel 0 (ncons h' t) = h'` by simp[nel_nhd,nhd_thm]
      >> `LENGTH (listOfN (ncons h l1)) = LENGTH (listOfN l1) + 1` by fs[LENGTH_ncons]
      >> `LENGTH (listOfN (ncons h l1)) >= 1` by simp[]
      >> `LENGTH (listOfN (ncons h l1)) > 0` by simp[]
      >> `0 < LENGTH (listOfN (ncons h l1))` by simp[]
      >> `nel 0 (ncons h l1) = nel 0 (ncons h' t)` by metis_tac[]
      >> fs[])
    >- (first_x_assum irule >> rw[]
      >- (SPOSE_NOT_THEN ASSUME_TAC >> fs[]
        >> `m + 1 < nlen l1 + 1` by simp[]
	>> `nel (m + 1) (ncons h l1) <> nel (m + 1) (ncons h' t)` suffices_by fs[]
	>> `0 < m + 1` by simp[]
	>> `nel (m + 1) (ncons h l1) = nel (m + 1 - 1) l1` by metis_tac[nel_ncons_nonzero]
	>> `_ = nel m l1` by simp[]
	>> `nel (m + 1) (ncons h' t) = nel (m + 1 - 1) t` by metis_tac[nel_ncons_nonzero]
	>> `_ = nel m t` by simp[]
	>> metis_tac[])
      >- (`LENGTH (listOfN (ncons h l1)) = LENGTH (listOfN l1) + 1` by fs[LENGTH_ncons]
        >> `LENGTH (listOfN (ncons h' t)) = LENGTH (listOfN t) + 1` by fs[LENGTH_ncons]
	>> `LENGTH (listOfN l1) + 1 = LENGTH (listOfN t) + 1` by fs[]
	>> fs[])))
    ));






val nel_ncons_singl = store_thm(
"nel_ncons_singl",
``nel 0 (ncons x 0) = x``,
rw[nel_def] >> rw[ndrop_def]);


val napp_ncons_not_nnil = store_thm(
"napp_ncons_not_nnil",
``!t h tn. napp t (ncons h tn) <> 0``,
rpt gen_tac
>> `ncons h tn <> 0` by simp[ncons_not_nnil]
        >> qspec_then `t` FULL_STRUCT_CASES_TAC nlist_cases
	  >>fs[napp_thm,ncons_not_nnil]);




val nlast_napp = store_thm(
"nlast_napp",
``!l1 l2. l2 <> 0 ==> nlast (napp l1 l2) = nlast l2``,
Induct_on `listOfN l1` >> simp[]
>> rw[]
>> simp[napp_thm] >> rw[]
  >> qspec_then `l2` FULL_STRUCT_CASES_TAC nlist_cases
  >> simp[]
  >> metis_tac[napp_ncons_not_nnil]);
  

val LENGTH_ntl = store_thm(
"LENGTH_ntl",
``!l. l <> 0 ==> LENGTH(listOfN l) = LENGTH (listOfN (ntl l)) + 1``,
rpt strip_tac
>> qspec_then `l` FULL_STRUCT_CASES_TAC nlist_cases
  >- fs[]
  >- simp[ntl_thm]);
 


val LENGTH_napp_singl = store_thm(
"LENGTH_napp_singl",
``LENGTH (listOfN (napp w (ncons v 0))) = LENGTH (listOfN w) + 1``,
Induct_on `listOfN w`
>- simp[Once listOfN_def]
>- (rw[]
  >> simp[napp_thm]));



val napp_ndrop_l1_empty = store_thm(
"napp_ndrop_l1_empty",
``!l1 l2. ndrop (LENGTH (listOfN l1)) (napp l1 l2) = l2``,
ho_match_mp_tac nlist_ind >> rpt strip_tac
>- simp[ndrop_def,napp_thm]
>- (simp[LENGTH_ncons]
  >> `nlen l1 + 1 = SUC (nlen l1)` by simp[] >> simp[ndrop_def] >> simp[ntl_ndrop] >> `nlen l1 = LENGTH (listOfN l1)` by simp[] >> metis_tac[]));




val nel_napp_l2_singl = store_thm(
"nel_napp_l2_singl",
``nel (LENGTH (listOfN w)) (napp w (ncons v 0)) = v``,
simp[nel_def]
>> `nlen w = (LENGTH (listOfN w))` by simp[]
>> `ndrop (nlen w) (napp w (ncons v 0)) = ncons v 0` by metis_tac[napp_ndrop_l1_empty]
>> simp[nhd_thm]);


val nlast_napp_singl = store_thm(
"nlast_napp_singl",
``nlast (napp w (nlist_of [v'])) = v'``,
`nlist_of [v'] <> 0` by simp[nlist_of_def,ncons_not_nnil]
>> simp[nlast_napp]);

Theorem ntl_LE :
!n. ntl n <= n
Proof
rw[ntl_def,ncons_def] >> `nsnd (n - 1) <= n - 1` by fs[nsnd_le] >> fs[]
QED

Theorem ntl_nonzero_LESS :
!n. n <> 0 ==> ntl n < n
Proof
rw[ntl_def,ncons_def] >> `nsnd (n - 1) <= n - 1` by fs[nsnd_le] >>
`n - 1 < n` by fs[] >> fs[]
QED


val nfst_le_npair = store_thm(
  "nfst_le_npair[simp]",
  ``n <= npair n m``,
  `n = nfst (npair n m)` by simp[GSYM nfst_npair] >>
  `nfst (npair n m) <= npair n m` by simp[nfst_le] >> fs[]);

val nsnd_le_npair = store_thm(
  "nsnd_le_npair[simp]",
  ``m <= npair n m``,
  `m = nsnd (npair n m)` by simp[GSYM nsnd_npair] >>
  `nsnd (npair n m) <= npair n m` by simp[nsnd_le] >> fs[]);

Theorem nel_EL :
!m l. m < nlen l ==> nel m l = EL m (listOfN l)
Proof
  Induct_on `listOfN l` >> rw[] >> `listOfN tn = listOfN tn` by fs[] >> first_assum drule >>
  rw[] >> Cases_on `m = 0` (* 2 *)
  >- simp[nel_nhd]
  >- (`0 < m` by fs[] >> simp[nel_ncons_nonzero] >> simp[EL_CONS] >>
     `nel (m − 1) tn = EL (m - 1) (listOfN tn)` suffices_by fs[] >>
     `m - 1 < nlen tn` suffices_by metis_tac[] >>
     `m < nlen tn + 1` by fs[nlen_thm] >> fs[])
QED

Theorem MEM_listOfN_LESS :
!e l. MEM e (listOfN l) ==> e < l
Proof
  Induct_on `listOfN l` >> rw[] >>
  first_x_assum (qspecl_then [`tn`] mp_tac) >> rw[] >> fs[listOfN_ncons] (* 2 *)
  >- (rw[ncons_def] >> `e <= npair e tn` by simp[] >>
     `npair e tn < (npair e tn) + 1` by rw[] >> irule LESS_EQ_LESS_TRANS >>
     rw[ncons_def] >> qexists_tac `npair e tn` >> rw[nfst_le])
  >- (`tn <= ncons h tn` suffices_by metis_tac[LESS_LESS_EQ_TRANS] >> rw[ncons_def] >>
     `tn <= npair h tn` by simp[] >>
     `npair h tn <= (npair h tn) + 1` by rw[] >> metis_tac[LESS_EQ_TRANS])
QED




val _ = export_theory();

