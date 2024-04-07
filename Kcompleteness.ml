(* ========================================================================= *)
(* Proof of the modal completeness of the provability logic K.               *)
(*                                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Iterated conjunction of formulae.                                         *)
(* ------------------------------------------------------------------------- *)

let CONJLIST = new_recursive_definition list_RECURSION
  `CONJLIST [] = True /\
   (!p X. CONJLIST (CONS p X) = if X = [] then p else p && CONJLIST X)`;;

let CONJLIST_IMP_MEM = prove
 (`!p X. MEM p X ==> |-- (CONJLIST X --> p)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; CONJLIST] THEN
  STRIP_TAC THENL
  [POP_ASSUM (SUBST_ALL_TAC o GSYM) THEN
   COND_CASES_TAC THEN REWRITE_TAC[K_IMP_REFL_TH; K_AND_LEFT_TH];
   COND_CASES_TAC THENL [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
   MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `CONJLIST t` THEN CONJ_TAC THENL
   [MATCH_ACCEPT_TAC K_AND_RIGHT_TH; ASM_SIMP_TAC[]]]);;

let CONJLIST_MONO = prove
 (`!X Y. (!p. MEM p Y ==> MEM p X) ==> |-- (CONJLIST X --> CONJLIST Y)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; CONJLIST] THENL
  [MESON_TAC[K_ADD_ASSUM; K_TRUTH_TH]; ALL_TAC] THEN
   COND_CASES_TAC THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC[MEM] THEN MESON_TAC[CONJLIST_IMP_MEM];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC K_AND_INTRO THEN CONJ_TAC THENL
  [ASM_MESON_TAC[CONJLIST_IMP_MEM];
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let CONJLIST_CONS = prove
 (`!p X. |-- (CONJLIST (CONS p X) <-> p && CONJLIST X)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJLIST] THEN COND_CASES_TAC THEN
  REWRITE_TAC[K_IFF_REFL_TH] THEN POP_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[CONJLIST] THEN ONCE_REWRITE_TAC[K_IFF_SYM] THEN
  MATCH_ACCEPT_TAC K_AND_RIGHT_TRUE_TH);;

let CONJLIST_IMP_HEAD = prove
 (`!p X. |-- (CONJLIST (CONS p X) --> p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJLIST] THEN COND_CASES_TAC THENL
  [ASM_REWRITE_TAC[K_IMP_REFL_TH];
   REWRITE_TAC[K_AND_LEFT_TH]]);;

let CONJLIST_IMP_TAIL = prove
 (`!p X. |-- (CONJLIST (CONS p X) --> CONJLIST X)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJLIST] THEN COND_CASES_TAC THENL
  [ASM_REWRITE_TAC[CONJLIST; K_IMP_CLAUSES];
   REWRITE_TAC[K_AND_RIGHT_TH]]);;

let HEAD_TAIL_IMP_CONJLIST = prove
 (`!p h t. |-- (p --> h) /\ |-- (p --> CONJLIST t)
           ==> |-- (p --> CONJLIST (CONS h t))`,
  INTRO_TAC "!p h t; ph pt" THEN REWRITE_TAC[CONJLIST] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[K_AND_INTRO]]);;

let IMP_CONJLIST = prove
 (`!p X. |-- (p --> CONJLIST X) <=> (!q. MEM q X ==> |-- (p --> q))`,
  GEN_TAC THEN SUBGOAL_THEN
    `(!X q. |-- (p --> CONJLIST X) /\ MEM q X ==> |-- (p --> q)) /\
     (!X. (!q. MEM q X ==> |-- (p --> q)) ==> |-- (p --> CONJLIST X))`
    (fun th -> MESON_TAC[th]) THEN
  CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC K_IMP_TRANS THEN
   EXISTS_TAC `CONJLIST X` THEN ASM_SIMP_TAC[CONJLIST_IMP_MEM];
   ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THENL
  [REWRITE_TAC[CONJLIST; K_IMP_CLAUSES]; ALL_TAC] THEN
  DISCH_TAC THEN  MATCH_MP_TAC HEAD_TAIL_IMP_CONJLIST THEN
  ASM_SIMP_TAC[]);;

let CONJLIST_IMP_SUBLIST = prove
 (`!X Y. Y SUBLIST X ==> |-- (CONJLIST X --> CONJLIST Y)`,
  REWRITE_TAC[SUBLIST; IMP_CONJLIST] THEN MESON_TAC[CONJLIST_IMP_MEM]);;

let CONJLIST_IMP = prove
 (`!l m.
     (!p. MEM p m ==> ?q. MEM q l /\ |-- (q --> p))
     ==> |-- (CONJLIST l --> CONJLIST m)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
  [REWRITE_TAC[CONJLIST; K_IMP_CLAUSES]; ALL_TAC] THEN
  INTRO_TAC "hp" THEN
  MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `h && CONJLIST t` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC K_AND_INTRO THEN
   CONJ_TAC THENL
   [HYP_TAC "hp: +" (SPEC `h:form`) THEN
    REWRITE_TAC[MEM] THEN MESON_TAC[CONJLIST_IMP_MEM; K_IMP_TRANS];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    INTRO_TAC "!p; p" THEN FIRST_X_ASSUM (MP_TAC o SPEC `p:form`) THEN
    ASM_REWRITE_TAC[MEM]];
   ALL_TAC] THEN
  MESON_TAC[CONJLIST_CONS; K_IFF_IMP2]);;

let CONJLIST_APPEND = prove
 (`!l m. |-- (CONJLIST (APPEND l m) <-> CONJLIST l && CONJLIST m)`,
  FIX_TAC "m" THEN LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THENL
  [REWRITE_TAC[CONJLIST] THEN ONCE_REWRITE_TAC[K_IFF_SYM] THEN
   MATCH_ACCEPT_TAC K_AND_LEFT_TRUE_TH;
   ALL_TAC] THEN
  MATCH_MP_TAC K_IFF_TRANS THEN
  EXISTS_TAC `h && CONJLIST (APPEND t m)` THEN REWRITE_TAC[CONJLIST_CONS] THEN
  MATCH_MP_TAC K_IFF_TRANS THEN
  EXISTS_TAC `h && (CONJLIST t && CONJLIST m)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_AND_SUBST_TH THEN ASM_REWRITE_TAC[K_IFF_REFL_TH];
   ALL_TAC] THEN
  MATCH_MP_TAC K_IFF_TRANS THEN
  EXISTS_TAC `(h && CONJLIST t) && CONJLIST m` THEN CONJ_TAC THENL
  [MESON_TAC[K_AND_ASSOC_TH; K_IFF_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC K_AND_SUBST_TH THEN REWRITE_TAC[K_IFF_REFL_TH] THEN
  ONCE_REWRITE_TAC[K_IFF_SYM] THEN MATCH_ACCEPT_TAC CONJLIST_CONS);;

let FALSE_NOT_CONJLIST = prove
 (`!X. MEM False X ==> |-- (Not (CONJLIST X))`,
  INTRO_TAC "!X; X" THEN REWRITE_TAC[K_NOT_DEF] THEN
  MATCH_MP_TAC CONJLIST_IMP_MEM THEN POP_ASSUM MATCH_ACCEPT_TAC);;

let CONJLIST_MAP_BOX = prove
 (`!l. |-- (CONJLIST (MAP (Box) l) <-> Box (CONJLIST l))`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[CONJLIST; MAP; K_IFF_REFL_TH] THEN
   MATCH_MP_TAC K_IMP_ANTISYM THEN
   SIMP_TAC[K_ADD_ASSUM; K_TRUTH_TH; K_NECESSITATION];
   ALL_TAC] THEN
  REWRITE_TAC[MAP] THEN MATCH_MP_TAC K_IFF_TRANS THEN
  EXISTS_TAC `Box h && CONJLIST (MAP (Box) t)` THEN CONJ_TAC THENL
  [MATCH_ACCEPT_TAC CONJLIST_CONS; ALL_TAC] THEN MATCH_MP_TAC K_IFF_TRANS THEN
  EXISTS_TAC `Box h && Box (CONJLIST t)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_IMP_ANTISYM THEN CONJ_TAC THEN
   MATCH_MP_TAC K_AND_INTRO THEN
   ASM_MESON_TAC[K_AND_LEFT_TH; K_AND_RIGHT_TH; K_IFF_IMP1;
                 K_IFF_IMP2; K_IMP_TRANS];
   ALL_TAC] THEN
  MATCH_MP_TAC K_IFF_TRANS THEN EXISTS_TAC `Box (h && CONJLIST t)` THEN
  CONJ_TAC THENL
  [MESON_TAC[K_BOX_AND_TH; K_BOX_AND_INV_TH; K_IMP_ANTISYM]; ALL_TAC] THEN
  MATCH_MP_TAC K_BOX_IFF THEN MATCH_MP_TAC K_NECESSITATION THEN
  ONCE_REWRITE_TAC[K_IFF_SYM] THEN MATCH_ACCEPT_TAC CONJLIST_CONS);;

(* ------------------------------------------------------------------------- *)
(* Consistent list of formulas.                                              *)
(* ------------------------------------------------------------------------- *)

let CONSISTENT = new_definition
  `CONSISTENT (l:form list) <=> ~ (|-- (Not (CONJLIST l)))`;;

let CONSISTENT_SING = prove
 (`!p. CONSISTENT [p] <=> ~ |-- (Not p)`,
  REWRITE_TAC[CONSISTENT; CONJLIST]);;

let CONSISTENT_LEMMA = prove
 (`!X p. MEM p X /\ MEM (Not p) X ==> |-- (Not (CONJLIST X))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[K_NOT_DEF] THEN
  MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `p && Not p` THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_AND_INTRO THEN
   ASM_MESON_TAC[CONJLIST_IMP_MEM; K_IMP_TRANS; K_AND_PAIR_TH];
   MESON_TAC[K_NC_TH]]);;

let CONSISTENT_SUBLIST = prove
 (`!X Y. CONSISTENT X /\ Y SUBLIST X ==> CONSISTENT Y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONSISTENT] THEN
  SUBGOAL_THEN `|-- (CONJLIST Y --> False) /\ Y SUBLIST X
                ==> |-- (CONJLIST X --> False)`
    (fun th -> ASM_MESON_TAC[th; K_NOT_DEF]) THEN
  INTRO_TAC "inc sub" THEN MATCH_MP_TAC K_IMP_TRANS THEN
  EXISTS_TAC `CONJLIST Y` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CONJLIST_IMP_SUBLIST]);;

let CONSISTENT_CONS = prove
 (`!h t. CONSISTENT (CONS h t) <=> ~ |-- (Not h || Not (CONJLIST t))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[CONSISTENT] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC K_IFF THEN MATCH_MP_TAC K_IFF_TRANS THEN
  EXISTS_TAC `Not (h && CONJLIST t)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_NOT_SUBST THEN MATCH_ACCEPT_TAC CONJLIST_CONS;
   MATCH_ACCEPT_TAC K_DE_MORGAN_AND_TH]);;

let CONSISTENT_NC = prove
 (`!X p. MEM p X /\ MEM (Not p) X ==> ~CONSISTENT X`,
  INTRO_TAC "!X p; p np" THEN REWRITE_TAC[CONSISTENT; K_NOT_DEF] THEN
  MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `p && Not p` THEN
  REWRITE_TAC[K_NC_TH] THEN MATCH_MP_TAC K_AND_INTRO THEN
  ASM_SIMP_TAC[CONJLIST_IMP_MEM]);;

let CONSISTENT_EM = prove
 (`!h t. CONSISTENT t
         ==> CONSISTENT (CONS h t) \/ CONSISTENT (CONS (Not h) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONSISTENT_CONS] THEN
  REWRITE_TAC[CONSISTENT] THEN
  SUBGOAL_THEN
    `|-- ((Not h || Not CONJLIST t) --> (Not Not h || Not CONJLIST t)
         --> (Not CONJLIST t))`
    (fun th -> MESON_TAC[th; K_MODUSPONENS]) THEN
  REWRITE_TAC[K_DISJ_IMP] THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_IMP_SWAP THEN REWRITE_TAC[K_DISJ_IMP] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC K_IMP_SWAP THEN MATCH_MP_TAC K_SHUNT THEN
    MATCH_MP_TAC K_FREGE THEN EXISTS_TAC `False` THEN
    REWRITE_TAC[K_NC_TH] THEN
    MATCH_MP_TAC K_ADD_ASSUM THEN MATCH_ACCEPT_TAC K_EX_FALSO_TH;
    MATCH_ACCEPT_TAC K_AXIOM_ADDIMP];
   MATCH_MP_TAC K_IMP_SWAP THEN REWRITE_TAC[K_DISJ_IMP] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC K_ADD_ASSUM THEN MATCH_ACCEPT_TAC K_IMP_REFL_TH;
    MATCH_ACCEPT_TAC K_AXIOM_ADDIMP]]);;

let FALSE_IMP_NOT_CONSISTENT = prove
 (`!X. MEM False X ==> ~ CONSISTENT X`,
  SIMP_TAC[CONSISTENT; FALSE_NOT_CONJLIST]);;

(* ------------------------------------------------------------------------- *)
(* Maximal Consistent Sets.                                                  *)
(* See Boolos p.79 (pdf p.118).  D in the text is p here.                    *)
(* ------------------------------------------------------------------------- *)

let MAXIMAL_CONSISTENT = new_definition
  `MAXIMAL_CONSISTENT p X <=>
   CONSISTENT X /\ NOREPETITION X /\
   (!q. q SUBFORMULA p ==> MEM q X \/ MEM (Not q) X)`;;

let MAXIMAL_CONSISTENT_LEMMA = prove
 (`!p X A b. MAXIMAL_CONSISTENT p X /\
             (!q. MEM q A ==> MEM q X) /\
             b SUBFORMULA p /\
             |-- (CONJLIST A --> b)
             ==> MEM b X`,
  INTRO_TAC "!p X A b; mconst subl b Ab" THEN REFUTE_THEN ASSUME_TAC THEN
  CLAIM_TAC "rmk" `MEM (Not b) X` THENL
  [ASM_MESON_TAC[MAXIMAL_CONSISTENT]; ALL_TAC] THEN
  CLAIM_TAC "rmk2" `|-- (CONJLIST X --> b && Not b)` THENL
  [MATCH_MP_TAC K_AND_INTRO THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CONJLIST_MONO; K_IMP_TRANS];
    ASM_MESON_TAC[CONJLIST_IMP_MEM]];
   ALL_TAC] THEN
  CLAIM_TAC "rmk3" `|-- (CONJLIST X --> False)` THENL
  [ASM_MESON_TAC[K_IMP_TRANS; K_NC_TH]; ALL_TAC] THEN
  SUBGOAL_THEN `~ CONSISTENT X`
    (fun th -> ASM_MESON_TAC[th; MAXIMAL_CONSISTENT]) THEN
  ASM_REWRITE_TAC[CONSISTENT; K_NOT_DEF]);;

let MAXIMAL_CONSISTENT_MEM_NOT = prove
 (`!X p q. MAXIMAL_CONSISTENT p X /\ q SUBFORMULA p
           ==> (MEM (Not q) X <=> ~ MEM q X)`,
  REWRITE_TAC[MAXIMAL_CONSISTENT] THEN MESON_TAC[CONSISTENT_NC]);;

let MAXIMAL_CONSISTENT_MEM_CASES = prove
 (`!X p q. MAXIMAL_CONSISTENT p X /\ q SUBFORMULA p
           ==> (MEM q X \/ MEM (Not q) X)`,
  REWRITE_TAC[MAXIMAL_CONSISTENT] THEN MESON_TAC[CONSISTENT_NC]);;

let MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE = prove
 (`!p w q. MAXIMAL_CONSISTENT p w /\ q SUBFORMULA p
           ==> (MEM q w <=> |-- (CONJLIST w --> q))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAXIMAL_CONSISTENT; CONSISTENT] THEN
  INTRO_TAC "(w em) sub" THEN LABEL_ASM_CASES_TAC "q" `MEM (q:form) w` THEN
  ASM_SIMP_TAC[CONJLIST_IMP_MEM] THEN CLAIM_TAC "nq" `MEM (Not q) w` THENL
  [ASM_MESON_TAC[]; INTRO_TAC "deriv"] THEN
  SUBGOAL_THEN `|-- (Not (CONJLIST w))` (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[K_NOT_DEF] THEN MATCH_MP_TAC K_IMP_TRANS THEN
  EXISTS_TAC `q && Not q` THEN REWRITE_TAC[K_NC_TH] THEN
  ASM_SIMP_TAC[K_AND_INTRO; CONJLIST_IMP_MEM]);;

let MAXIMAL_CONSISTENT_SUBFORMULA_MEM_NEG_EQ_DERIVABLE = prove
 (`!p w q. MAXIMAL_CONSISTENT p w /\ q SUBFORMULA p
           ==> (MEM (Not q) w <=> |-- (CONJLIST w --> Not q))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAXIMAL_CONSISTENT; CONSISTENT] THEN
  INTRO_TAC "(w em) sub" THEN LABEL_ASM_CASES_TAC "q" `MEM (Not q) w` THEN
  ASM_SIMP_TAC[CONJLIST_IMP_MEM] THEN CLAIM_TAC "nq" `MEM (q:form) w` THENL
  [ASM_MESON_TAC[]; INTRO_TAC "deriv"] THEN
  SUBGOAL_THEN `|-- (Not (CONJLIST w))` (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[K_NOT_DEF] THEN MATCH_MP_TAC K_IMP_TRANS THEN
  EXISTS_TAC `q && Not q` THEN REWRITE_TAC[K_NC_TH] THEN
  ASM_SIMP_TAC[K_AND_INTRO; CONJLIST_IMP_MEM]);;

(* ------------------------------------------------------------------------- *)
(* Subsentences.                                                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("SUBSENTENCE",get_infix_status "SUBFORMULA");;

let SUBSENTENCE_RULES,SUBSENTENCE_INDUCT,SUBSENTENCE_CASES =
  new_inductive_definition
  `(!p q. p SUBFORMULA q ==> p SUBSENTENCE q) /\
   (!p q. p SUBFORMULA q ==> Not p SUBSENTENCE q)`;;

let K_STANDARD_FRAME = new_definition
  `K_STANDARD_FRAME p (W,R) <=>
   W = {w | MAXIMAL_CONSISTENT p w /\
            (!q. MEM q w ==> q SUBSENTENCE p)} /\
   FRAME (W,R) /\
   (!q w. Box q SUBFORMULA p /\ w IN W
          ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`;;

let SUBFORMULA_IMP_SUBSENTENCE = prove
 (`!p q. p SUBFORMULA q ==> p SUBSENTENCE q`,
  REWRITE_TAC[SUBSENTENCE_RULES]);;

let SUBFORMULA_IMP_NEG_SUBSENTENCE = prove
 (`!p q. p SUBFORMULA q ==> Not p SUBSENTENCE q`,
  REWRITE_TAC[SUBSENTENCE_RULES]);;

(* ------------------------------------------------------------------------- *)
(* Standard model.                                                           *)
(* ------------------------------------------------------------------------- *)

let K_STANDARD_MODEL = new_definition
  `K_STANDARD_MODEL p (W,R) V <=>
   K_STANDARD_FRAME p (W,R) /\
   (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`;;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let K_TRUTH_LEMMA = prove
(`!W R p V q.
    ~ |-- p /\
    K_STANDARD_MODEL p (W,R) V /\
    q SUBFORMULA p
    ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
 REPEAT GEN_TAC THEN
 REWRITE_TAC[K_STANDARD_MODEL; K_STANDARD_FRAME; SUBSENTENCE_CASES] THEN
 INTRO_TAC "np ((W FRAME 1) val) q" THEN REMOVE_THEN "W" SUBST_VAR_TAC THEN
 REWRITE_TAC[FORALL_IN_GSPEC] THEN REMOVE_THEN "q" MP_TAC THEN
 HYP_TAC "1" (REWRITE_RULE[IN_ELIM_THM]) THEN
 HYP_TAC "val" (REWRITE_RULE[FORALL_IN_GSPEC]) THEN
 SPEC_TAC (`q:form`,`q:form`) THEN MATCH_MP_TAC form_INDUCT THEN
 REWRITE_TAC[holds] THEN
 CONJ_TAC THENL
 [INTRO_TAC "sub; !w; w" THEN
  HYP_TAC "w -> cons memq" (REWRITE_RULE[MAXIMAL_CONSISTENT]) THEN
  ASM_MESON_TAC[FALSE_IMP_NOT_CONSISTENT];
  ALL_TAC] THEN
 CONJ_TAC THENL
 [REWRITE_TAC[MAXIMAL_CONSISTENT] THEN
  INTRO_TAC "p; !w; (cons (norep mem)) subf" THEN
  HYP_TAC "mem: t | nt" (C MATCH_MP (ASSUME `True SUBFORMULA p`)) THEN
  ASM_REWRITE_TAC[] THEN
  REFUTE_THEN (K ALL_TAC) THEN
  REMOVE_THEN "cons" MP_TAC THEN REWRITE_TAC[CONSISTENT] THEN
  REWRITE_TAC[K_NOT_DEF] THEN MATCH_MP_TAC K_IMP_TRANS THEN
  EXISTS_TAC `Not True` THEN ASM_SIMP_TAC[CONJLIST_IMP_MEM] THEN
  MATCH_MP_TAC K_IFF_IMP1 THEN MATCH_ACCEPT_TAC K_NOT_TRUE_TH;
  ALL_TAC] THEN
 CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
 CONJ_TAC THENL
 [INTRO_TAC "![q/a]; q; sub; !w; w" THEN REMOVE_THEN "q" MP_TAC THEN
  MATCH_MP_TAC (MESON[] `P /\ (P /\ Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
   INTRO_TAC "sub1 q"] THEN EQ_TAC THENL
   [HYP MESON_TAC "w sub1 q" [MAXIMAL_CONSISTENT_MEM_NOT];
    REMOVE_THEN "q" (MP_TAC o SPEC `w: form list`) THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_NOT]];
    ALL_TAC] THEN
 REPEAT CONJ_TAC THEN TRY
 (INTRO_TAC "![q1] [q2]; q1 q2; sub; !w; w" THEN
  REMOVE_THEN "q1" MP_TAC THEN
  MATCH_MP_TAC (MESON[] `P /\ (P /\ Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
   INTRO_TAC "sub1 +" THEN DISCH_THEN (MP_TAC o SPEC `w:form list`)] THEN
  REMOVE_THEN "q2" MP_TAC THEN
  MATCH_MP_TAC (MESON[] `P /\ (P /\ Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
   INTRO_TAC "sub2 +" THEN DISCH_THEN (MP_TAC o SPEC `w:form list`)] THEN
  HYP REWRITE_TAC "w" [] THEN
  DISCH_THEN (SUBST1_TAC o GSYM) THEN
  DISCH_THEN (SUBST1_TAC o GSYM) THEN
  CLAIM_TAC "rmk"
    `!q. q SUBFORMULA p ==> (MEM q w <=> |-- (CONJLIST w --> q))` THENL
  [ASM_MESON_TAC[MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE];
   ALL_TAC]) THENL
 [
  (* Case && *)
  ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE;
    K_AND_INTRO; K_AND_LEFT_TH; K_AND_RIGHT_TH; K_IMP_TRANS]
 ;
  (* Case || *)
  EQ_TAC THENL
  [INTRO_TAC "q1q2";
   ASM_MESON_TAC[K_OR_LEFT_TH; K_OR_RIGHT_TH; K_IMP_TRANS]] THEN
  CLAIM_TAC "wq1q2" `|-- (CONJLIST w --> q1 || q2)` THENL
  [ASM_SIMP_TAC[CONJLIST_IMP_MEM]; ALL_TAC] THEN
  CLAIM_TAC "hq1 | hq1" `MEM q1 w \/ MEM (Not q1) w` THENL
  [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CLAIM_TAC "hq2 | hq2" `MEM q2 w \/ MEM (Not q2) w` THENL
  [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
   ASM_REWRITE_TAC[];
   REFUTE_THEN (K ALL_TAC)] THEN
  SUBGOAL_THEN `~ (|-- (CONJLIST w --> False))` MP_TAC THENL
  [REWRITE_TAC[GSYM K_NOT_DEF] THEN
   ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT];
   REWRITE_TAC[]] THEN
  MATCH_MP_TAC K_FREGE THEN EXISTS_TAC `q1 || q2` THEN
  ASM_SIMP_TAC[CONJLIST_IMP_MEM] THEN MATCH_MP_TAC K_IMP_SWAP THEN
  REWRITE_TAC[K_DISJ_IMP] THEN CONJ_TAC THEN MATCH_MP_TAC K_IMP_SWAP THEN
  ASM_MESON_TAC[CONJLIST_IMP_MEM; K_AXIOM_NOT; K_IFF_IMP1; K_IMP_TRANS]
 ;
  (* Case --> *)
  ASM_SIMP_TAC[] THEN EQ_TAC THENL
  [ASM_MESON_TAC[K_FREGE; CONJLIST_IMP_MEM]; INTRO_TAC "imp"] THEN
  CLAIM_TAC "hq1 | hq1" `MEM q1 w \/ MEM (Not q1) w` THENL
  [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
   ASM_MESON_TAC[CONJLIST_IMP_MEM; K_IMP_SWAP; K_ADD_ASSUM];
   ALL_TAC] THEN
  MATCH_MP_TAC K_SHUNT THEN MATCH_MP_TAC K_IMP_TRANS THEN
  EXISTS_TAC `q1 && Not q1` THEN CONJ_TAC THENL
  [ALL_TAC; MESON_TAC[K_NC_TH; K_IMP_TRANS; K_EX_FALSO_TH]] THEN
  MATCH_MP_TAC K_AND_INTRO THEN REWRITE_TAC[K_AND_RIGHT_TH] THEN
  ASM_MESON_TAC[CONJLIST_IMP_MEM; K_IMP_TRANS; K_AND_LEFT_TH]
 ;
  (* Case <-> *)
  ASM_SIMP_TAC[] THEN REMOVE_THEN "sub" (K ALL_TAC) THEN EQ_TAC THENL
  [MESON_TAC[K_FREGE; K_ADD_ASSUM; K_MODUSPONENS_TH;
             K_AXIOM_IFFIMP1; K_AXIOM_IFFIMP2];
   ALL_TAC] THEN
  INTRO_TAC "iff" THEN MATCH_MP_TAC K_IMP_TRANS THEN
  EXISTS_TAC `(q1 --> q2) && (q2 --> q1)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_AND_INTRO; MESON_TAC[K_IFF_DEF_TH; K_IFF_IMP2]] THEN
  CLAIM_TAC "rmk'"
    `!q. q SUBFORMULA p
         ==> (MEM (Not q) w <=> |-- (CONJLIST w --> Not q))` THENL
  [ASM_MESON_TAC[MAXIMAL_CONSISTENT_SUBFORMULA_MEM_NEG_EQ_DERIVABLE];
   ALL_TAC] THEN
  CLAIM_TAC "hq1 | hq1"
    `|-- (CONJLIST w --> q1) \/ |-- (CONJLIST w --> Not q1)` THENL
  [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
   ASM_MESON_TAC[K_IMP_SWAP; K_ADD_ASSUM];
   ALL_TAC] THEN
  CLAIM_TAC "hq2 | hq2"
    `|-- (CONJLIST w --> q2) \/ |-- (CONJLIST w --> Not q2)` THENL
  [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
   ASM_MESON_TAC[K_IMP_SWAP; K_ADD_ASSUM];
   ALL_TAC] THEN
  ASM_MESON_TAC[K_NC_TH; K_IMP_TRANS; K_AND_INTRO;
                K_EX_FALSO_TH; K_IMP_SWAP; K_SHUNT]
 ;
  (* Case Box *)
  INTRO_TAC "!a; a; sub; !w; w" THEN REWRITE_TAC[holds; IN_ELIM_THM] THEN
  CLAIM_TAC "suba" `a SUBFORMULA p` THENL
  [MATCH_MP_TAC SUBFORMULA_TRANS THEN
    EXISTS_TAC `Box a` THEN
    ASM_REWRITE_TAC[SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    ALL_TAC] THEN
  HYP_TAC "FRAME" (REWRITE_RULE[FRAME; IN_ELIM_THM]) THEN
  EQ_TAC THENL
  [INTRO_TAC "boxa; !w'; (maxw' subw') r" THEN
   HYP_TAC "a" (C MATCH_MP (ASSUME `a SUBFORMULA p`)) THEN
   HYP_TAC "a: +" (SPEC `w':form list`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o GSYM) THEN
   REMOVE_THEN "1" (MP_TAC o SPECL [`a: form`;`w: form list`]) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  INTRO_TAC "3" THEN
  REMOVE_THEN  "1" (MP_TAC o SPECL [`a:form`; `w:form list`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN INTRO_TAC "![w']; w'" THEN
  REMOVE_THEN "3" (MP_TAC o SPEC `w':form list`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  HYP_TAC "a" (C MATCH_MP (ASSUME `a SUBFORMULA p`)) THEN
  HYP_TAC "a: +" (SPEC `w':form list`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN (SUBST1_TAC o GSYM) THEN REWRITE_TAC[]
 ]);;

(* ------------------------------------------------------------------------- *)
(* Extension Lemma.                                                          *)
(* Every consistent list of formulae can be extended to a maximal consistent *)
(* list by a construction similar to Lindenbaum's extension.                 *)
(* ------------------------------------------------------------------------- *)

let EXTEND_MAXIMAL_CONSISTENT = prove
(`!p X. CONSISTENT X /\
        (!q. MEM q X ==> q SUBSENTENCE p)
        ==> ?M. MAXIMAL_CONSISTENT p M /\
                (!q. MEM q M ==> q SUBSENTENCE p) /\
                X SUBLIST M`,
 GEN_TAC THEN SUBGOAL_THEN
   `!L X. CONSISTENT X /\ NOREPETITION X /\
          (!q. MEM q X ==> q SUBSENTENCE p) /\
          (!q. MEM q L ==> q SUBFORMULA p) /\
          (!q. q SUBFORMULA p ==> MEM q L \/ MEM q X \/ MEM (Not q) X)
          ==> ?M. MAXIMAL_CONSISTENT p M /\
                  (!q. MEM q M ==> q SUBSENTENCE p) /\
                  X SUBLIST M`
   (LABEL_TAC "P") THENL
 [ALL_TAC;
  INTRO_TAC "![X']; cons' subf'" THEN
  DESTRUCT_TAC "@X. uniq sub1 sub2"
    (ISPEC `X':form list` EXISTS_NOREPETITION) THEN
  DESTRUCT_TAC "@L'. uniq L'" (SPEC `p:form` SUBFORMULA_LIST) THEN
  HYP_TAC "P: +" (SPECL[`L':form list`; `X:form list`]) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL [ASM_MESON_TAC[CONSISTENT_SUBLIST]; ALL_TAC] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[SUBLIST];
   ALL_TAC] THEN
  INTRO_TAC "@M. max sub" THEN EXISTS_TAC `M:form list` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBLIST_TRANS]] THEN
 LIST_INDUCT_TAC THENL
 [REWRITE_TAC[MEM] THEN INTRO_TAC "!X; X uniq max subf" THEN
  EXISTS_TAC `X:form list` THEN
  ASM_REWRITE_TAC[SUBLIST_REFL; MAXIMAL_CONSISTENT];
  ALL_TAC] THEN
 POP_ASSUM (LABEL_TAC "hpind") THEN REWRITE_TAC[MEM] THEN
 INTRO_TAC "!X; cons uniq qmem qmem' subf" THEN
 LABEL_ASM_CASES_TAC "hmemX" `MEM (h:form) X` THENL
 [REMOVE_THEN "hpind" (MP_TAC o SPEC `X:form list`) THEN
  ASM_MESON_TAC[]; ALL_TAC] THEN
 LABEL_ASM_CASES_TAC "nhmemX" `MEM (Not h) X` THENL
 [REMOVE_THEN "hpind" (MP_TAC o SPEC `X:form list`) THEN
  ASM_MESON_TAC[]; ALL_TAC] THEN
 LABEL_ASM_CASES_TAC "consh" `CONSISTENT (CONS (h:form) X)` THENL
 [REMOVE_THEN "hpind" (MP_TAC o SPEC `CONS (h:form) X`) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[NOREPETITION_CLAUSES; MEM] THEN
   CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
   ASM_MESON_TAC[SUBLIST; SUBFORMULA_IMP_SUBSENTENCE];
   ALL_TAC] THEN
  INTRO_TAC "@M. max sub" THEN EXISTS_TAC `M:form list` THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "sub" MP_TAC THEN
  REWRITE_TAC[SUBLIST; MEM] THEN MESON_TAC[];
  ALL_TAC] THEN
 REMOVE_THEN "hpind" (MP_TAC o SPEC `CONS (Not h) X`) THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[NOREPETITION_CLAUSES] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONSISTENT_EM]; ALL_TAC] THEN
  REWRITE_TAC[MEM] THEN ASM_MESON_TAC[SUBLIST; SUBSENTENCE_RULES];
  ALL_TAC] THEN
 INTRO_TAC "@M. max sub" THEN EXISTS_TAC `M:form list` THEN
 ASM_REWRITE_TAC[] THEN REMOVE_THEN "sub" MP_TAC THEN
 REWRITE_TAC[SUBLIST; MEM] THEN MESON_TAC[]);;

let NONEMPTY_MAXIMAL_CONSISTENT = prove
(`!p. ~ |-- p
      ==> ?M. MAXIMAL_CONSISTENT p M /\
              MEM (Not p) M /\
              (!q. MEM q M ==> q SUBSENTENCE p)`,
 INTRO_TAC "!p; p" THEN
 MP_TAC (SPECL [`p:form`; `[Not p]`] EXTEND_MAXIMAL_CONSISTENT) THEN
 ANTS_TAC THENL
 [CONJ_TAC THENL
  [REWRITE_TAC[CONSISTENT_SING] THEN ASM_MESON_TAC[K_DOUBLENEG_CL];
   ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[MEM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MESON_TAC[SUBFORMULA_IMP_NEG_SUBSENTENCE; SUBFORMULA_REFL];
  ALL_TAC] THEN
 STRIP_TAC THEN EXISTS_TAC `M:form list` THEN
 ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBLIST; MEM]);;

(* ------------------------------------------------------------------------- *)
(* Necessitations Lemmas.                                                    *)
(* See Boolos p.6-7 (pdf p.44-45).                                           *)
(* ------------------------------------------------------------------------- *)

 g `!p q. |-- (p --> q) ==> |-- ((Box p) --> (Box q)) `;;
 e (REPEAT GEN_TAC);;
 e (STRIP_TAC);;
 e (SUBGOAL_THEN `|-- (Box(p --> q) --> (Box p --> Box q)) ==> 
           |-- ((Box p) --> (Box q))`
                 (fun(th) -> (MATCH_MP_TAC th)));;
 e (CLAIM_TAC "asd" `|-- (Box (p --> q))`);;
   e (ASM_MESON_TAC[K_NECESSITATION]);;
 e (ASM_MESON_TAC[K_MODUSPONENS]);;
 e (REWRITE_TAC[K_AXIOM_BOXIMP]);;
 let LEMMA_BOX_1 = top_thm();;
 
 g `!p q. |-- (p <-> q) ==> |-- ((Box p) <-> (Box q)) `;;
 e (REPEAT GEN_TAC);;
 e (REWRITE_TAC[K_IFF_DEF]);;
 e (MESON_TAC[LEMMA_BOX_1]);;
 let LEMMA_BOX_2 = top_thm();;
 
 g `!p q. |-- (Box p && Box q) <=> |-- (Box (p && q))`;;
 e (MESON_TAC[K_BOX_AND; K_BOX_AND_INV]);;
 let LEMMA_BOX_3 = top_thm();;
 
 g `!X. |-- (Box (CONJLIST X)) <=> |-- (CONJLIST (MAP(Box) X))`;;
 e (LIST_INDUCT_TAC);;
   e (MESON_TAC[K_TRUTH_TH; MAP; CONJLIST; K_NECESSITATION]);;
 e (REWRITE_TAC[CONJLIST; MAP]);;
 e (COND_CASES_TAC);;
   e (FIRST_X_ASSUM (SUBST_VAR_TAC));;
   e (REWRITE_TAC[CONJLIST; MAP]);;
 e (COND_CASES_TAC);;
   e (CLAIM_TAC "asd" `t:(form)list = []`);;
     e (REMOVE_THEN "" MP_TAC);;
     e (REWRITE_TAC[MAP_EQ_NIL]);;
   e (ASM_MESON_TAC[]);;
 e (REWRITE_TAC[GSYM LEMMA_BOX_3]);;
 e (REWRITE_TAC[K_AND]);;
 e (ASM_REWRITE_TAC[]);;
 let LEMMA_BOX_4A = top_thm();;

g `!p q1 q2. |-- (q1 <-> q2) ==> |-- (p && q1 <-> p && q2)`;;
e (REPEAT STRIP_TAC);;
e (MATCH_MP_TAC K_MODUSPONENS);;
e (EXISTS_TAC `(q1 <-> q2)`);;
e (ASM_REWRITE_TAC[K_AND_SUBSTR_RIGHT_TH]);;
let K_AND_SUBSTR_RIGHT_TH_1 = top_thm();;

g `!X. |-- (Box (CONJLIST X) <-> CONJLIST (MAP(Box) X))`;;
e (LIST_INDUCT_TAC);;
  e (REWRITE_TAC[CONJLIST; MAP]);;
  e (REWRITE_TAC[K_IFF_DEF]);;
  e (CONJ_TAC);;
    e (MATCH_MP_TAC K_ADD_ASSUM);;
    e (REWRITE_TAC[K_TRUTH_TH]);;
  e (MATCH_MP_TAC K_ADD_ASSUM);;
  e (MATCH_MP_TAC K_NECESSITATION);;
  e (REWRITE_TAC[K_TRUTH_TH]);;
e (REWRITE_TAC[CONJLIST; MAP]);;
e (COND_CASES_TAC);;
  e (FIRST_X_ASSUM (SUBST_VAR_TAC));;
  e (REWRITE_TAC[CONJLIST; MAP]);;
  e (REWRITE_TAC[K_IFF_REFL_TH]);;
e (COND_CASES_TAC);;
  e (CLAIM_TAC "asd" `t:(form)list = []`);;
    e (REMOVE_THEN "" MP_TAC);;
    e (REWRITE_TAC[MAP_EQ_NIL]);;
  e (ASM_MESON_TAC[]);;
e (MATCH_MP_TAC K_IFF_TRANS);;
e (EXISTS_TAC `(Box h) && Box (CONJLIST t)`);;
e (CONJ_TAC);;
  r 1;;
    e (MATCH_MP_TAC K_AND_SUBSTR_RIGHT_TH_1);;
    e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[K_IFF_DEF]);;
e (REWRITE_TAC[K_BOX_AND_TH; K_BOX_AND_INV_TH]);;
let LEMMA_BOX_4 = top_thm();;

g `!p X. |-- (CONJLIST X --> p) ==> |-- (CONJLIST (MAP(Box) X) --> (Box p))`;;
e (REPEAT GEN_TAC);; 
e (STRIP_TAC);; 
e (CLAIM_TAC "asd" `|-- ((Box (CONJLIST X)) --> (Box p))`);; 
  e (MATCH_MP_TAC LEMMA_BOX_1);;
  e (ASM_REWRITE_TAC[]);;
e (MATCH_MP_TAC K_IMP_TRANS);;
e (EXISTS_TAC `Box CONJLIST X`);;
e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `|-- (CONJLIST (MAP (Box) X) <-> Box CONJLIST X)
          ==> |-- (CONJLIST (MAP (Box) X) --> Box CONJLIST X)`
                    (fun(th) -> MATCH_MP_TAC th));;
  e (MESON_TAC[K_IFF_DEF]);;
e (REWRITE_TAC[LEMMA_BOX_4; K_IFF_SYM]);;
let LEMMA_BOX_5 = top_thm();; 

(* ------------------------------------------------------------------------- *)
(* Accessibility lemma.                                                      *)
(* ------------------------------------------------------------------------- *)

let K_STANDARD_REL = new_definition
  `K_STANDARD_REL p w x <=>
   MAXIMAL_CONSISTENT p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
   MAXIMAL_CONSISTENT p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
   (!B. MEM (Box B) w ==> MEM B x)`;;

g `!p. ~ |-- p ==> FRAME ({M | MAXIMAL_CONSISTENT p M /\
                         (!q. MEM q M ==> q SUBSENTENCE p)},
                                           K_STANDARD_REL p)`;;
e (INTRO_TAC "!p; p");;
e (REWRITE_TAC[FRAME]);;
e (CONJ_TAC);; (* non empty *)
  e (REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM]);;
  e (ASM_MESON_TAC[NONEMPTY_MAXIMAL_CONSISTENT]);;
e (CONJ_TAC);; (* well define *)
  e (REWRITE_TAC[K_STANDARD_REL]);;
  e (SET_TAC[]);;
e (MATCH_MP_TAC FINITE_SUBSET);; (* finite *)
e (EXISTS_TAC `{l | NOREPETITION l /\
                  !q. MEM q l ==> q IN {q | q SUBSENTENCE p}}`);;
e (CONJ_TAC);;
  e (MATCH_MP_TAC FINITE_NOREPETITION);;
  e (POP_ASSUM_LIST (K ALL_TAC));;
  e (SUBGOAL_THEN `{q | q SUBSENTENCE p} =
        {q | q SUBFORMULA p} UNION IMAGE (Not) {q | q SUBFORMULA p}`
                  SUBST1_TAC);;
    e (REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_UNION;
                  FORALL_IN_GSPEC; FORALL_IN_IMAGE]);;
    e (REWRITE_TAC[IN_UNION; IN_ELIM_THM; SUBSENTENCE_RULES]);;
    e (GEN_TAC);;
    e (GEN_REWRITE_TAC LAND_CONV [SUBSENTENCE_CASES]);;
    e (ASM SET_TAC[]);;
  e (REWRITE_TAC[FINITE_UNION; FINITE_SUBFORMULA]);;
  e (MATCH_MP_TAC FINITE_IMAGE);;
  e (REWRITE_TAC[FINITE_SUBFORMULA]);;
e (ASM SET_TAC[MAXIMAL_CONSISTENT]);;
let K_MAXIMAL_CONSISTENT = top_thm ();;

g `!p l. MEM p (FLATMAP (\x. match x with Box c -> [c] | _ -> []) l) ==>
      MEM (Box p) l`;;
e (GEN_TAC);;
e (LIST_INDUCT_TAC);;
  e (REWRITE_TAC[MEM; FLATMAP]);;
e (PURE_REWRITE_TAC[FLATMAP]);;
e (PURE_REWRITE_TAC[MEM_APPEND]);;
e (PURE_ONCE_REWRITE_TAC[MESON[]`((a \/ b) ==> c) <=> 
              ((a ==> c) /\ (b ==> c)) `]);;
e CONJ_TAC;;
  r 1;;
  e (ASM IMP_REWRITE_TAC[MEM]);;
e (REWRITE_TAC[MEM]);;
e (ASSUME_TAC (MATCH_CONV `(match h with Box c -> [c] | _ -> [])`));;
e (REMOVE_THEN "" MP_TAC THEN COND_CASES_TAC);;
  e (POP_ASSUM (CHOOSE_THEN SUBST_VAR_TAC));;
  e (ASM_REWRITE_TAC[MEM]);;
  e (MESON_TAC[]);;
e (STRIP_TAC);;
e (FIRST_X_ASSUM(SUBST1_TAC));;
e (REWRITE_TAC[MEM]);;
let MEM_FLATMAP_LEMMA = top_thm();;

g `!p l. MEM p (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) l) ==>
      MEM p l`;;
e (GEN_TAC);;
e (LIST_INDUCT_TAC);;
  e (REWRITE_TAC[MEM; FLATMAP]);;
e (PURE_REWRITE_TAC[FLATMAP]);;
e (PURE_REWRITE_TAC[MEM_APPEND]);;
e (PURE_ONCE_REWRITE_TAC[MESON[]`((a \/ b) ==> c) <=> 
              ((a ==> c) /\ (b ==> c)) `]);;
e CONJ_TAC;;
  r 1;;
  e (ASM IMP_REWRITE_TAC[MEM]);;
e (REWRITE_TAC[MEM]);;
e (ASSUME_TAC (MATCH_CONV `(match h with Box c -> [Box c] | _ -> [])`));;
e (REMOVE_THEN "" MP_TAC THEN COND_CASES_TAC);;
  e (POP_ASSUM (CHOOSE_THEN SUBST_VAR_TAC));;
  e (ASM_REWRITE_TAC[MEM]);;
  e (MESON_TAC[]);;
e (STRIP_TAC);;
e (FIRST_X_ASSUM(SUBST1_TAC));;
e (REWRITE_TAC[MEM]);;
let MEM_FLATMAP_LEMMA_1 = top_thm();;

g `!w. |-- (CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
  -->
  CONJLIST (MAP (Box)
    (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)))`;;
e (LIST_INDUCT_TAC);;
  e (REWRITE_TAC[MEM; FLATMAP; MAP; K_IMP_REFL_TH]);;
e (REWRITE_TAC[FLATMAP; MAP_APPEND]);;
e (MATCH_MP_TAC K_IMP_TRANS);;
e (EXISTS_TAC 
     `CONJLIST (match h with Box c -> [Box c] | _ -> []) &&
      CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) t)`);;
e (CONJ_TAC);;
  e (MATCH_MP_TAC K_IFF_IMP1);;
  e (MATCH_ACCEPT_TAC CONJLIST_APPEND);;
e (MATCH_MP_TAC K_IMP_TRANS);;
e (EXISTS_TAC  
     `CONJLIST (MAP (Box) (match h with Box c -> [c] | _ -> [])) &&
      CONJLIST (MAP (Box)
       (FLATMAP (\x. match x with Box c -> [c] | _ -> []) t))`);;
e (CONJ_TAC);;
  r (1);;
  e (MATCH_MP_TAC K_IFF_IMP2);;
  e (MATCH_ACCEPT_TAC CONJLIST_APPEND);;
e (MATCH_MP_TAC K_AND_INTRO);;
e (CONJ_TAC);;
  r (1);;
  e (ASM_MESON_TAC[K_IMP_TRANS; K_AND_RIGHT_TH; MAP]);;
e (MATCH_MP_TAC K_IMP_TRANS);;
e (EXISTS_TAC `CONJLIST (match h with Box c -> [Box c] | _ -> [])`);;
e (CONJ_TAC);;
  e (MATCH_ACCEPT_TAC K_AND_LEFT_TH);;
e (POP_ASSUM (K ALL_TAC));;
e (STRUCT_CASES_TAC (SPEC `h:form` (cases "form")));;
e (REWRITE_TAC[distinctness "form"; MAP; K_IMP_REFL_TH]);;
e (REWRITE_TAC[distinctness "form"; MAP; K_IMP_REFL_TH]);;
e (REWRITE_TAC[distinctness "form"; MAP; K_IMP_REFL_TH]);;
e (REWRITE_TAC[distinctness "form"; MAP; K_IMP_REFL_TH]);;
e (REWRITE_TAC[distinctness "form"; MAP; K_IMP_REFL_TH]);;
e (REWRITE_TAC[distinctness "form"; MAP; K_IMP_REFL_TH]);;
e (REWRITE_TAC[distinctness "form"; MAP; K_IMP_REFL_TH]);;
e (REWRITE_TAC[distinctness "form"; MAP; K_IMP_REFL_TH]);;
e (REWRITE_TAC[distinctness "form"; MAP; K_IMP_REFL_TH]);;
let CONJLIST_FLATMAP_DOT_BOX_LEMMA = top_thm();;

g `!p X. |-- ((CONJLIST (CONS p X) --> False) <-> 
  (p && CONJLIST X) --> False)`;;
e (REPEAT GEN_TAC);;
e (MATCH_MP_TAC K_IMP_SUBST);;
e (ASM_REWRITE_TAC[K_IFF_REFL_TH; CONJLIST_CONS]);;
let CONJLIST_CONS_NOT = top_thm();;

g `!p X. (|-- ((CONJLIST (CONS p X) --> False)) <=> 
 (|-- ((p && CONJLIST X) --> False)))`;;
e (REPEAT GEN_TAC);;
e (ASM_MESON_TAC[CONJLIST_CONS_NOT; K_IFF]);;
let CONJLIST_CONS_NOT_TH = top_thm();;

g `!p q r. |-- (p && q --> r) <=> |-- (p --> q --> r)`;;
e (MESON_TAC[K_SHUNT;K_ANTE_CONJ]);;
let K_AND_IMP = top_thm();;

g `!p q. |-- ((Not p) --> q <-> (p --> False) --> q)`;;
e (REPEAT GEN_TAC);;
e (MATCH_MP_TAC K_IMP_SUBST);;
e (REWRITE_TAC[K_AXIOM_NOT; K_IFF_REFL_TH]);;
let K_NOT_IMP_ID = top_thm();;

g `!p q r. |-- (((Not p) --> q --> r) <-> ((p --> False) --> q --> r))`;;
e (REPEAT GEN_TAC);;
e (MATCH_MP_TAC K_IMP_SUBST);;
e (REWRITE_TAC[K_AXIOM_NOT; K_IFF_REFL_TH]);;
let K_NOT_IMP_ID_1 = top_thm();;

g `!p q r. |-- ((Not p) --> q --> r) <=> 
                        |-- ((p --> False) --> q --> r)`;;
e (REPEAT GEN_TAC);;
e (MESON_TAC[K_NOT_IMP_ID_1; K_IFF]);;
let K_NOT_IMP_ID_2 = top_thm();;

g `!q p. |-- (((Not q) && p) --> False)
                        <=> |-- ((q --> False) --> p --> False)`;;
e (REPEAT GEN_TAC);;
e (REWRITE_TAC[K_AND_IMP]);;
e (REWRITE_TAC[K_NOT_IMP_ID_2]);;
let K_NOT_IMP_False = top_thm();;

g `!p q. (|-- (p <-> q)) ==> (|-- (Not p) <=> |-- (Not q))`;;
e (MESON_TAC[K_IFF;K_NOT_SUBST]);;
let K_NOT_SUBST_1 = top_thm();;

g `!p q. |-- ((p --> q) --> False <-> Not (p --> q))`;;
e (MESON_TAC[K_AXIOM_NOT; K_IFF_SYM]);;
let K_NOT_IMP_ID_3 = top_thm();;

g `!p. |-- (Not p --> False) <=> |-- (Not (p --> False))`;;
e (GEN_TAC);;
e (MATCH_MP_TAC (MESON[]`!p q r. ((|-- p <=> |-- q) /\ (|-- q <=> |-- r)) ==> 
                    (|-- p <=> |-- r)`));;
e (EXISTS_TAC `Not Not p`);;
e (CONJ_TAC);;
  e (ASM_MESON_TAC[K_DOUBLENEG_CL; K_NOT_DEF]);;
e (SUBGOAL_THEN ` (|-- ((Not p) <-> (p --> False)))
              ==> (|-- (Not Not p) <=> |-- (Not (p --> False)))`
                      (fun(th) -> MATCH_MP_TAC th));;
  e (MESON_TAC[K_NOT_SUBST_1]);;
e (REWRITE_TAC[K_AXIOM_NOT]);;
let K_NOT_IMP_ID_4 = top_thm();;

g `!q p. |-- (Not q && p --> False) 
                        ==> |-- (p --> q)`;;
e (REPEAT GEN_TAC);;
e (REWRITE_TAC[K_NOT_IMP_False]);;
e (MATCH_MP_TAC (MESON[]`!p q r. ((|-- p ==> |-- q) /\ (|-- q ==> |-- r)) ==> 
                      (|-- p ==> |-- r)`));;
e (EXISTS_TAC `(((p --> q) --> False) --> False)`);;
e (REWRITE_TAC[K_IMP_FALSE_RULE]);;
e (REWRITE_TAC[GSYM K_NOT_DEF]);;
e (STRIP_TAC);;
e (MATCH_MP_TAC K_DOUBLENEG_CL);;
e (SIMP_TAC[K_NOT_DEF]);;
e (ASM_MESON_TAC[K_NOT_IMP_ID_4]);;
let K_NOT_IMP_ID_5 = top_thm();;

g `!p w q.
    ~ |-- p /\
    MAXIMAL_CONSISTENT p w /\
    (!q. MEM q w ==> q SUBSENTENCE p) /\
    Box q SUBFORMULA p ==>
    ((!x. K_STANDARD_REL p w x ==> MEM q x)
    <=> MEM (Box q) w)`;;
e (REPEAT GEN_TAC);;
e (REPEAT GEN_TAC THEN INTRO_TAC "p maxM maxw boxq");;
e (EQ_TAC);;
  r (1);;
  e (ASM_MESON_TAC[K_STANDARD_REL]);;
e (ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM]);;
e (INTRO_TAC "asd");;
e (REWRITE_TAC[NOT_FORALL_THM]);;
e (REWRITE_TAC[MESON[]`~(p ==> q) <=> (p /\ ~q)`]);;
e (REWRITE_TAC[K_STANDARD_REL]);;
e (CLAIM_TAC "consistent_X" 
              `CONSISTENT (CONS (Not q)
                (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w))`);;
  e (REFUTE_THEN MP_TAC);;
  e (INTRO_TAC "PA");;
  e (SUBGOAL_THEN `MEM (Box q) w ==> F` 
                            (fun(th) -> (MATCH_MP_TAC th)));;
    e (ASM_MESON_TAC[]);;
  e (REMOVE_THEN "PA" MP_TAC THEN REWRITE_TAC[CONSISTENT]);;
  e (INTRO_TAC "PA");;
  e (SUBGOAL_THEN 
        `|-- (CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
                  --> (Box q)) /\
            (!c. MEM c (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w) 
            ==> MEM (Box c) w ) /\
                  (Box q) SUBSENTENCE p
                          ==> MEM (Box q) w`
                          (fun(th) -> (MATCH_MP_TAC th)));;
    e (REPEAT STRIP_TAC);;
    e (MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA);;
    e (MAP_EVERY EXISTS_TAC[`p:form` ; 
              `(FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)`]);;
    e (ASM_REWRITE_TAC[MEM_FLATMAP_LEMMA_1]);;
  e (ASM IMP_REWRITE_TAC[MEM_FLATMAP_LEMMA; SUBFORMULA_IMP_SUBSENTENCE]);;
  e (REWRITE_TAC[CONJLIST_FLATMAP_DOT_BOX_LEMMA]);;
  e (MATCH_MP_TAC K_IMP_TRANS);;
  e (EXISTS_TAC `CONJLIST (MAP (Box)
          (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w))`);;
  e (REWRITE_TAC[CONJLIST_FLATMAP_DOT_BOX_LEMMA]);;
  e (MATCH_MP_TAC LEMMA_BOX_5);;
  e (REMOVE_THEN "PA" MP_TAC);;
  e (REWRITE_TAC[K_NOT_DEF]);;
  e (REWRITE_TAC[CONJLIST_CONS_NOT_TH]);;
  e (MESON_TAC[K_NOT_IMP_ID_5]);;
e (MP_TAC (SPECL
              [`p:form`;
               `CONS (Not q)
                  (FLATMAP (\x. match x with Box c -> [c] | _ -> []) w)`]
                              EXTEND_MAXIMAL_CONSISTENT));;
e (ANTS_TAC);;
  e (ASM_REWRITE_TAC[MEM]);;
  e (GEN_TAC THEN STRIP_TAC);;
  e (FIRST_X_ASSUM SUBST_VAR_TAC);;
  e (MATCH_MP_TAC SUBFORMULA_IMP_NEG_SUBSENTENCE);;
  e (HYP MESON_TAC "boxq"
        [SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]);;
e (CLAIM_TAC "boxq'" `MEM (Box q') (w:(form)list)`);;
  e (MATCH_MP_TAC MEM_FLATMAP_LEMMA);;
  e (ASM_REWRITE_TAC[]);;
e (CLAIM_TAC "boxq'sub" `Box (q':form) SUBSENTENCE p`);;
  e (ASM_MESON_TAC[]);;
e (HYP_TAC "boxq'sub" (REWRITE_RULE[SUBSENTENCE_CASES; distinctness "form"]));;
e (MATCH_MP_TAC SUBFORMULA_IMP_SUBSENTENCE);;
e (HYP MESON_TAC "boxq'sub"
    [SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]);;
e (INTRO_TAC "@X. maxX subX subl" THEN EXISTS_TAC `X:form list`);;
e (ASM_REWRITE_TAC[K_STANDARD_REL; NOT_IMP]);;
e (CONJ_TAC);;
  e (INTRO_TAC "!B; B");;
  e (HYP_TAC "subl" (REWRITE_RULE[SUBLIST]));;
  e (REMOVE_THEN "subl" MATCH_MP_TAC);;
  e (REWRITE_TAC[MEM; distinctness "form"; injectivity "form"]);;
  e (DISJ2_TAC THEN REWRITE_TAC[MEM_FLATMAP]);;
  e (EXISTS_TAC `Box B`);;
  e (ASM_REWRITE_TAC[MEM]);;
e (HYP_TAC "subl" (REWRITE_RULE[SUBLIST]));;
e (HYP_TAC "subl: +" (SPEC `Not q` o REWRITE_RULE[SUBLIST]));;
e (IMP_REWRITE_TAC[GSYM MAXIMAL_CONSISTENT_MEM_NOT]);;
e (STRIP_TAC);;
e (CONJ_TAC);;
  r 1;;
  e (MATCH_MP_TAC SUBFORMULA_TRANS);;
  e (EXISTS_TAC `Box (q:form)`);;
  e (ASM_REWRITE_TAC[]);;
  e (ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]);;
r 1;;
e (REMOVE_THEN "" MATCH_MP_TAC THEN REWRITE_TAC[MEM]);;
let ACCESSIBILITY_LEMMA = top_thm();;

g `!p w q.
    ~ |-- p /\
    MAXIMAL_CONSISTENT p w /\
    (!q. MEM q w ==> q SUBSENTENCE p) /\
    Box q SUBFORMULA p /\
    (!x. K_STANDARD_REL p w x ==> MEM q x)
    ==> MEM (Box q) w`;;
e (REPEAT STRIP_TAC);;
e (REMOVE_THEN "" MP_TAC);;
e (MATCH_MP_TAC EQ_IMP);;
e (MATCH_MP_TAC ACCESSIBILITY_LEMMA);;
e (ASM_REWRITE_TAC[]);;
let ACCESSIBILITY_LEMMA_1 = top_thm();;

(* ------------------------------------------------------------------------- *)
(* Modal completeness theorem for K.                                         *)
(* ------------------------------------------------------------------------- *)

g `!M p.
  ~(|-- p) /\
  MAXIMAL_CONSISTENT p M /\
  MEM (Not p) M /\
  (!q. MEM q M ==> q SUBSENTENCE p) ==>
  ~holds  ({M | MAXIMAL_CONSISTENT p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
          K_STANDARD_REL p) (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w) p M`;;
e (REPEAT GEN_TAC THEN STRIP_TAC);;
e (MP_TAC (ISPECL
    [`{M | MAXIMAL_CONSISTENT p M /\ (!q. MEM q M ==> q SUBSENTENCE p)}`;
      `K_STANDARD_REL p`;
      `p:form`;
      `\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w`;
      `p:form`] K_TRUTH_LEMMA));;
  e (ANTS_TAC);;
  e (ASM_REWRITE_TAC[SUBFORMULA_REFL; K_STANDARD_MODEL; K_STANDARD_FRAME]);;
  e (ASM_SIMP_TAC[K_MAXIMAL_CONSISTENT]);;
  e (REWRITE_TAC[IN_ELIM_THM]);;
  e (CONJ_TAC);;
    e (INTRO_TAC "!q w; boxq w subf");;
    e (EQ_TAC);;
      e (ASM_MESON_TAC[ACCESSIBILITY_LEMMA]);;
    e (INTRO_TAC "hp");;
    e (MATCH_MP_TAC ACCESSIBILITY_LEMMA_1);;
    e (EXISTS_TAC `p:form`);;
    e (ASM_REWRITE_TAC[]);;
  e (ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT_NC]);;
e (DISCH_THEN (MP_TAC o SPEC `M:form list`));;
e (ANTS_TAC);;
e (ASM_REWRITE_TAC[IN_ELIM_THM]);;
e (DISCH_THEN (SUBST1_TAC o GSYM));;
e (ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT_NC]);;
let K_COUNTERMODEL = top_thm();;

g `!p. ~(|-- p) ==> ~holds_in
          ({M | MAXIMAL_CONSISTENT p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
                                                        K_STANDARD_REL p) p`;;
e (INTRO_TAC "!p; Np");;
e (REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP; IN_ELIM_THM]);;
e (EXISTS_TAC `\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w`);;
e (DESTRUCT_TAC "@M. max mem subf"
      (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ |-- p`)));;
e (EXISTS_TAC `M:form list`);;
e (ASM_REWRITE_TAC[]);;
e (MATCH_MP_TAC K_COUNTERMODEL);;
e (ASM_REWRITE_TAC[]);;
let LEMMA_K_COUNTER = top_thm();;

g `!p. FRAME:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> |-- p`;;
e (GEN_TAC);;
e (GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM]);;
e (INTRO_TAC "p");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC `({M | MAXIMAL_CONSISTENT p M /\ 
                      (!q. MEM q M ==> q SUBSENTENCE p)},
                                          K_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP]);;
e (CONJ_TAC);;
  e (MATCH_MP_TAC K_MAXIMAL_CONSISTENT);;
  e (ASM_REWRITE_TAC[]);;
e (MATCH_MP_TAC LEMMA_K_COUNTER);;
e (ASM_REWRITE_TAC[]);;
let K_COMPLETENESS_THM = top_thm();;
