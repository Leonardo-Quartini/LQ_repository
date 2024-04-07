(* ------------------------------------------------------------------------- *)
(* Axioms of K.                                                              *)
(* ------------------------------------------------------------------------- *)

let Kaxiom_RULES,Kaxiom_INDUCT,Kaxiom_CASES = new_inductive_definition
  `(!p q. Kaxiom (p --> (q --> p))) /\
   (!p q r. Kaxiom ((p --> q --> r) --> (p --> q) --> (p --> r))) /\
   (!p. Kaxiom (((p --> False) --> False) --> p)) /\
   (!p q. Kaxiom ((p <-> q) --> p --> q)) /\
   (!p q. Kaxiom ((p <-> q) --> q --> p)) /\
   (!p q. Kaxiom ((p --> q) --> (q --> p) --> (p <-> q))) /\
    Kaxiom (True <-> False --> False) /\
   (!p. Kaxiom (Not p <-> p --> False)) /\
   (!p q. Kaxiom (p && q <-> (p --> q --> False) --> False)) /\
   (!p q. Kaxiom (p || q <-> Not(Not p && Not q))) /\
   (!p q. Kaxiom (Box (p --> q) --> Box p --> Box q))`;;

(* ------------------------------------------------------------------------- *)
(* Rules.                                                                    *)
(* ------------------------------------------------------------------------- *)

let Kproves_RULES,Kproves_INDUCT,Kproves_CASES = new_inductive_definition
  `(!p. Kaxiom p ==> |-- p) /\
   (!p q. |-- (p --> q) /\ |-- p ==> |-- q) /\
   (!p. |-- p ==> |-- (Box p))`;;

(* ------------------------------------------------------------------------- *)
(* The primitive basis, separated into its named components.                 *)
(* ------------------------------------------------------------------------- *)

let K_AXIOM_ADDIMP = prove
 (`!p q. |-- (p --> (q --> p))`,
  MESON_TAC[Kproves_RULES; Kaxiom_RULES]);;

let K_AXIOM_DISTRIBIMP = prove
 (`!p q r. |-- ((p --> q --> r) --> (p --> q) --> (p --> r))`,
  MESON_TAC[Kproves_RULES; Kaxiom_RULES]);;

let K_AXIOM_DOUBLENEG = prove
 (`!p. |-- (((p --> False) --> False) --> p)`,
  MESON_TAC[Kproves_RULES; Kaxiom_RULES]);;

let K_AXIOM_IFFIMP1 = prove
 (`!p q. |-- ((p <-> q) --> p --> q)`,
  MESON_TAC[Kproves_RULES; Kaxiom_RULES]);;

let K_AXIOM_IFFIMP2 = prove
 (`!p q. |-- ((p <-> q) --> q --> p)`,
  MESON_TAC[Kproves_RULES; Kaxiom_RULES]);;

let K_AXIOM_IMPIFF = prove
 (`!p q. |-- ((p --> q) --> (q --> p) --> (p <-> q))`,
  MESON_TAC[Kproves_RULES; Kaxiom_RULES]);;

let K_AXIOM_TRUE = prove
 (`|-- (True <-> (False --> False))`,
  MESON_TAC[Kproves_RULES; Kaxiom_RULES]);;

let K_AXIOM_NOT = prove
 (`!p. |-- (Not p <-> (p --> False))`,
  MESON_TAC[Kproves_RULES; Kaxiom_RULES]);;

let K_AXIOM_AND = prove
 (`!p q. |-- ((p && q) <-> (p --> q --> False) --> False)`,
  MESON_TAC[Kproves_RULES; Kaxiom_RULES]);;

let K_AXIOM_OR = prove
 (`!p q. |-- ((p || q) <-> Not(Not p && Not q))`,
  MESON_TAC[Kproves_RULES; Kaxiom_RULES]);;

let K_AXIOM_BOXIMP = prove
  (`!p q. |-- (Box (p --> q) --> Box p --> Box q)`,
   MESON_TAC[Kproves_RULES; Kaxiom_RULES]);;

let K_MODUSPONENS = prove
 (`!p. |-- (p --> q) /\ |-- p ==> |-- q`,
  MESON_TAC[Kproves_RULES]);;

let K_NECESSITATION = prove
 (`!p. |-- p ==> |-- (Box p)`,
  MESON_TAC[Kproves_RULES]);;

(* ------------------------------------------------------------------------- *)
(* Some purely propositional schemas and derived rules.                      *)
(* ------------------------------------------------------------------------- *)

let K_IFF_IMP1 = prove 
 (`!p q. |-- (p <-> q) ==> |-- (p --> q)`,
 MESON_TAC[K_MODUSPONENS; K_AXIOM_IFFIMP1]);;

let K_IFF_IMP2 = prove
 (`!p q. |-- (p <-> q) ==> |-- (q --> p)`,
  MESON_TAC[K_MODUSPONENS; K_AXIOM_IFFIMP2]);;

let K_IMP_ANTISYM = prove 
 (`!p q. |-- (p --> q) /\ |-- (q --> p) ==> |-- (p <-> q)`,
 MESON_TAC[K_MODUSPONENS; K_AXIOM_IMPIFF]);;

let K_ADD_ASSUM = prove
 (`!p q. |-- q ==> |-- (p --> q)`,
 MESON_TAC[K_MODUSPONENS; K_AXIOM_ADDIMP]);;

let K_IMP_REFL_TH = prove
 (`!p. |-- (p --> p)`,
 MESON_TAC[K_MODUSPONENS; K_AXIOM_DISTRIBIMP; K_AXIOM_ADDIMP]);;

let K_IMP_ADD_ASSUM = prove 
 (`!p q r. |-- (q --> r) ==> |-- ((p --> q) --> (p --> r))`,
 MESON_TAC[K_MODUSPONENS; K_AXIOM_DISTRIBIMP; K_ADD_ASSUM]);;

let K_IMP_UNDUPLICATE = prove
 (`!p q. |-- (p --> p --> q) ==> |-- (p --> q)`,
 MESON_TAC[K_MODUSPONENS; K_AXIOM_DISTRIBIMP; K_IMP_REFL_TH]);;

let K_IMP_TRANS = prove
 (`!p q. |-- (p --> q) /\ |-- (q --> r) ==> |-- (p --> r)`,
 MESON_TAC[K_MODUSPONENS; K_IMP_ADD_ASSUM]);;

let K_IMP_SWAP = prove
 (`!p q r. |-- (p --> q --> r) ==> |-- (q --> p --> r)`,
 MESON_TAC[K_IMP_TRANS; K_AXIOM_ADDIMP; K_MODUSPONENS; K_AXIOM_DISTRIBIMP]);;

let K_IMP_TRANS_CHAIN = prove
 (`!p q1 q2 r. |-- (p --> q1) /\ |-- (p --> q2) /\ |-- (q1 --> q2 --> r)
 ==> |-- (p --> r)`,
 MESON_TAC[K_IMP_TRANS; K_IMP_SWAP; K_IMP_UNDUPLICATE]);;

let K_IMP_TRANS_TH = prove
 (`!p q r. |-- ((q --> r) --> (p --> q) --> (p --> r))`,
 MESON_TAC[K_IMP_TRANS; K_AXIOM_ADDIMP; K_AXIOM_DISTRIBIMP]);;

let K_IMP_ADD_CONCL = prove
 (`!p q r. |-- (p --> q) ==> |-- ((q --> r) --> (p --> r))`,
 MESON_TAC[K_MODUSPONENS; K_IMP_SWAP; K_IMP_TRANS_TH]);;

let K_IMP_TRANS_2 = prove
 (`!p q r s. |-- (p --> q --> r) /\ |-- (r --> s) ==> |-- (p --> q --> s)`,
 MESON_TAC[K_IMP_ADD_ASSUM; K_MODUSPONENS; K_IMP_TRANS_TH]);;

let K_IMP_SWAP_TH = prove
 (`!p q r. |-- ((p --> q --> r) --> (q --> p --> r))`,
 MESON_TAC[K_IMP_TRANS; K_AXIOM_DISTRIBIMP; K_IMP_ADD_CONCL; K_AXIOM_ADDIMP]);;

let K_CONTRAPOS = prove
 (`!p q. |-- (p --> q) ==> |-- (Not q --> Not p)`,
 MESON_TAC[K_IMP_TRANS; K_IFF_IMP1; K_AXIOM_NOT; K_IMP_ADD_CONCL; K_IFF_IMP2]);;

let K_IMP_TRUE_FALSE_TH = prove
 (`!p q. |-- ((q --> False) --> p --> (p --> q) --> False)`,
 MESON_TAC[K_IMP_TRANS; K_IMP_TRANS_TH; K_IMP_SWAP_TH]);;

let K_IMP_INSERT = prove
 (`!p q r. |-- (p --> r) ==> |-- (p --> q --> r)`,
 MESON_TAC[K_IMP_TRANS; K_AXIOM_ADDIMP]);;

let K_IMP_MONO_TH = prove
 (`|-- ((p' --> p) --> (q --> q') --> (p --> q) --> (p' --> q'))`,
 MESON_TAC[K_IMP_TRANS; K_IMP_SWAP; K_IMP_TRANS_TH]);;

let K_EX_FALSO_TH = prove
 (`!p. |-- (False --> p)`,
 MESON_TAC[K_IMP_TRANS; K_AXIOM_ADDIMP; K_AXIOM_DOUBLENEG]);;

let K_EX_FALSO = prove
 (`!p. |-- False ==> |-- p`,
 MESON_TAC[K_EX_FALSO_TH; K_MODUSPONENS]);;

let K_IMP_CONTR_TH = prove
 (`!p q. |-- ((p --> False) --> (p --> q))`,
 MESON_TAC[K_IMP_ADD_ASSUM; K_EX_FALSO_TH]);;

let K_CONTRAD = prove
 (`!p. |-- ((p --> False) --> p) ==> |-- p`,
 MESON_TAC[K_MODUSPONENS; K_AXIOM_DISTRIBIMP; K_IMP_REFL_TH; 
 K_AXIOM_DOUBLENEG]);;

let K_BOOL_CASES = prove
 (`!p q. |-- (p --> q) /\ |-- ((p --> False) --> q) ==> |-- q`,
 MESON_TAC[K_CONTRAD; K_IMP_TRANS; K_IMP_ADD_CONCL]);;

let K_IMP_FALSE_RULE = prove
 (`!p q r. |-- ((q --> False) --> p --> r)
      ==> |-- (((p --> q) --> False) --> r)`,
 MESON_TAC[K_IMP_ADD_CONCL; K_IMP_ADD_ASSUM; K_EX_FALSO_TH; K_AXIOM_ADDIMP; 
           K_IMP_SWAP; K_IMP_TRANS; K_AXIOM_DOUBLENEG; K_IMP_UNDUPLICATE]);;

let K_IMP_TRUE_RULE = prove
 (`!p q r. |-- ((p --> False) --> r) /\ |-- (q --> r)
            ==> |-- ((p --> q) --> r)`,
 MESON_TAC[K_IMP_INSERT; K_IMP_SWAP; K_MODUSPONENS; K_IMP_TRANS_TH; 
           K_BOOL_CASES]);;

let K_TRUTH_TH = prove
 (`|-- True`,
 MESON_TAC[K_MODUSPONENS; K_AXIOM_TRUE; K_IMP_REFL_TH; K_IFF_IMP2]);;

let K_AND_LEFT_TH = prove
 (`!p q. |-- (p && q --> p)`,
 MESON_TAC[K_IMP_ADD_ASSUM; K_AXIOM_ADDIMP; K_IMP_TRANS; K_IMP_ADD_CONCL;
           K_AXIOM_DOUBLENEG; K_IMP_TRANS; K_IFF_IMP1; K_AXIOM_AND]);;

let K_AND_RIGHT_TH = prove
 (`!p q. |-- (p && q --> q)`,
 MESON_TAC[K_AXIOM_ADDIMP; K_IMP_TRANS; K_IMP_ADD_CONCL; K_AXIOM_DOUBLENEG;
           K_IFF_IMP1; K_AXIOM_AND]);;

let K_AND_PAIR_TH = prove
 (`!p q. |-- (p --> q --> p && q)`,
 MESON_TAC[K_IFF_IMP2; K_AXIOM_AND; K_IMP_SWAP_TH; K_IMP_ADD_ASSUM;
           K_IMP_TRANS_2; K_MODUSPONENS; K_IMP_SWAP; K_IMP_REFL_TH]);;

let K_AND = prove
 (`!p q. |-- (p && q) <=> |-- p /\ |-- q`,
 MESON_TAC[K_AND_LEFT_TH; K_AND_RIGHT_TH; K_AND_PAIR_TH; K_MODUSPONENS]);;

let K_AND_ELIM = prove
 (`!p q r. |-- (r --> p && q) ==> |-- (r --> q)  /\ |-- (r --> p)`,
 MESON_TAC[K_AND_LEFT_TH; K_AND_RIGHT_TH; K_IMP_TRANS]);;

let K_SHUNT = prove
 (`!p q r. |-- (p && q --> r) ==> |-- (p --> q --> r)`,
 MESON_TAC[K_MODUSPONENS; K_IMP_ADD_ASSUM; K_AND_PAIR_TH]);;

let K_ANTE_CONJ = prove
 (`!p q r. |-- (p --> q --> r) ==> |-- (p && q --> r)`,
 MESON_TAC[K_IMP_TRANS_CHAIN; K_AND_LEFT_TH; K_AND_RIGHT_TH]);;

let K_MODUSPONENS_TH = prove
 (`!p q. |-- ((p --> q) && p --> q)`,
 MESON_TAC[K_IMP_REFL_TH; K_ANTE_CONJ]);;

let K_NOT_NOT_FALSE_TH = prove
 (`!p. |-- ((p --> False) --> False <-> p)`,
 MESON_TAC[K_IMP_ANTISYM; K_AXIOM_DOUBLENEG; K_IMP_SWAP; K_IMP_REFL_TH]);;

let K_IFF_SYM = prove
 (`!p q. |-- (p <-> q) <=> |-- (q <-> p)`,
 MESON_TAC[K_IFF_IMP1; K_IFF_IMP2; K_IMP_ANTISYM]);;

let K_IFF_TRANS = prove
 (`!p q r. |-- (p <-> q) /\ |-- (q <-> r) ==> |-- (p <-> r)`,
 MESON_TAC[K_IFF_IMP1; K_IFF_IMP2; K_IMP_TRANS; K_IMP_ANTISYM]);;

let K_NOT_NOT_TH = prove
 (`!p. |-- (Not (Not p) <-> p)`,
 MESON_TAC[K_IFF_TRANS; K_NOT_NOT_FALSE_TH; K_AXIOM_NOT; K_IMP_ANTISYM; 
           K_IMP_ADD_CONCL; K_IFF_IMP1; K_IFF_IMP2]);;

let K_CONTRAPOS_EQ = prove
 (`!p q. |-- (Not p --> Not q) <=> |-- (q --> p)`,
 MESON_TAC[K_CONTRAPOS; K_NOT_NOT_TH; K_IFF_IMP1; K_IFF_IMP2; K_IMP_TRANS]);;

let K_OR_LEFT_TH = prove
 (`!p q. |-- (q --> p || q)`,
 MESON_TAC[K_IMP_TRANS; K_NOT_NOT_TH; K_IFF_IMP2; K_AND_RIGHT_TH; K_CONTRAPOS;
           K_AXIOM_OR]);;

let K_OR_RIGHT_TH = prove
 (`!p q. |-- (p --> p || q)`,
 MESON_TAC[K_IMP_TRANS; K_NOT_NOT_TH; K_IFF_IMP2; K_AND_LEFT_TH; K_CONTRAPOS;
           K_AXIOM_OR]);;

let K_ANTE_DISJ = prove
 (`!p q r. |-- (p --> r) /\ |-- (q --> r)
            ==> |-- (p || q --> r)`,
 REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM K_CONTRAPOS_EQ] THEN
 MESON_TAC[K_IMP_TRANS; K_IMP_TRANS_CHAIN; K_AND_PAIR_TH; K_CONTRAPOS_EQ;
           K_NOT_NOT_TH; K_AXIOM_OR; K_IFF_IMP1; K_IFF_IMP2; K_IMP_TRANS]);;

let K_IFF_DEF_TH = prove
 (`!p q. |-- ((p <-> q) <-> (p --> q) && (q --> p))`,
 MESON_TAC[K_IMP_ANTISYM; K_IMP_TRANS_CHAIN; K_AXIOM_IFFIMP1; K_AXIOM_IFFIMP2;
           K_AND_PAIR_TH; K_AXIOM_IMPIFF; K_IMP_TRANS_CHAIN; K_AND_LEFT_TH;
           K_AND_RIGHT_TH]);;

let K_IFF_REFL_TH = prove
 (`!p. |-- (p <-> p)`,
 MESON_TAC[K_IMP_ANTISYM; K_IMP_REFL_TH]);;

let K_IMP_BOX = prove
 (`!p q. |-- (p --> q) ==> |-- (Box p --> Box q)`,
 MESON_TAC[K_MODUSPONENS; K_NECESSITATION; K_AXIOM_BOXIMP]);;

let K_IMP_BOX2 = prove
(`!p q. |-- (Box (p --> q)) ==> |-- (Box p --> Box q)`,
MESON_TAC[K_MODUSPONENS; K_AXIOM_BOXIMP]);;

let K_BOX_MODUSPONENS = prove
 (`!p q. |-- (p --> q) /\ |-- (Box p) ==> |-- (Box q)`,
 MESON_TAC[K_IMP_BOX; K_MODUSPONENS]);;

let K_BOX_AND = prove
 (`!p q. |-- (Box(p && q)) ==> |-- (Box p && Box q)`,
 MESON_TAC[K_AND_LEFT_TH; K_AND_RIGHT_TH; K_IMP_BOX; K_BOX_MODUSPONENS; 
           K_AND]);;

let K_BOX_AND_INV = prove
 (`!p q. |-- (Box p && Box q) ==> |-- (Box (p && q))`,
 MESON_TAC[K_AND_PAIR_TH; K_IMP_BOX; K_AXIOM_BOXIMP; K_IMP_TRANS; K_ANTE_CONJ; 
           K_MODUSPONENS]);;

let K_AND_COMM = prove
 (`!p q . |-- (p && q) <=> |-- (q && p)`,
 MESON_TAC[K_AND]);;

let K_AND_ASSOC = prove
 (`!p q r. |-- ((p && q) && r) <=> |-- (p && (q && r))`,
 MESON_TAC[K_AND]);;

let K_DISJ_IMP = prove
 (`!p q r. |-- (p || q --> r) <=> |-- (p --> r) /\ |-- (q --> r)`,
 MESON_TAC[K_ANTE_DISJ; K_OR_RIGHT_TH; K_OR_LEFT_TH; K_IMP_TRANS]);;

let K_OR_ELIM = prove
 (`!p q r. |-- (p || q) /\ |-- (p --> r) /\ |-- (q --> r) ==> |-- r`,
 MESON_TAC[K_DISJ_IMP; K_MODUSPONENS]);;

let K_OR_COMM = prove
 (`!p q . |-- (p || q) <=> |-- (q || p)`,
 MESON_TAC[K_OR_RIGHT_TH; K_OR_LEFT_TH; K_MODUSPONENS; K_DISJ_IMP]);;

let K_OR_ASSOC = prove
 (`!p q r. |-- ((p || q) || r) <=> |-- (p || (q || r))`,
 MESON_TAC[K_OR_RIGHT_TH; K_OR_LEFT_TH; K_MODUSPONENS; K_DISJ_IMP]);;

let K_OR_INTROR = prove
 (`!p q. |-- q ==> |-- (p || q)`,
 MESON_TAC[K_OR_LEFT_TH; K_MODUSPONENS]);;

let K_OR_INTROL = prove
 (`!p q. |-- p ==> |-- (p || q)`,
 MESON_TAC[K_OR_RIGHT_TH; K_MODUSPONENS]);;

let K_OR_TRANSL= prove
 (`!p q r. |-- (p --> q) ==> |-- (p --> q || r)`,
 MESON_TAC[K_OR_RIGHT_TH; K_IMP_TRANS]);;

let K_OR_TRANSR = prove
 (`!p q r. |-- (p --> r) ==> |-- (p --> q || r)`,
 MESON_TAC[K_OR_LEFT_TH; K_IMP_TRANS]);;

let K_FREGE = prove
 (`!p q r. |-- (p --> q --> r) /\ |-- (p --> q) ==> |-- (p --> r)`,
 MESON_TAC[K_AXIOM_DISTRIBIMP; K_MODUSPONENS; K_SHUNT; K_ANTE_CONJ]);;

let K_AND_INTRO = prove
 (`!p q r. |-- (p --> q) /\ |-- (p --> r) ==> |-- (p --> q && r)`,
 MESON_TAC[K_AND_PAIR_TH; K_IMP_TRANS_CHAIN]);;

let K_NOT_DEF = prove
 (`!p. |-- (Not p) <=> |-- (p --> False)`,
 MESON_TAC[K_AXIOM_NOT; K_MODUSPONENS; K_IFF_IMP1; K_IFF_IMP2]);;

let K_NC = prove 
 (`!p. |-- (p  && Not p) <=> |-- False`,
 MESON_TAC[K_NOT_DEF; K_MODUSPONENS; K_AND; K_EX_FALSO]);;

let K_NC_TH = prove
 (`!p. |-- (p && Not p --> False)`,
 MESON_TAC[K_ANTE_CONJ; K_IMP_SWAP; K_AXIOM_NOT; K_AXIOM_IFFIMP1; 
           K_MODUSPONENS]);;

let K_IMP_CLAUSES = prove 
 (`(!p. |-- (p --> True)) /\
 (!p. |-- (p --> False) <=> |-- (Not p)) /\
 (!p. |-- (True --> p) <=> |-- p) /\
 (!p. |-- (False --> p))`,
 SIMP_TAC[K_TRUTH_TH; K_ADD_ASSUM; K_NOT_DEF; K_EX_FALSO_TH] THEN GEN_TAC 
 THEN EQ_TAC THENL [MESON_TAC[K_MODUSPONENS; K_TRUTH_TH];
 MESON_TAC[K_ADD_ASSUM]]);;

let K_AND_LEFT_TRUE_TH = prove
 (`!p. |-- (True && p <-> p)`,
 GEN_TAC THEN MATCH_MP_TAC K_IMP_ANTISYM THEN CONJ_TAC THENL
 [MATCH_ACCEPT_TAC K_AND_RIGHT_TH; ALL_TAC] THEN
 MATCH_MP_TAC K_AND_INTRO THEN REWRITE_TAC[K_IMP_REFL_TH; K_IMP_CLAUSES]);;

let K_OR_AND_DISTR = prove
 (`!p q r. |-- ((p || q) && r) ==> |-- ((p && r) || (q && r))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[K_AND] THEN STRIP_TAC THEN
  MATCH_MP_TAC K_OR_ELIM THEN EXISTS_TAC `p:form` THEN
  EXISTS_TAC `q :form` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_OR_TRANSL THEN MATCH_MP_TAC K_AND_INTRO THEN
   REWRITE_TAC[K_IMP_REFL_TH] THEN ASM_SIMP_TAC[K_ADD_ASSUM];
   MATCH_MP_TAC K_OR_TRANSR THEN MATCH_MP_TAC K_AND_INTRO THEN
   REWRITE_TAC[K_IMP_REFL_TH] THEN ASM_SIMP_TAC[K_ADD_ASSUM]]);;

let K_AND_OR_DISTR = prove
 (`!p q r. |-- ((p && q) || r) ==> |-- ((p || r) && (q || r))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[K_AND] THEN DISCH_TAC THEN
  CONJ_TAC THEN MATCH_MP_TAC K_OR_ELIM THEN
  MAP_EVERY EXISTS_TAC [`p && q`; `r:form`] THEN
  ASM_REWRITE_TAC[K_OR_LEFT_TH] THEN MATCH_MP_TAC K_OR_TRANSL THEN
  ASM_REWRITE_TAC[K_AND_LEFT_TH; K_AND_RIGHT_TH]);;

let K_OR_AND_DISTR_INV = prove
 (`!p q r. |-- ((p && r) || (q && r)) ==> |-- ((p || q) && r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC K_OR_ELIM THEN
  MAP_EVERY EXISTS_TAC [`p && r`; `q && r`] THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM (K ALL_TAC) THEN CONJ_TAC THEN MATCH_MP_TAC K_AND_INTRO THEN
  CONJ_TAC THEN REWRITE_TAC[K_AND_LEFT_TH; K_AND_RIGHT_TH] THENL
  [MATCH_MP_TAC K_OR_TRANSL THEN MATCH_ACCEPT_TAC K_AND_LEFT_TH;
   MATCH_MP_TAC K_OR_TRANSR THEN MATCH_ACCEPT_TAC K_AND_LEFT_TH]);;

let K_OR_AND_DISTR_EQUIV = prove
(`!p q r. |-- ((p || q) && r) <=> |-- ((p && r) || (q && r))`,
 MESON_TAC[K_OR_AND_DISTR; K_OR_AND_DISTR_INV]);;

let K_AND_OR_DISTR_INV_PRELIM = prove
 (`!p q r. |-- ((p || r) && (q || r)) ==> |-- (q --> (p && q) || r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[K_AND] THEN INTRO_TAC "pr qr" THEN
  MATCH_MP_TAC (SPECL [`p:form`; `r:form`] K_OR_ELIM) THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "pr" (K ALL_TAC) THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_SHUNT THEN MATCH_ACCEPT_TAC K_OR_RIGHT_TH; ALL_TAC] THEN
  MATCH_MP_TAC K_IMP_INSERT THEN MATCH_ACCEPT_TAC K_OR_LEFT_TH);;

let K_AND_OR_DISTR_INV = prove
 (`!p q r. |-- ((p || r) && (q || r)) ==> |-- ((p && q) || r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[K_AND] THEN INTRO_TAC "pr qr" THEN
  MATCH_MP_TAC (SPECL [`p:form`; `r:form`] K_OR_ELIM) THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "pr" (K ALL_TAC) THEN
  REWRITE_TAC[K_OR_LEFT_TH] THEN
  MATCH_MP_TAC (SPECL [`q:form`; `r:form`] K_OR_ELIM) THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "qr" (K ALL_TAC) THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_IMP_SWAP THEN MATCH_MP_TAC K_SHUNT THEN
   MATCH_ACCEPT_TAC K_OR_RIGHT_TH;
   MATCH_MP_TAC K_IMP_INSERT THEN MATCH_ACCEPT_TAC K_OR_LEFT_TH]);;

let K_AND_OR_DISTR_EQUIV = prove
 (`!p q r. |-- ((p && q) || r) <=> |-- ((p || r) && (q || r))`,
  MESON_TAC[K_AND_OR_DISTR; K_AND_OR_DISTR_INV]);;

let K_DOUBLENEG_CL = prove
 (`!p. |-- (Not(Not p)) ==> |-- p`,
 MESON_TAC[K_NOT_NOT_TH; K_MODUSPONENS; K_IFF_IMP1; K_IFF_IMP2]);;

let K_DOUBLENEG = prove
 (`!p. |-- p ==> |-- (Not(Not p))`,
  MESON_TAC[K_NOT_NOT_TH; K_MODUSPONENS; K_IFF_IMP1; K_IFF_IMP2]);;

let K_AND_EQ_OR = prove
 (`!p q. |-- (p || q) <=> |-- (Not(Not p && Not q))`,
  MESON_TAC[K_MODUSPONENS; K_AXIOM_OR; K_IFF_IMP1; K_IFF_IMP2]);;

let K_TND_TH = prove
 (`!p. |-- (p || Not p)`,
  GEN_TAC THEN REWRITE_TAC[K_AND_EQ_OR] THEN
  REWRITE_TAC[K_NOT_DEF] THEN MESON_TAC[K_NC_TH]);;

let K_IFF_MP = prove
 (`!p q. |-- (p <-> q) /\ |-- p ==> |-- q`,
  MESON_TAC[K_IFF_IMP1; K_MODUSPONENS]);;

let K_AND_SUBST = prove
 (`!p p' q q'. |-- (p <-> p') /\ |-- (q <-> q')
               ==> (|-- (p && q) <=> |-- (p' && q'))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[K_AND] THEN
  ASM_MESON_TAC[K_IFF_MP; K_IFF_SYM]);;

let K_IMP_MONO_TH_1 = prove
 (`!p p' q q'. |-- ((p' --> p) && (q --> q') --> (p --> q) --> (p' --> q'))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K_ANTE_CONJ THEN
  MATCH_ACCEPT_TAC K_IMP_MONO_TH);;

let K_IMP_MONO_TH_2 = prove
 (`!p p' q q'. |-- (p' --> p) /\ |-- (q --> q')
               ==> |-- ((p --> q) --> (p' --> q'))`,
  REWRITE_TAC[GSYM K_AND] THEN MESON_TAC[K_MODUSPONENS; K_IMP_MONO_TH_1]);;

let K_IFF = prove
 (`!p q. |-- (p <-> q) ==> (|-- p <=> |-- q)`,
  MESON_TAC[K_IFF_IMP1; K_IFF_IMP2; K_MODUSPONENS]);;

let K_IFF_DEF = prove
 (`!p q. |-- (p <-> q) <=> |-- (p --> q) /\ |-- (q --> p)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [MESON_TAC[K_IFF_IMP1; K_IFF_IMP2];
   MATCH_ACCEPT_TAC K_IMP_ANTISYM]);;

let K_NOT_SUBST = prove
 (`!p q. |-- (p <-> q) ==> |-- (Not p <-> Not q)`,
  MESON_TAC[K_IFF_DEF; K_IFF_IMP2; K_CONTRAPOS]);;

let K_AND_RIGHT_TRUE_TH = prove
 (`!p. |-- (p && True <-> p)`,
  GEN_TAC THEN REWRITE_TAC[K_IFF_DEF] THEN CONJ_TAC THENL
  [MATCH_ACCEPT_TAC K_AND_LEFT_TH; ALL_TAC] THEN
  MATCH_MP_TAC K_AND_INTRO THEN REWRITE_TAC[K_IMP_REFL_TH] THEN
  MATCH_MP_TAC K_ADD_ASSUM THEN
  MATCH_ACCEPT_TAC K_TRUTH_TH);;

let K_AND_COMM_TH = prove
 (`!p q. |-- (p && q <-> q && p)`,
  SUBGOAL_THEN `!p q. |-- (p && q --> q && p)`
    (fun th -> MESON_TAC[th; K_IFF_DEF]) THEN
  MESON_TAC[K_AND_INTRO; K_AND_LEFT_TH; K_AND_RIGHT_TH]);;

let K_AND_ASSOC_TH = prove
 (`!p q r. |-- ((p && q) && r <-> p && (q && r))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K_IMP_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC K_AND_INTRO THEN
  MESON_TAC[K_AND_LEFT_TH; K_AND_RIGHT_TH; K_IMP_TRANS; K_AND_INTRO]);;

let K_AND_SUBST_TH = prove
 (`!p p' q q'. |-- (p <-> p') /\ |-- (q <-> q')
               ==> |-- (p && q <-> p' && q')`,
  SUBGOAL_THEN
    `!p p' q q'. |-- (p <-> p') /\ |-- (q <-> q')
                 ==> |-- (p && q --> p' && q')`
    (fun th -> MESON_TAC[th; K_IFF_DEF]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC K_AND_INTRO THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `p:form` THEN
   REWRITE_TAC[K_AND_LEFT_TH] THEN ASM_SIMP_TAC[K_IFF_IMP1];
   MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `q:form` THEN
   REWRITE_TAC[K_AND_RIGHT_TH] THEN ASM_SIMP_TAC[K_IFF_IMP1]]);;

let K_IMP_SUBST = prove
 (`!p p' q q'. |-- (p <-> p') /\ |-- (q <-> q')
               ==> |-- ((p --> q) <-> (p' --> q'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[K_IFF_DEF] THEN
  POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN
  SUBGOAL_THEN `!p q p' q'.
                  |-- (p <-> p') /\ |-- (q <-> q')
                  ==> |-- ((p --> q) --> (p' --> q'))`
    (fun th -> MESON_TAC[th; K_IFF_SYM]) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC K_IMP_MONO_TH_2 THEN
  ASM_MESON_TAC[K_IFF_IMP1; K_IFF_SYM]);;

let K_DE_MORGAN_AND_TH = prove
 (`!p q. |-- (Not (p && q) <-> Not p || Not q)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K_IFF_TRANS THEN
  EXISTS_TAC `Not (Not (Not p) && Not (Not q))` THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_NOT_SUBST THEN ONCE_REWRITE_TAC[K_IFF_SYM] THEN
   MATCH_MP_TAC K_AND_SUBST_TH THEN CONJ_TAC THEN
   MATCH_ACCEPT_TAC K_NOT_NOT_TH;
   ONCE_REWRITE_TAC[K_IFF_SYM] THEN MATCH_ACCEPT_TAC K_AXIOM_OR]);;

let K_IFF_SYM_TH = prove
 (`!p q. |-- ((p <-> q) <-> (q <-> p))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K_IFF_TRANS THEN
  EXISTS_TAC `(p --> q) && (q --> p)` THEN ASM_REWRITE_TAC[K_IFF_DEF_TH] THEN
  ONCE_REWRITE_TAC[K_IFF_SYM] THEN MATCH_MP_TAC K_IFF_TRANS THEN
  EXISTS_TAC `(q --> p) && (p --> q)` THEN
REWRITE_TAC[K_IFF_DEF_TH; K_AND_COMM_TH]);;

let K_IFF_TRUE_TH = prove
 (`(!p. |-- ((p <-> True) <-> p)) /\
   (!p. |-- ((True <-> p) <-> p))`,
  CLAIM_TAC "1" `!p. |-- ((p <-> True) <-> p)` THENL
  [GEN_TAC THEN MATCH_MP_TAC K_IMP_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `True --> p` THEN CONJ_TAC THENL
    [MATCH_ACCEPT_TAC K_AXIOM_IFFIMP2; ALL_TAC] THEN
    MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `(True --> p) && True` THEN
    REWRITE_TAC[K_MODUSPONENS_TH] THEN MATCH_MP_TAC K_AND_INTRO THEN
    REWRITE_TAC[K_IMP_REFL_TH] THEN MATCH_MP_TAC K_ADD_ASSUM THEN
    MATCH_ACCEPT_TAC K_TRUTH_TH;
    ALL_TAC] THEN
   MATCH_MP_TAC K_IMP_TRANS THEN
   EXISTS_TAC `(p --> True) && (True --> p)` THEN
   CONJ_TAC THENL [ALL_TAC; MESON_TAC[K_IFF_DEF_TH; K_IFF_IMP2]] THEN
   MATCH_MP_TAC K_AND_INTRO THEN REWRITE_TAC[K_AXIOM_ADDIMP] THEN
   SIMP_TAC[K_ADD_ASSUM; K_TRUTH_TH];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC K_IFF_TRANS THEN
  EXISTS_TAC `p <-> True` THEN ASM_REWRITE_TAC[K_IFF_SYM_TH]);;

let K_OR_SUBST_TH = prove
 (`!p p' q q'. |-- (p <-> p') /\ |-- (q <-> q')
               ==> |-- (p || q <-> p' || q')`,
  SUBGOAL_THEN
    `!p p' q q'. |-- (p <-> p') /\ |-- (q <-> q')
                 ==> |-- (p || q --> p' || q')`
    (fun th -> MESON_TAC[th; K_IFF_SYM; K_IFF_DEF]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[K_DISJ_IMP] THEN CONJ_TAC THEN
  MATCH_MP_TAC K_FREGE THENL
  [EXISTS_TAC `p':form` THEN CONJ_TAC THENL
   [MATCH_MP_TAC K_ADD_ASSUM THEN MATCH_ACCEPT_TAC K_OR_RIGHT_TH;
    ASM_SIMP_TAC[K_IFF_IMP1]];
   EXISTS_TAC `q':form` THEN CONJ_TAC THENL
   [MATCH_MP_TAC K_ADD_ASSUM THEN MATCH_ACCEPT_TAC K_OR_LEFT_TH;
    ASM_SIMP_TAC[K_IFF_IMP1]]]);;

let K_OR_SUBST_RIGHT = prove
 (`!p q1 q2. |-- (q1 <-> q2) ==> |-- (p || q1 <-> p || q2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC K_OR_SUBST_TH THEN
  ASM_REWRITE_TAC[K_IFF_REFL_TH]);;

let K_OR_RID_TH = prove
 (`!p. |-- (p || False <-> p)`,
  GEN_TAC THEN REWRITE_TAC[K_IFF_DEF] THEN CONJ_TAC THENL
  [REWRITE_TAC[K_DISJ_IMP; K_IMP_REFL_TH; K_EX_FALSO_TH];
   MATCH_ACCEPT_TAC K_OR_RIGHT_TH]);;

let K_OR_LID_TH = prove
 (`!p. |-- (False || p <-> p)`,
  GEN_TAC THEN REWRITE_TAC[K_IFF_DEF] THEN CONJ_TAC THENL
  [REWRITE_TAC[K_DISJ_IMP; K_IMP_REFL_TH; K_EX_FALSO_TH];
   MATCH_ACCEPT_TAC K_OR_LEFT_TH]);;

let K_OR_ASSOC_LEFT_TH = prove
 (`!p q r. |-- (p || (q || r) --> (p || q) || r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[K_DISJ_IMP] THEN
  MESON_TAC[K_OR_LEFT_TH; K_OR_RIGHT_TH; K_IMP_TRANS]);;

let K_OR_ASSOC_RIGHT_TH = prove
 (`!p q r. |-- ((p || q) || r --> p || (q || r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[K_DISJ_IMP] THEN
  MESON_TAC[K_OR_LEFT_TH; K_OR_RIGHT_TH; K_IMP_TRANS]);;

let K_OR_ASSOC_TH = prove
 (`!p q r. |-- (p || (q || r) <-> (p || q) || r)`,
  REWRITE_TAC[K_IFF_DEF; K_OR_ASSOC_LEFT_TH; K_OR_ASSOC_RIGHT_TH]);;

let K_AND_OR_LDISTRIB_TH = prove
 (`!p q r. |-- (p && (q || r) <-> p && q || p && r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[K_IFF_DEF; K_DISJ_IMP] THEN
  REPEAT CONJ_TAC THEN TRY (MATCH_MP_TAC K_AND_INTRO) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC K_ANTE_CONJ THENL
  [MATCH_MP_TAC K_IMP_SWAP THEN REWRITE_TAC[K_DISJ_IMP] THEN
  CONJ_TAC THEN MATCH_MP_TAC K_IMP_SWAP THEN MATCH_MP_TAC K_SHUNT THENL
   [MATCH_ACCEPT_TAC K_OR_RIGHT_TH; MATCH_ACCEPT_TAC K_OR_LEFT_TH];
   MATCH_ACCEPT_TAC K_AXIOM_ADDIMP;
   MATCH_MP_TAC K_ADD_ASSUM THEN MATCH_ACCEPT_TAC K_OR_RIGHT_TH;
   MATCH_ACCEPT_TAC K_AXIOM_ADDIMP;
   MATCH_MP_TAC K_ADD_ASSUM THEN MATCH_ACCEPT_TAC K_OR_LEFT_TH]);;

let K_NOT_TRUE_TH = prove
 (`|-- (Not True <-> False)`,
  REWRITE_TAC[K_IFF_DEF; K_EX_FALSO_TH; GSYM K_NOT_DEF] THEN
  MATCH_MP_TAC K_IFF_MP THEN EXISTS_TAC `True` THEN
  REWRITE_TAC[K_TRUTH_TH] THEN ONCE_REWRITE_TAC[K_IFF_SYM] THEN
  MATCH_ACCEPT_TAC K_NOT_NOT_TH);;

let K_AND_SUBSTR_RIGHT_TH = prove
 (`!p q1 q2. |-- ((q1 <-> q2) --> (p && q1 <-> p && q2))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K_IMP_TRANS THEN
  EXISTS_TAC `(p && q1 --> p && q2) && (p && q2 --> p && q1)` THEN
  CONJ_TAC THENL
  [ALL_TAC; MATCH_MP_TAC K_IFF_IMP2 THEN MATCH_ACCEPT_TAC K_IFF_DEF_TH] THEN
  SUBGOAL_THEN `!p q1 q2. |-- ((q1 <-> q2) --> (p && q1 --> p && q2))`
    (fun th -> MATCH_MP_TAC K_AND_INTRO THEN
      MESON_TAC[th; K_AND_COMM_TH; K_IMP_TRANS; K_IFF_DEF_TH;
                K_IFF_IMP1; K_IFF_IMP2]) THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC K_SHUNT THEN MATCH_MP_TAC K_AND_INTRO THEN
  CONJ_TAC THENL
  [MESON_TAC[K_AND_LEFT_TH; K_AND_RIGHT_TH; K_IMP_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `(q1 <-> q2) && q1` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC K_AND_INTRO THEN REWRITE_TAC[K_AND_LEFT_TH] THEN
   MESON_TAC[K_AND_RIGHT_TH; K_IMP_TRANS];
   MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `(q1 --> q2) && q1` THEN
   REWRITE_TAC[K_MODUSPONENS_TH] THEN MATCH_MP_TAC K_AND_INTRO THEN
   REWRITE_TAC[K_AND_RIGHT_TH] THEN MATCH_MP_TAC K_IMP_TRANS THEN
   EXISTS_TAC `(q1 <-> q2)` THEN REWRITE_TAC[K_AND_LEFT_TH] THEN
   MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `(q1 --> q2) && (q2 --> q1)` THEN
   REWRITE_TAC[K_AND_LEFT_TH] THEN MATCH_MP_TAC K_IFF_IMP1 THEN
   MATCH_ACCEPT_TAC K_IFF_DEF_TH]);;

let K_AND_SUBST_LEFT_TH = prove
 (`!p1 p2 q. |-- ((p1 <-> p2) --> (p1 && q <-> p2 && q))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K_IMP_TRANS THEN
  EXISTS_TAC `(p1 && q --> p2 && q) && (p2 && q --> p1 && q)` THEN
  CONJ_TAC THENL
  [ALL_TAC; MATCH_MP_TAC K_IFF_IMP2 THEN MATCH_ACCEPT_TAC K_IFF_DEF_TH] THEN
  SUBGOAL_THEN `!p1 p2 q. |-- ((p1 <-> p2) --> (p1 && q --> p2 && q))`
    (fun th -> MATCH_MP_TAC K_AND_INTRO THEN
      MESON_TAC[th; K_AND_COMM_TH; K_IMP_TRANS; K_IFF_DEF_TH;
                K_IFF_IMP1; K_IFF_IMP2]) THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC K_SHUNT THEN MATCH_MP_TAC K_AND_INTRO THEN
  CONJ_TAC THENL
  [ALL_TAC; MESON_TAC[K_AND_LEFT_TH; K_AND_RIGHT_TH; K_IMP_TRANS]] THEN
  MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `(p1 <-> p2) && p1` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC K_AND_INTRO THEN REWRITE_TAC[K_AND_LEFT_TH] THEN
   MESON_TAC[K_AND_RIGHT_TH; K_AND_LEFT_TH; K_IMP_TRANS];
   MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `(p1 --> p2) && p1` THEN
   REWRITE_TAC[K_MODUSPONENS_TH] THEN MATCH_MP_TAC K_AND_INTRO THEN
   REWRITE_TAC[K_AND_RIGHT_TH] THEN MATCH_MP_TAC K_IMP_TRANS THEN
   EXISTS_TAC `(p1 <-> p2)` THEN REWRITE_TAC[K_AND_LEFT_TH] THEN
   MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `(p1 --> p2) && (p2 --> p1)` THEN
   REWRITE_TAC[K_AND_LEFT_TH] THEN MATCH_MP_TAC K_IFF_IMP1 THEN
   MATCH_ACCEPT_TAC K_IFF_DEF_TH]);;

let K_CONTRAPOS_TH = prove
 (`!p q. |-- ((p --> q) --> (Not q --> Not p))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K_IMP_SWAP THEN
  MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `(q --> False)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_IFF_IMP1 THEN MATCH_ACCEPT_TAC K_AXIOM_NOT;
   MATCH_MP_TAC K_SHUNT THEN MATCH_MP_TAC K_IMP_TRANS THEN
   EXISTS_TAC `p --> False` THEN CONJ_TAC THENL
   [MESON_TAC[K_ANTE_CONJ; K_IMP_TRANS_TH];
    MESON_TAC[K_AXIOM_NOT; K_IFF_IMP2]]]);;

let K_CONTRAPOS_EQ_TH = prove
 (`!p q. |-- ((p --> q) <-> (Not q --> Not p))`,
  SUBGOAL_THEN `!p q. |-- ((Not q --> Not p) --> (p --> q))`
    (fun th -> MESON_TAC[th; K_IFF_DEF; K_CONTRAPOS_TH]) THEN
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC K_IMP_TRANS THEN
  EXISTS_TAC `Not (Not p) --> Not (Not q)` THEN CONJ_TAC THENL
  [MATCH_ACCEPT_TAC K_CONTRAPOS_TH; ALL_TAC] THEN
  MATCH_MP_TAC K_IFF_IMP1 THEN MATCH_MP_TAC K_IMP_SUBST THEN
  MESON_TAC[K_NOT_NOT_TH]);;

let K_IFF_SYM_TH_1 = prove
 (`!p q. |-- ((p <-> q) --> (q <-> p))`,
  REPEAT  GEN_TAC THEN MATCH_MP_TAC K_IMP_TRANS THEN
  EXISTS_TAC `(p --> q) && (q --> p)` THEN CONJ_TAC THENL
  [MESON_TAC[K_IFF_DEF_TH; K_IFF_IMP1]; ALL_TAC] THEN
  MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `(q --> p) && (p --> q)` THEN
  CONJ_TAC THENL
  [MESON_TAC[K_AND_COMM_TH; K_IFF_IMP1];
   MESON_TAC[K_IFF_DEF_TH; K_IFF_IMP2]]);;

let K_DE_MORGAN_OR_TH = prove
 (`!p q. |-- (Not (p || q) <-> Not p && Not q)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K_IFF_TRANS THEN
  EXISTS_TAC `Not (Not (Not p && Not q))` THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_NOT_SUBST THEN MATCH_ACCEPT_TAC K_AXIOM_OR;
  MATCH_ACCEPT_TAC K_NOT_NOT_TH]);;

let K_CRYSIPPUS_TH = prove
 (`!p q. |-- (Not (p --> q) <-> p && Not q)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K_IFF_TRANS THEN
  EXISTS_TAC `(p --> Not q --> False) --> False` THEN CONJ_TAC THENL
  [ALL_TAC; MESON_TAC[K_AXIOM_AND; K_IFF_SYM]] THEN
  MATCH_MP_TAC K_IFF_TRANS THEN EXISTS_TAC `Not (p --> Not q --> False)` THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_ACCEPT_TAC K_AXIOM_NOT] THEN
  MATCH_MP_TAC K_NOT_SUBST THEN
  MATCH_MP_TAC K_IMP_SUBST THEN
  CONJ_TAC THENL [MATCH_ACCEPT_TAC K_IFF_REFL_TH; ALL_TAC] THEN
  MATCH_MP_TAC K_IFF_TRANS THEN EXISTS_TAC `Not (Not q)` THEN CONJ_TAC THENL
  [MESON_TAC[K_NOT_NOT_TH; K_IFF_SYM]; MATCH_ACCEPT_TAC K_AXIOM_NOT]);;

(* ------------------------------------------------------------------------- *)
(* Substitution.                                                             *)
(* ------------------------------------------------------------------------- *)

let SUBST = new_recursive_definition form_RECURSION
  `(!f. SUBST f True = True) /\
   (!f. SUBST f False = False) /\
   (!f a. SUBST f (Atom a) = f a) /\
   (!f p. SUBST f (Not p) = Not (SUBST f p)) /\
   (!f p q. SUBST f (p && q) = SUBST f p && SUBST f q) /\
   (!f p q. SUBST f (p || q) = SUBST f p || SUBST f q) /\
   (!f p q. SUBST f (p --> q) = SUBST f p --> SUBST f q) /\
   (!f p q. SUBST f (p <-> q) = SUBST f p <-> SUBST f q) /\
   (!f p. SUBST f (Box p) = Box (SUBST f p))`;;

let SUBST_IMP = prove
 (`!f p. |-- p ==> |-- (SUBST f p)`,
  GEN_TAC THEN MATCH_MP_TAC Kproves_INDUCT THEN REWRITE_TAC[SUBST] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC Kaxiom_INDUCT THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC (CONJUNCT1 Kproves_RULES) THEN
   REWRITE_TAC[Kaxiom_RULES; SUBST];
   ALL_TAC] THEN
  REWRITE_TAC[SUBST; Kproves_RULES]);;

let SUBSTITUTION_LEMMA = prove
 (`!f p q. |-- (p <-> q) ==> |-- (SUBST f p <-> SUBST f q)`,
  REWRITE_TAC[GSYM SUBST; SUBST_IMP]);;

(* ------------------------------------------------------------------------- *)
(* SUBST_IFF.                                                                *)
(* ------------------------------------------------------------------------- *)

let K_IFF_SUBST = prove
 (`!p p' q q'. |-- (p <-> p') /\ |-- (q <-> q')
               ==> |-- ((p <-> q) <-> (p' <-> q'))`,
  SUBGOAL_THEN `!p q p' q'.
                |-- (p <-> p') /\ |-- (q <-> q')
                ==> |-- ((p <-> q) --> (p' <-> q'))`
    (fun th -> REPEAT STRIP_TAC THEN REWRITE_TAC[K_IFF_DEF] THEN
                ASM_MESON_TAC[th; K_IFF_SYM]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC K_IMP_TRANS THEN
  EXISTS_TAC `(p --> q) && (q --> p)` THEN
  CONJ_TAC THENL [MESON_TAC[K_IFF_DEF_TH; K_IFF_IMP1]; ALL_TAC] THEN
  MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `(p' --> q') && (q' --> p')` THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[K_IFF_DEF_TH; K_IFF_IMP2]] THEN
  MATCH_MP_TAC K_AND_INTRO THEN CONJ_TAC THEN MATCH_MP_TAC K_ANTE_CONJ THENL
  [MATCH_MP_TAC K_IMP_INSERT THEN MATCH_MP_TAC K_IMP_SWAP THEN
   MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `p:form` THEN
   CONJ_TAC THENL [ASM_MESON_TAC[K_IFF_IMP2]; ALL_TAC] THEN
   MATCH_MP_TAC K_SHUNT THEN MATCH_MP_TAC K_IMP_TRANS THEN
   EXISTS_TAC `q:form` THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[K_IFF_IMP1]] THEN
   MATCH_MP_TAC K_ANTE_CONJ THEN MATCH_MP_TAC K_IMP_SWAP THEN
   MATCH_ACCEPT_TAC K_IMP_REFL_TH;
   ALL_TAC] THEN
  MATCH_MP_TAC K_ADD_ASSUM THEN MATCH_MP_TAC K_IMP_SWAP THEN
  MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `q:form` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[K_IFF_IMP2]; ALL_TAC] THEN
  MATCH_MP_TAC K_IMP_SWAP THEN MATCH_MP_TAC K_IMP_ADD_ASSUM THEN
  ASM_MESON_TAC[K_IFF_IMP1]);;

let K_BOX_IFF_TH = prove
 (`!p q. |-- (Box (p <-> q) --> (Box p <-> Box q))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K_IMP_TRANS THEN
  EXISTS_TAC `(Box p --> Box q) && (Box q --> Box p)` THEN CONJ_TAC THENL
  [ALL_TAC; MATCH_MP_TAC K_IFF_IMP2 THEN MATCH_ACCEPT_TAC K_IFF_DEF_TH] THEN
  MATCH_MP_TAC K_AND_INTRO THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `Box (p --> q)` THEN
   REWRITE_TAC[K_AXIOM_BOXIMP] THEN MATCH_MP_TAC K_IMP_BOX THEN
   MATCH_ACCEPT_TAC K_AXIOM_IFFIMP1;
   MATCH_MP_TAC K_IMP_TRANS THEN EXISTS_TAC `Box (q --> p)` THEN
   REWRITE_TAC[K_AXIOM_BOXIMP] THEN MATCH_MP_TAC K_IMP_BOX THEN
   MATCH_ACCEPT_TAC K_AXIOM_IFFIMP2]);;

let K_BOX_IFF = prove
 (`!p q. |-- (Box (p <-> q)) ==> |-- (Box p <-> Box q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC K_IMP_ANTISYM THEN CONJ_TAC THENL
  [MATCH_MP_TAC K_MODUSPONENS THEN EXISTS_TAC `Box (p --> q)` THEN
   REWRITE_TAC[K_AXIOM_BOXIMP] THEN
   MATCH_MP_TAC K_BOX_MODUSPONENS THEN EXISTS_TAC `(p <-> q)` THEN
   ASM_REWRITE_TAC[K_AXIOM_IFFIMP1];
   MATCH_MP_TAC K_MODUSPONENS THEN EXISTS_TAC `Box (q --> p)` THEN
   REWRITE_TAC[K_AXIOM_BOXIMP] THEN
   MATCH_MP_TAC K_BOX_MODUSPONENS THEN EXISTS_TAC `(p <-> q)` THEN
   ASM_REWRITE_TAC[K_AXIOM_IFFIMP2]]);;

let K_BOX_SUBST = prove
 (`!p q. |-- (p <-> q) ==> |-- (Box p <-> Box q)`,
  SIMP_TAC[K_BOX_IFF; K_NECESSITATION]);;

let SUBST_IFF = prove
 (`!f g p. (!a. |-- (f a <-> g a)) ==> |-- (SUBST f p <-> SUBST g p)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC form_INDUCT THEN
  ASM_REWRITE_TAC[SUBST; K_IFF_REFL_TH] THEN REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC K_NOT_SUBST THEN POP_ASSUM MATCH_ACCEPT_TAC;
   MATCH_MP_TAC K_AND_SUBST_TH THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC K_OR_SUBST_TH THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC K_IMP_SUBST THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC K_IFF_SUBST THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC K_BOX_SUBST THEN POP_ASSUM MATCH_ACCEPT_TAC]);;

(* ----------------------------------------------------------------------- *)
(* Some modal propositional schemas and derived rules.                     *)
(* ----------------------------------------------------------------------- *)

let K_BOX_AND_TH = prove
 (`!p q. |-- (Box(p && q) --> (Box p && Box q))`,
  MESON_TAC[K_AND_INTRO; K_IMP_BOX; K_AND_LEFT_TH; K_AND_RIGHT_TH]);;

let K_BOX_AND_INV_TH = prove
 (`!p q. |-- ((Box p && Box q) --> Box (p && q))`,
  MESON_TAC[K_ANTE_CONJ; K_IMP_TRANS; K_IMP_BOX; K_AND_PAIR_TH;
            K_AXIOM_BOXIMP; K_SHUNT]);;

(* ----------------------------------------------------------------------  *)
(* Soundness.                                                              *)
(* ----------------------------------------------------------------------  *)

g `!p. Kaxiom p ==> WR |= p`;;
e (MATCH_MP_TAC Kaxiom_INDUCT);;
e (MODAL_TAC);;
let K_VALID = top_thm();;

let FRAME = new_definition
  `FRAME (W:W->bool,R:W->W->bool) <=>
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   FINITE W`;;

g `!p. |-- p ==> FRAME:(W->bool)#(W->W->bool)->bool |= p`;;
e (MATCH_MP_TAC Kproves_INDUCT);;
e (REWRITE_TAC[K_VALID]);;
e (MODAL_TAC);;
let K_FRAME_VALID = top_thm ();;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness                                                        *)
(* ------------------------------------------------------------------------- *)

g `~ |-- False`;;
e (REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] K_FRAME_VALID)));;
e (REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM; 
                FRAME; NOT_FORALL_THM]);;
e (MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. F`]);;
e (REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING]);;
e (MESON_TAC[]);;
let K_CONSISTENT = top_thm ();;
