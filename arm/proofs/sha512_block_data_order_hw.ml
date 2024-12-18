(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA512 with hardware intrinsics.                                          *)
(* ========================================================================= *)

needs "arm/proofs/sha512_block_data_order_hw_program.ml";;

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* First, some helper lemmas *)

let REV64_BITMANIP_SIMP_LEMMAS = prove(`!(x64:(64)word).
(word_subword (word_subword x64 (0,16) :(16)word) (0,8) :(8)word) = 
(word_subword x64 (0,8) :(8)word)
/\
(word_subword (word_subword x64 (0,16) :(16)word) (8,8) :(8)word) = 
(word_subword x64 (8,8) :(8)word)
/\
(word_subword (word_subword x64 (0,32) :(32)word) (0,16) :(16)word) = 
(word_subword x64 (0,16) :(16)word)
/\
(word_subword (word_subword x64 (0,32) :(32)word) (16,16) :(16)word) = 
(word_subword x64 (16,16) :(16)word)
/\
(word_subword (word_subword x64 (32,32) :(32)word) (0,16) :(16)word) = 
(word_subword x64 (32,16) :(16)word)
/\
(word_subword (word_subword x64 (32,32) :(32)word) (16,16) :(16)word) = 
(word_subword x64 (48,16) :(16)word)
/\
(word_subword
  (word_join (word_subword x64 (0,32) :(32)word)
             (word_subword x64 (32,32) :(32)word) :(64)word)
  (32,16) :(16)word) =
(word_subword x64 (0,16) :(16)word)  
/\
(word_subword
  (word_join (word_subword x64 (0,32) :(32)word)
             (word_subword x64 (32,32) :(32)word) :(64)word)
  (48,16) :(16)word) =
(word_subword x64 (16,16) :(16)word) 
/\
(word_subword
 (word_join (word_subword x64 (0,32)  :(32)word)
            (word_subword x64 (32,32) :(32)word) :(64)word)
 (0,16) :(16)word) =
(word_subword x64 (32, 16) :(16)word)
/\
(word_subword
 (word_join (word_subword x64 (0,32)  :(32)word)
            (word_subword x64 (32,32) :(32)word) :(64)word)
 (16,16) :(16)word) =
(word_subword x64 (48, 16) :(16)word)
/\
(word_subword
 (word_subword
  (word_join
   (word_join (word_subword x64 (0,16)  :(16)word)
              (word_subword x64 (16,16) :(16)word) :(32)word)
   (word_join (word_subword  x64 (32,16) :(16)word)
              (word_subword  x64 (48,16) :(16)word) :(32)word) :(64)word)
  (48,16) :(16)word)
 (0,8) :(8)word) =
 (word_subword x64 (0,8)  :(8)word)
/\
(word_subword
 (word_subword
  (word_join
   (word_join (word_subword x64 (0,16)  :(16)word)
              (word_subword x64 (16,16) :(16)word) :(32)word)
   (word_join (word_subword  x64 (32,16) :(16)word)
              (word_subword  x64 (48,16) :(16)word) :(32)word) :(64)word)
  (48,16) :(16)word)
 (8,8) :(8)word) =
 (word_subword x64 (8,8)  :(8)word) 
/\
(word_subword
 (word_subword
  (word_join
   (word_join (word_subword x64 (0,16)  :(16)word)
              (word_subword x64 (16,16) :(16)word) :(32)word)
   (word_join (word_subword x64 (32,16) :(16)word)
              (word_subword x64 (48,16) :(16)word) :(32)word) :(64)word)
  (32,16) :(16)word)
 (0,8) :(8)word) = 
(word_subword x64 (16,8)  :(8)word)
/\
(word_subword
 (word_subword
  (word_join
   (word_join (word_subword x64 (0,16)  :(16)word)
              (word_subword x64 (16,16) :(16)word) :(32)word)
   (word_join (word_subword x64 (32,16) :(16)word)
              (word_subword x64 (48,16) :(16)word) :(32)word) :(64)word)
  (32,16) :(16)word)
 (8,8) :(8)word) = 
(word_subword x64 (24,8)  :(8)word)
/\
(word_join
       (word_join (word_subword x64 (0,8) :(8)word)
                  (word_subword x64 (8,8) :(8)word) :(16)word)
       (word_join (word_subword x64 (16,8) :(8)word)
                  (word_subword x64 (24,8) :(8)word) :(16)word) :(32)word) =
word_bytereverse (word_subword x64 (0,32) :(32)word)
/\
(word_subword
 (word_subword
  (word_join
   (word_join (word_subword x64 (0,16) :(16)word)
              (word_subword x64 (16,16) :(16)word) :(32)word)
   (word_join (word_subword x64 (32,16) :(16)word)
              (word_subword x64 (48,16) :(16)word) :(32)word) :(64)word)
  (16,16) :(16)word)
 (0,8) :(8)word) =
(word_subword x64 (32, 8) :(8)word) 
/\
(word_subword
 (word_subword
  (word_join
   (word_join (word_subword x64 (0,16) :(16)word)
              (word_subword x64 (16,16) :(16)word) :(32)word)
   (word_join (word_subword x64 (32,16) :(16)word)
              (word_subword x64 (48,16) :(16)word) :(32)word) :(64)word)
  (16,16) :(16)word)
 (8,8) :(8)word) =
(word_subword x64 (40, 8) :(8)word) 
/\
(word_subword
 (word_join
    (word_join (word_subword x64 (0,16) :(16)word)
               (word_subword x64 (16,16) :(16)word) :(32)word)
     (word_join (word_subword x64 (32,16) :(16)word)
                (word_subword x64 (48,16) :(16)word) :(32)word) :(64)word)
(0,8) :(8)word) = 
(word_subword x64 (48,8) :(8)word)
/\
(word_subword
 (word_join
    (word_join (word_subword x64 (0,16) :(16)word)
               (word_subword x64 (16,16) :(16)word) :(32)word)
     (word_join (word_subword x64 (32,16) :(16)word)
                (word_subword x64 (48,16) :(16)word) :(32)word) :(64)word)
(8,8) :(8)word) = 
(word_subword x64 (56,8) :(8)word)
/\
(word_join
       (word_join (word_subword x64 (32,8) :(8)word)
                  (word_subword x64 (40,8) :(8)word) :(16)word)
       (word_join (word_subword x64 (48,8) :(8)word)
                  (word_subword x64 (56,8) :(8)word) :(16)word) :(32)word) =
word_bytereverse (word_subword x64 (32,32) :(32)word)
/\
(word_bytereverse (word_subword (word_bytereverse x64) (0,32) :(32)word)) =
(word_subword x64 (32,32) :(32)word)
/\
(word_bytereverse (word_subword (word_bytereverse x64) (32,32) :(32)word)) =
(word_subword x64 (0,32) :(32)word)
/\
(word_join (word_subword x64 (32,32) :(32)word) (word_subword x64 (0,32) :(32)word) :(64)word) = 
x64
`,
CONV_TAC WORD_BLAST);;

(* SHA512 instrinsics in terms of specification functions. *)

let SHA512SU1_SU0 = prove(
 `!(a0:(64)word) (a1:(64)word) (b0:(64)word) (b1:(64)word) 
   (c0:(64)word) (c1:(64)word) (d0:(64)word) (d1:(64)word).
    sha512su1 (sha512su0 (word_join a1 a0 :(128)word) (word_join b1 b0 :(128)word))
              (word_join c1 c0 :(128)word)
              (word_join d1 d0:(128)word) =
    word_join (message_schedule_word c1 d1 b0 a1)
              (message_schedule_word c0 d0 a1 a0) :(128)word`,
  REWRITE_TAC[sha512su0; sha512su1; message_schedule_word] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_BITMANIP_SIMP_LEMMAS; REV64_BITMANIP_SIMP_LEMMAS] THEN
  REWRITE_TAC[WORD_ADD; WORD_ADD_AC]);;
    
(* 
Note that
Maj(a,b,c) = Maj(a,c,b) = Maj(b,a,c) = Maj(b,c,a) = Maj(c,a,b) = Maj(c,b,a). 
*)  
let MAJ_ABC_EQ_CBA = prove(
   `!(a:(64)word) (b:(64)word) (c:(64)word).
     Maj(a,b,c) = Maj(c,b,a)`,
     REWRITE_TAC[Maj_DEF] THEN
     CONV_TAC WORD_BLAST);;      

let SHA512H2_RULE = prove(
 `!(x1:(64)word) (x0:(64)word) 
  (y1:(64)word) (y0:(64)word)
  (z1:(64)word) (z0:(64)word).
  sha512h2 (word_join x1 x0) (word_join y1 y0) (word_join z1 z0) = 
  word_join (x1 + (compression_t2 z0 z1 y0)) 
            ((compression_t2 (x1 + (compression_t2 z0 z1 y0)) z0 z1) + x0) :(128)word`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha512h2; compression_t2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_BITMANIP_SIMP_LEMMAS; REV64_BITMANIP_SIMP_LEMMAS] THEN
  REWRITE_TAC[WORD_ADD_AC] THEN
  (* We rotate the arguments of Maj using MAJ_ABC_EQ_CBA to match the invocation
     in the specification function. *)
  SUBST1_TAC(ISPECL [`y0:64 word`; `z1:64 word`;`z0:64 word`] MAJ_ABC_EQ_CBA) THEN
  REWRITE_TAC[]);;

let SHA512H_RULE = prove(
`!(d:(64)word) (e:(64)word) (f:(64)word) (g:(64)word) (h:(64)word)
  (i0:(64)word) (i1:(64)word) (k0:(64)word) (k1:(64)word).
  (sha512h (word_join (h + k0 + i0) (g + k1 + i1))
              (word_join g f)
              (word_join e d)) =
  word_join (compression_t1 e f g h k0 i0)
            (compression_t1 (d + (compression_t1 e f g h k0 i0)) e f g k1 i1)`,
  REWRITE_TAC[sha512h; compression_t1] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_BITMANIP_SIMP_LEMMAS; REV64_BITMANIP_SIMP_LEMMAS] THEN
  REWRITE_TAC[WORD_ADD_AC]);;

(* Simplifying the SHA512 specification functions. *)

let SHA512_SPEC_ONE_BLOCK_RULE = prove(
`forall i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15.
     sha512 (\i:num j:num. EL j 
              [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9;i10; i11; i12; i13; i14; i15]) 
            1
     = 
     add8
        (compression 
          0 h_init
          (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15]))
        h_init`,
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [sha512] THEN CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV) THEN
    ONCE_REWRITE_TAC [sha512] THEN CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV) THEN
    REWRITE_TAC[sha512_block] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV));;  

(*
let MESSAGE_SCHEDULE_I_LT_16_RULE = prove(    
 `forall n i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15.
  n < 16 ==>
  (message_schedule
     (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
     n) =
  EL n [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15]`,
  REPEAT STRIP_TAC THEN
  ONCE_ASM_REWRITE_TAC [message_schedule] THEN
  ASM_REWRITE_TAC []);;
*)    

let MESSAGE_SCHEDULE_1_16_RULES = prove( 
`forall i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15.
 (message_schedule
    (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
    0) = i0 
 /\
 (message_schedule
   (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
   1) = i1
 /\
 (message_schedule
   (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
   2) = i2
 /\
 (message_schedule
   (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
   3) = i3 
 /\
 (message_schedule
  (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
  4) = i4 
 /\
 (message_schedule
  (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
  5) = i5
 /\
 (message_schedule
  (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
  6) = i6
 /\
 (message_schedule
  (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
  7) = i7
  /\
 (message_schedule
  (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
  8) = i8
  /\
 (message_schedule
  (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
  9) = i9
  /\
 (message_schedule
  (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
  10) = i10
  /\
 (message_schedule
  (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
  11) = i11
  /\
 (message_schedule
  (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
  12) = i12 
  /\
 (message_schedule
  (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
  13) = i13 
  /\
 (message_schedule
  (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
  14) = i14 
  /\
 (message_schedule
  (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
  15) = i15`, 
 REPEAT STRIP_TAC THEN
 ONCE_ASM_REWRITE_TAC [message_schedule] THEN
 ASM_REWRITE_TAC [EL_CONS] THEN 
 CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV));;

let MESSAGE_SCHEDULE_16_RULE = prove(
   `forall i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15.   
   (message_schedule
      (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
      16) =
   message_schedule_word i14 i9 i1 i0`,
   REPEAT STRIP_TAC THEN
   ONCE_ASM_REWRITE_TAC [message_schedule] THEN
   CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV) THEN
   REWRITE_TAC[MESSAGE_SCHEDULE_1_16_RULES]);;

let MESSAGE_SCHEDULE_17_RULE = prove(
`forall i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15.   
   (message_schedule
      (\j. EL j [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15])
      17) =
    message_schedule_word i15 i10 i2 i1`,
    REPEAT STRIP_TAC THEN
    ONCE_ASM_REWRITE_TAC [message_schedule] THEN
    CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV) THEN
    REWRITE_TAC[MESSAGE_SCHEDULE_1_16_RULES]);;

(* Abbreviates the first terms matching compression_t1 and compression_t2 in the goal. 
let ABBREV_CT1_CT2_TERM n (asl, w as gl) = 
 let ty = `:((64)word)` in
 let ct1_var = mk_var("ct1_" ^ string_of_int n, ty) in
 let ct2_var = mk_var("ct2_" ^ string_of_int n, ty) in
 let occ_ct1 = find_term (fun tm -> fst (strip_comb tm) = `compression_t1`) w in
 let occ_ct2 = find_term (fun tm -> fst (strip_comb tm) = `compression_t2`) w in
 (ABBREV_TAC (mk_eq(ct1_var, occ_ct1)) THEN ABBREV_TAC (mk_eq(ct2_var, occ_ct2))) gl;; 
*)

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(* Augment the OCaml reference variable that stores rewrite rules that will be
   applied after each step of symbolic simulation. *)
extra_word_CONV := 
  (GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; 
                       REV64_BITMANIP_SIMP_LEMMAS; 
                       SHA512SU1_SU0; SHA512H_RULE; SHA512H2_RULE;                       
                       MESSAGE_SCHEDULE_16_RULE]) ::
                       !extra_word_CONV;;

let COMPRESSION_EXPAND_INIT_TAC = 
 (RULE_ASSUM_TAC(REWRITE_RULE[compression; h_init]) THEN
  RULE_ASSUM_TAC((CONV_RULE(TOP_DEPTH_CONV let_CONV))) THEN
  RULE_ASSUM_TAC((CONV_RULE(TOP_DEPTH_CONV NUM_RED_CONV))) THEN
  RULE_ASSUM_TAC((REWRITE_RULE[MESSAGE_SCHEDULE_1_16_RULES])));;

let COMPRESSION_EXPAND_TAC = 
  (RULE_ASSUM_TAC(REWRITE_RULE[compression; compression_update]) THEN
   RULE_ASSUM_TAC(CONV_RULE (TOP_DEPTH_CONV let_CONV)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[compression]) THEN
   RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
   RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV NUM_RED_CONV)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[MESSAGE_SCHEDULE_1_16_RULES]));;
                       
(* Abbreviate the first call of function fn found in the assumption list. 
   
   (FIXME) This is ugly because we're expecting that the first matches we 
   encounter in the assumption list aren't previously abbreviated terms; i.e., 
   we aren't re-abbreviating the LHS of the following that's ostensibly been 
   introduced using a prior ABBREV_TAC. E.g.,

   [compression_t1 h_e h_f h_g h_h (K 0) i0 = ct1_0]
*)
let ABBREV_FIRST_TERMS_IN_ASM_TAC (n:int) (var:string) (fn:term) (asl, w as gl) = 
  let ty = `:((64)word)` in
  let v = mk_var(var ^ string_of_int n, ty) in
  let (f : term -> term -> bool) = (fun pat tm -> fst (strip_comb tm) = pat) in
  let g = fun pat -> 
            find
              (fun (_, th) -> 
                try let _ = find_term (f pat) (concl th) in true
                with Failure _ -> false)             
             (rev asl) in
  let (_, matching_assum) = g fn in  
  let occ = find_term (f fn) (concl matching_assum) in  
  ABBREV_TAC (mk_eq(v, occ)) gl;;

(*
n: argument of the call of the compression function in the context.
*)  
let COMPRESSION_UNWIND_TAC (n:int) : tactic =
  if n < 18 || n > 80 then 
    failwith "COMPRESSION_UNWIND_TAC: constraint on n violated! Constraint: 18 <= n <= 80."
  else
    (* (FIXME) If i < 16, we don't have an H_ms_* hyp in the context to use; we
       have MESSAGE_SCHEDULE_1_16_RULES instead. However, we default to H_ms_16 
       out of sheer laziness. *)
    let (f : int -> string) = (fun i -> if i < 16 then "H_ms_16"
                                        else ("H_ms_" ^ (string_of_int i))) in
    let h_ms = f n in    
    let h_ms_2 = f (n - 2) in    
    let h_ms_7 = f (n - 7) in
    let h_ms_15 = f (n - 15) in    
    let h_ms_16 = f (n - 16) in        
    let ms_lhs = mk_comb 
                  (`message_schedule
                      (\j. EL j [i0; i1; i2; i3; 
                                 i4; i5; i6; i7; 
                                 i8; i9; i10; i11; 
                                 i12; i13; i14; i15])`,
                    (mk_small_numeral n)) in    
    let ms_rhs = mk_var(("ms_" ^ (string_of_int n)), `:((64)word)`) in
    let ms_term = mk_eq(ms_lhs, ms_rhs) in    
    (COMPRESSION_EXPAND_TAC THEN
     ABBREV_FIRST_TERMS_IN_ASM_TAC (n - 1) "ct1_" `compression_t1` THEN
     ABBREV_FIRST_TERMS_IN_ASM_TAC (n - 1) "ct2_" `compression_t2` THEN
     ABBREV_FIRST_TERMS_IN_ASM_TAC n "ms_" `message_schedule` THEN
     LABEL_TAC h_ms (ASSUME ms_term) THEN
     USE_THEN h_ms_2 (fun out2 -> 
     USE_THEN h_ms_7 (fun out7 -> 
     USE_THEN h_ms_15 (fun out15 -> 
     USE_THEN h_ms_16 (fun out16 -> 
          USE_THEN h_ms
           (fun th -> 
              let th' = ONCE_REWRITE_RULE [message_schedule] th in
              let th' = CONV_RULE(TOP_DEPTH_CONV NUM_RED_CONV) th' in
              let th' = REWRITE_RULE [MESSAGE_SCHEDULE_1_16_RULES; 
                                      out2; out7; out15; out16] th' in
              ASSUME_TAC th'))))));; 

arm_print_log := false;;
components_print_log := true;;

(* let tmp = WORD_REDUCE_CONV `word_bytereverse (word 0x11223344556677889900AABBCCDDEEFF):int128`;; *)
(* let tmp = WORD_REDUCE_CONV `(word_join (word_bytereverse (word 0x1122334455667788):int64) (word_bytereverse (word 0xAABBCCDDEEFF0011):int64)) : 128 word`;; *)
(* Printf.printf "%x\n" 857870592;; *)

g`forall pc retpc sp num_blocks hash_base ktbl_base input_base   
  // input_block 
  i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 
  // final hash
  a b c d e f g h.
// We fix the number of blocks to be hashed to 1 for now.
num_blocks = 1 /\
// No aliasing among all memory regions of interest.
PAIRWISE nonoverlapping
  [(word sp:int64, 128); (word pc:int64, LENGTH sha512_hw_mc); 
   (word hash_base:int64, 64);
   (word input_base:int64, 16 * 8 * num_blocks);
   (word ktbl_base:int64, 80 * 8)] /\
(a, b, c, d, e, f, g, h) = 
    sha512 (\i:num j:num. EL j 
              [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9;i10; i11; i12; i13; i14; i15]) 
            1
==>
ensures arm
  // Precondition
  (\s. aligned_bytes_loaded s (word pc) sha512_hw_mc /\
       aligned 16 (word sp:int64) /\ 
       read PC s  = word pc  /\
       read X30 s = word retpc /\
       read X0 s  = word hash_base /\
       read X1 s  = word input_base /\
       read X3 s  = word ktbl_base /\
       read X2 s  = word num_blocks /\
       read SP s  = word_add (word sp) (word 128) /\
       // KTbl constants are in memory.
       // bignum_from_memory (word ktbl_base, 80) s = ktbl_bignum /\
       read (memory :> bytes128 (word ktbl_base))                           s = word_join (K  1) (K  0) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word 16)))      s = word_join (K  3) (K  2) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*2))))  s = word_join (K  5) (K  4) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*3))))  s = word_join (K  7) (K  6) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*4))))  s = word_join (K  9) (K  8) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*5))))  s = word_join (K 11) (K 10) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*6))))  s = word_join (K 13) (K 12) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*7))))  s = word_join (K 15) (K 14) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*8))))  s = word_join (K 17) (K 16) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*9))))  s = word_join (K 19) (K 18) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*10)))) s = word_join (K 21) (K 20) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*11)))) s = word_join (K 23) (K 22) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*12)))) s = word_join (K 25) (K 24) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*13)))) s = word_join (K 27) (K 26) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*14)))) s = word_join (K 29) (K 28) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*15)))) s = word_join (K 31) (K 30) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*16)))) s = word_join (K 33) (K 32) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*17)))) s = word_join (K 35) (K 34) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*18)))) s = word_join (K 37) (K 36) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*19)))) s = word_join (K 39) (K 38) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*20)))) s = word_join (K 41) (K 40) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*21)))) s = word_join (K 43) (K 42) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*22)))) s = word_join (K 45) (K 44) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*23)))) s = word_join (K 47) (K 46) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*24)))) s = word_join (K 49) (K 48) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*25)))) s = word_join (K 51) (K 50) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*26)))) s = word_join (K 53) (K 52) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*27)))) s = word_join (K 55) (K 54) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*28)))) s = word_join (K 57) (K 56) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*29)))) s = word_join (K 59) (K 58) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*30)))) s = word_join (K 61) (K 60) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*31)))) s = word_join (K 63) (K 62) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*32)))) s = word_join (K 65) (K 64) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*33)))) s = word_join (K 67) (K 66) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*34)))) s = word_join (K 69) (K 68) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*35)))) s = word_join (K 71) (K 70) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*36)))) s = word_join (K 73) (K 72) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*37)))) s = word_join (K 75) (K 74) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*38)))) s = word_join (K 77) (K 76) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*39)))) s = word_join (K 79) (K 78) /\ 
       // One input block is in memory.       
       // bignum_from_memory (word input_base, 16) s = input_block /\
       // We use word_bytereverse below for each input word i0-i15 because they 
       // are in big-endian format, and this Arm machine is little-endian.
       //
       // The SHA512 specification expects the input as a big-endian value, and
       // REV64 instructions in the program change the endianness of 
       // the input words, so we will subsequently see 
       // (word_bytereverse (word_bytereverse i0)) = i0 in the rest of the program.
       read (memory :> bytes128 (word input_base))                       s = word_join (word_bytereverse  (i1 : 64 word)) (word_bytereverse  (i0 : 64 word)) /\
       read (memory :> bytes128 (word_add (word input_base) (word  16))) s = word_join (word_bytereverse  (i3 : 64 word)) (word_bytereverse  (i2 : 64 word)) /\
       read (memory :> bytes128 (word_add (word input_base) (word  32))) s = word_join (word_bytereverse  (i5 : 64 word)) (word_bytereverse  (i4 : 64 word)) /\
       read (memory :> bytes128 (word_add (word input_base) (word  48))) s = word_join (word_bytereverse  (i7 : 64 word)) (word_bytereverse  (i6 : 64 word)) /\
       read (memory :> bytes128 (word_add (word input_base) (word  64))) s = word_join (word_bytereverse  (i9 : 64 word)) (word_bytereverse  (i8 : 64 word)) /\
       read (memory :> bytes128 (word_add (word input_base) (word  80))) s = word_join (word_bytereverse (i11 : 64 word)) (word_bytereverse (i10 : 64 word)) /\
       read (memory :> bytes128 (word_add (word input_base) (word  96))) s = word_join (word_bytereverse (i13 : 64 word)) (word_bytereverse (i12 : 64 word)) /\
       read (memory :> bytes128 (word_add (word input_base) (word 112))) s = word_join (word_bytereverse (i15 : 64 word)) (word_bytereverse (i14 : 64 word)) /\
       // init_hash is stored at address hash_base.
       // bignum_from_memory (word hash_base, 8) s = init_hash
       read (memory :> bytes128 (word hash_base))                      s = word_join h_b h_a /\
       read (memory :> bytes128 (word_add (word hash_base) (word 16))) s = word_join h_d h_c /\
       read (memory :> bytes128 (word_add (word hash_base) (word 32))) s = word_join h_f h_e /\
       read (memory :> bytes128 (word_add (word hash_base) (word 48))) s = word_join h_h h_g)
  // Postcondition
  (\s. read PC s = word retpc /\       
       read X1 s = word input_base + word 128 /\
       // No more blocks are left to hash.
       read X2 s = word 0 /\ 
       // x3 points to the base address of the KTbl.
       read X3 s = word ktbl_base /\
       read (memory :> bytes128 (word hash_base)) s = word_join a b)
  // Registers (and memory locations) that may change after execution.
  (\s s'. T)
  `;;

e(REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; 
              fst SHA512_HW_EXEC; BIGNUM_FROM_MEMORY_BYTES;
              SHA512_SPEC_ONE_BLOCK_RULE]);;
e(REPEAT STRIP_TAC);;
e(ENSURES_INIT_TAC "s0");;

(* Reduce 16*<n> in the assumptions to a concrete number, otherwise 
   we may lose the loads' effects during simulation. *)
e(RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV NUM_RED_CONV)));;

(* #### Expand and simplify the specification function compression. #### *)
e(COMPRESSION_EXPAND_INIT_TAC);;   
e(MAP_EVERY (fun i -> (COMPRESSION_EXPAND_TAC THEN
                       ABBREV_FIRST_TERMS_IN_ASM_TAC i "ct1_" `compression_t1` THEN
                       ABBREV_FIRST_TERMS_IN_ASM_TAC i "ct2_" `compression_t2`))
            (0--15));;
(* I want to have ms_16 as the RHS in the equality of two terms:
   one in terms of message_schedule and the other in terms of 
   message_schedule_word. This is to mimic memoization: the former 
   will help in reusing already-computed values when expanding the
   message_schedule (the specification function) and the latter will 
   be used during symbolic simulation. We also get the equality of 
   these for "free". *)
e(ABBREV_FIRST_TERMS_IN_ASM_TAC 16 "ms_" `message_schedule`);;
e(LABEL_TAC "H_ms_16" 
              (ASSUME `(message_schedule
                        (\j. EL j [i0; i1; i2; i3; 
                                   i4; i5; i6; i7; 
                                   i8; i9; i10; i11; 
                                   i12; i13; i14; i15])
                       16) = ms_16`));;
e(USE_THEN "H_ms_16" 
            (fun th -> 
              let th' = REWRITE_RULE [MESSAGE_SCHEDULE_16_RULE] th in
              ASSUME_TAC th'));;

e(COMPRESSION_EXPAND_TAC THEN
  ABBREV_FIRST_TERMS_IN_ASM_TAC 16 "ct1_" `compression_t1` THEN
  ABBREV_FIRST_TERMS_IN_ASM_TAC 16 "ct2_" `compression_t2`);; 
e(ABBREV_FIRST_TERMS_IN_ASM_TAC 17 "ms_" `message_schedule`);;
e(LABEL_TAC "H_ms_17" 
            (ASSUME `(message_schedule
                      (\j. EL j [i0; i1; i2; i3; 
                                 i4; i5; i6; i7; 
                                 i8; i9; i10; i11; 
                                 i12; i13; i14; i15])
                     17) = ms_17`));;
e(USE_THEN "H_ms_17" 
            (fun th -> 
                let th' = REWRITE_RULE [MESSAGE_SCHEDULE_17_RULE] th in
                ASSUME_TAC th'));;

(* Snorkeling COMPRESSION_UNWIND_TAC for a better interactive experience. *)
e(MAP_EVERY (fun n -> COMPRESSION_UNWIND_TAC n) (18--40));;
e(MAP_EVERY (fun n -> COMPRESSION_UNWIND_TAC n) (41--60));;
e(MAP_EVERY (fun n -> COMPRESSION_UNWIND_TAC n) (61--79));;

e(COMPRESSION_EXPAND_TAC);;
e(ABBREV_FIRST_TERMS_IN_ASM_TAC 79 "ct1_" `compression_t1` THEN
  ABBREV_FIRST_TERMS_IN_ASM_TAC 79 "ct2_" `compression_t2`);;
e(DISCARD_MATCHING_ASSUMPTIONS [`message_schedule m i = var`]);;  
e(RULE_ASSUM_TAC(REWRITE_RULE[add8; PAIR_EQ]));;

(* #### End of simplifying the specification function compression. #### *)

(* #### Begin Symbolic Simulation. #### *)

e(ARM_STEPS_TAC SHA512_HW_EXEC (1--14));;
(* (FIXME) Speed this up.
    Simulate and simplify the REV64 instructions. *)
e(MAP_EVERY (fun n -> ARM_STEPS_TAC SHA512_HW_EXEC [n] THEN 
                      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
                      RULE_ASSUM_TAC(REWRITE_RULE[WORD_BITMANIP_SIMP_LEMMAS; REV64_BITMANIP_SIMP_LEMMAS]))
           (15--22));;
(* Simulate the unconditional branch instruction. *)
e(ARM_STEPS_TAC SHA512_HW_EXEC (16--16));;
(* Now, we are poised to execute the body of the loop. *)

(* 0x3cc10478;  ldr q24, [x3], #16 *)
e(ARM_STEPS_TAC SHA512_HW_EXEC (17--25));;

(* A crude but quick way of checking if structure sharing is broken: 
   the following functions ought to occur in the goal the specified number of 
   times (stemming from the specification). If the count is more, then 
   the program isn't generating identical terms. 

   compression_t1: 80
   compression_t2: 80
   message_schedule_word: 64
*)

(* (1--32)/32: 5  12-instruction sub-blocks *)
e(ARM_STEPS_TAC SHA512_HW_EXEC (26--37));;
e(ARM_STEPS_TAC SHA512_HW_EXEC (38--49));;
(*
Structure sharing broken; e.g.:
program: compression_t2 (ct2_1 + ct1_1) (ct1_0 + ct2_0) h_a)
spec:    compression_t2 (ct1_1 + ct2_1) (ct1_0 + ct2_0) h_a = ct2_2
*)

(* ... TODO ... (Total instructions: 514) *)


(* (1--7)/7: 7  11-instruction sub-blocks *)

(* 1/1: 1  11-instruction sub-block *)

(* 1/1: 1  5-instruction sub-block *)

(* Now we are at the end of the loop. *)

(* 1/1: 1  6-instruction sub-block *)

(* #### End Symbolic Simulation. #### *)

e(ENSURES_FINAL_STATE_TAC);;
e(ASM_REWRITE_TAC[]);;
