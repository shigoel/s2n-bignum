(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA512 with hardware intrinsics.                                          *)
(* ========================================================================= *)

needs "arm/proofs/sha512_block_data_order_hw_program.ml";;

(* ------------------------------------------------------------------------- *)
(* First, some helper lemmas                                                 *)
(* ------------------------------------------------------------------------- *)

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
  word_join ((compression_t1 e f g h) + k0 + i0)
            ((compression_t1 (d + (compression_t1 e f g h + k0 + i0)) e f g) + k1 + i1)`,
  REWRITE_TAC[sha512h; compression_t1] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_BITMANIP_SIMP_LEMMAS; REV64_BITMANIP_SIMP_LEMMAS] THEN
  REWRITE_TAC[WORD_ADD_AC]);;

(* Simplifying the SHA512 specification functions. *)

let SHA512_UNWIND_RULE = prove(  
 `forall m n.
  0 < n ==>
  sha512 m n = 
  add8 (compression 0 (sha512 m (n - 1)) (m (n - 1))) (sha512 m (n - 1))`,  
  ASM_REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  REPEAT STRIP_TAC THEN
  CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [sha512])) THEN
  ASM_SIMP_TAC[sha512_block] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REFL_TAC);;

let SHA512_SPEC_ONE_BLOCK_RULE = prove(
`forall m. sha512 m 1 = add8 (compression 0 h_init (m 0)) h_init`,
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [sha512] THEN CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV) THEN
    ONCE_REWRITE_TAC [sha512] THEN CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV) THEN
    REWRITE_TAC[sha512_block] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV));;  

let MESSAGE_SCHEDULE_I_LT_16_RULE = prove(    
 `forall n mi.
  n < 16 ==>
  (message_schedule mi n) = (mi n)`,
  REPEAT STRIP_TAC THEN
  ONCE_ASM_REWRITE_TAC [message_schedule] THEN
  ASM_REWRITE_TAC []);;

let MESSAGE_SCHEDULE_1_16_RULES = prove(
 `forall mi.
 (message_schedule mi  0) = (mi 0) /\
 (message_schedule mi  1) = (mi 1) /\
 (message_schedule mi  2) = (mi 2) /\
 (message_schedule mi  3) = (mi 3) /\
 (message_schedule mi  4) = (mi 4) /\
 (message_schedule mi  5) = (mi 5) /\
 (message_schedule mi  6) = (mi 6) /\
 (message_schedule mi  7) = (mi 7) /\
 (message_schedule mi  8) = (mi 8) /\
 (message_schedule mi  9) = (mi 9) /\
 (message_schedule mi 10) = (mi 10) /\
 (message_schedule mi 11) = (mi 11) /\
 (message_schedule mi 12) = (mi 12) /\
 (message_schedule mi 13) = (mi 13) /\
 (message_schedule mi 14) = (mi 14) /\
 (message_schedule mi 15) = (mi 15)`,
  IMP_REWRITE_TAC[MESSAGE_SCHEDULE_I_LT_16_RULE] THEN 
  CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV));;

let MESSAGE_SCHEDULE_16_RULE = prove(
   `forall mi.
   (message_schedule mi 16) =
   message_schedule_word (mi 14) (mi 9) (mi 1) (mi 0)`,
   REPEAT STRIP_TAC THEN
   ONCE_ASM_REWRITE_TAC [message_schedule] THEN
   CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV) THEN
   REWRITE_TAC[MESSAGE_SCHEDULE_1_16_RULES]);;

let MESSAGE_SCHEDULE_17_RULE = prove(
`forall mi.
   (message_schedule mi 17) =
    message_schedule_word (mi 15) (mi 10) (mi 2) (mi 1)`,
    REPEAT STRIP_TAC THEN
    ONCE_ASM_REWRITE_TAC [message_schedule] THEN
    CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV) THEN
    REWRITE_TAC[MESSAGE_SCHEDULE_1_16_RULES]);;

let sha512_loop_inv_helper_lemma_1 = prove(
`forall input_base:int64 num_blocks:int64. 
 (word_sub
  (input_base + word 128 + word_mul (word_sub (num_blocks) (word 1)) (word 128))
  (word 128) + word 128) =
 input_base + (word_mul (num_blocks) (word 128))`,
CONV_TAC WORD_BLAST);;

let sha512_loop_inv_helper_lemma_2 = prove(
 `forall input_base:int64 num_blocks:int64. 
 (input_base + word 128 + word_mul (word_sub (num_blocks) (word (i + 1))) (word 128)) + word 128 =
  input_base + word_mul (word_sub (num_blocks) (word i)) (word 128) + word 128`,
 CONV_TAC WORD_BLAST);;    

(* ------------------------------------------------------------------------- *)
(* Custom tactics                                                            *)
(* ------------------------------------------------------------------------- *)

let COMPRESSION_EXPAND_INIT_TAC = 
  (RULE_ASSUM_TAC(ONCE_REWRITE_RULE[compression]) THEN
   RULE_ASSUM_TAC((CONV_RULE(TOP_DEPTH_CONV let_CONV))) THEN
   RULE_ASSUM_TAC((CONV_RULE(TOP_DEPTH_CONV NUM_RED_CONV))) THEN
   RULE_ASSUM_TAC((REWRITE_RULE[MESSAGE_SCHEDULE_1_16_RULES])));;
 
let COMPRESSION_EXPAND_TAC = 
  (RULE_ASSUM_TAC(ONCE_REWRITE_RULE[compression_update]) THEN
   RULE_ASSUM_TAC(CONV_RULE (TOP_DEPTH_CONV let_CONV)) THEN
   RULE_ASSUM_TAC(ONCE_REWRITE_RULE[SHA512_A; SHA512_B; SHA512_C; SHA512_D; SHA512_E; SHA512_F; SHA512_G; SHA512_H]) THEN
   RULE_ASSUM_TAC(ONCE_REWRITE_RULE[compression]) THEN
   RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
   RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV NUM_RED_CONV)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[MESSAGE_SCHEDULE_1_16_RULES]));;

(* 
Abbreviate the first occurrence of a function call of fn
found among the assumptions. Note that we do not abbreviate if
the matched assumption's RHS is a variable whose name is a prefix 
of var; this is to avoid re-abbreviating previously abbreviated 
assumptions.
*)   
let ABBREV_FIRST_UNABBREV_OCC_IN_ASM_TAC (n:int) (var:string) (fn:term) (asl, w as gl) = 
  let ty = `:((64)word)` in
  let v = mk_var(var ^ string_of_int n, ty) in
  let (f : term -> term -> bool) = (fun pat tm -> fst (strip_comb tm) = pat) in
  let g = fun pat -> 
            find
              (fun (_, th) ->
                  let tm = concl th in
                  try let _ = find_term (f pat) tm in
                    ((not (is_var (rhs tm))) ||
                     (not (String.starts_with ~prefix:var (string_of_term (rhs tm)))))
                  with Failure _ -> false)
             (rev asl) in        
  let (_, matching_assum) = g fn in  
  let occ = find_term (f fn) (concl matching_assum) in  
  ABBREV_TAC (mk_eq(v, occ)) gl;;    

(*
We unwind a call of the compression function with n as the first 
argument, creating abbreviations for unique calls of compression_t1, 
compression_t2, and message_schedule along the way. 

compression_t1 ?a ?b ?c ?d = ct1_<n-1>
compression_t2 ?a ?b ?c = ct2_<n-1>
message_schedule ?m n = ms_<n>

Additionally, we introduce another equation where the call of 
message_schedule above is simplified to an equivalent call of
message_schedule_word (note that the variable in the RHS is still
ms_<n>).

message_schedule_word ?a ?b ?c ?d = ms_<n>

This simplification is done by expanding the call of 
message_schedule once and rewriting away subsequent 
message_schedule calls using previously introduced abbreviations.

As we see, the message_schedule abbreviations are reused when 
expanding the specification function. Those about 
message_schedule_word will come in useful during symbolic simulation -- 
ref. the theorem SHA512SU1_SU0 which rewrites the SHA512SU0/SU1 
instructions in terms of message_schedule_word.

Once the specification is expanded away, we will discard all 
message_schedule assumptions but the ms_i variables will be retained
in the RHS of the message_schedule_word assumptions and in the 
expanded specification. These ms_i variables will help in establishing 
the equivalence of the specification and the implementation.
*)  
let COMPRESSION_UNWIND_TAC (n:int) : tactic =
  if n < 18 || n > 80 then 
    failwith "COMPRESSION_UNWIND_TAC: constraint on n violated! Constraint: 18 <= n <= 80."
  else
    let pat1 = `message_schedule m i = var` in
    let h_ms = ("H_ms_" ^ (string_of_int n)) in
    let ms_lhs = mk_comb 
                  (`message_schedule (m (num_blocks - (i + 1)))`, (mk_small_numeral n)) in
    let ms_rhs = mk_var(("ms_" ^ (string_of_int n)), `:((64)word)`) in
    let ms_term = mk_eq(ms_lhs, ms_rhs) in    
    fun (asl, w as gl) ->
      let abbrev_asms =
        (filter (fun (_, th) -> (can (term_match [] pat1) (concl th)))
                asl) in
      let abbrev_thms = map (fun (_, th) -> th) abbrev_asms in
      let abbrev_thms = MESSAGE_SCHEDULE_1_16_RULES :: abbrev_thms in
      (COMPRESSION_EXPAND_TAC THEN
       ABBREV_FIRST_UNABBREV_OCC_IN_ASM_TAC (n - 1) "ct1_" `compression_t1` THEN
       ABBREV_FIRST_UNABBREV_OCC_IN_ASM_TAC (n - 1) "ct2_" `compression_t2` THEN
       ABBREV_FIRST_UNABBREV_OCC_IN_ASM_TAC n "ms_" `message_schedule` THEN
       LABEL_TAC h_ms (ASSUME ms_term) THEN
       REMOVE_THEN h_ms 
        (fun th -> 
          let th' = ONCE_REWRITE_RULE [message_schedule] th in
          let th' = CONV_RULE(TOP_DEPTH_CONV NUM_RED_CONV) th' in
          let th' = REWRITE_RULE abbrev_thms th' in
          ASSUME_TAC th')) gl;;  

(*
Rewrite with assumptions of the form 
compression_t1 ... = var and
compression_t2 ... = var 
at the assumption of the form
read <?> s? = <term>
*)
let ABBREV_CT1_CT2_IN_STATE_COMPONENTS_TAC : tactic =
  let pat1 = `compression_t1 a b c d = var`
  and pat2 = `compression_t2 x y z = var`
  and pat3 = `read reg state = term` in
  fun (asl, w) ->
    let abbrev_asms =
      (filter (fun (_, th) ->
                (can (term_match [] pat1) (concl th)) ||
                 can (term_match [] pat2) (concl th))
              asl) in
    let abbrev_thms = map (fun (_, th) -> th) abbrev_asms in
    let asl' = mapfilter
                (fun (s,th) ->
                  if can (term_match [] pat3) (concl th) then
                    (s, (PURE_REWRITE_RULE abbrev_thms th))
                  else (s,th))
                asl in
    ALL_TAC (asl', w);;      
    
(* FIXME: Not implemented in HOL Light? *)
let strip_imp = splitlist dest_imp;;    

(* ------------------------------------------------------------------------- *)
(* Helper functions                                                          *)
(* ------------------------------------------------------------------------- *)

(*
  We use word_bytereverse below for each input word because they 
  are in big-endian format, and this Arm machine is little-endian. 
  The SHA512 specification expects the input as a big-endian value, and
  REV64 instructions in the program change the endianness of 
  the input words, so we will subsequently see 
  (word_bytereverse (word_bytereverse i0)) = i0 in the rest of the program.
*)                        
let INPUT_BLOCKS_IN_MEM_P_DEF = define
  `input_blocks_in_mem_p (b:num) (input_base:(64)word) (m:num->num->int64) s : bool = 
   (read (memory :> bytes128 (word_add input_base (word ((128 * b)))))            s = word_join (word_bytereverse (m b  1)) (word_bytereverse (m b  0)) /\
    read (memory :> bytes128 (word_add input_base (word ((16 * 1) + (128 * b))))) s = word_join (word_bytereverse (m b  3)) (word_bytereverse (m b  2)) /\
    read (memory :> bytes128 (word_add input_base (word ((16 * 2) + (128 * b))))) s = word_join (word_bytereverse (m b  5)) (word_bytereverse (m b  4)) /\
    read (memory :> bytes128 (word_add input_base (word ((16 * 3) + (128 * b))))) s = word_join (word_bytereverse (m b  7)) (word_bytereverse (m b  6)) /\
    read (memory :> bytes128 (word_add input_base (word ((16 * 4) + (128 * b))))) s = word_join (word_bytereverse (m b  9)) (word_bytereverse (m b  8)) /\
    read (memory :> bytes128 (word_add input_base (word ((16 * 5) + (128 * b))))) s = word_join (word_bytereverse (m b 11)) (word_bytereverse (m b 10)) /\
    read (memory :> bytes128 (word_add input_base (word ((16 * 6) + (128 * b))))) s = word_join (word_bytereverse (m b 13)) (word_bytereverse (m b 12)) /\
    read (memory :> bytes128 (word_add input_base (word ((16 * 7) + (128 * b))))) s = word_join (word_bytereverse (m b 15)) (word_bytereverse (m b 14)))`;;

let KTBL_IN_MEM_P_DEF = define
  `ktbl_in_mem_p (ktbl_base:(64)word) s : bool = 
   (read (memory :> bytes128 ktbl_base)                           s = word_join (K  1) (K  0) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word 16)))      s = word_join (K  3) (K  2) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*2))))  s = word_join (K  5) (K  4) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*3))))  s = word_join (K  7) (K  6) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*4))))  s = word_join (K  9) (K  8) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*5))))  s = word_join (K 11) (K 10) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*6))))  s = word_join (K 13) (K 12) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*7))))  s = word_join (K 15) (K 14) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*8))))  s = word_join (K 17) (K 16) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*9))))  s = word_join (K 19) (K 18) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*10)))) s = word_join (K 21) (K 20) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*11)))) s = word_join (K 23) (K 22) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*12)))) s = word_join (K 25) (K 24) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*13)))) s = word_join (K 27) (K 26) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*14)))) s = word_join (K 29) (K 28) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*15)))) s = word_join (K 31) (K 30) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*16)))) s = word_join (K 33) (K 32) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*17)))) s = word_join (K 35) (K 34) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*18)))) s = word_join (K 37) (K 36) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*19)))) s = word_join (K 39) (K 38) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*20)))) s = word_join (K 41) (K 40) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*21)))) s = word_join (K 43) (K 42) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*22)))) s = word_join (K 45) (K 44) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*23)))) s = word_join (K 47) (K 46) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*24)))) s = word_join (K 49) (K 48) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*25)))) s = word_join (K 51) (K 50) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*26)))) s = word_join (K 53) (K 52) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*27)))) s = word_join (K 55) (K 54) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*28)))) s = word_join (K 57) (K 56) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*29)))) s = word_join (K 59) (K 58) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*30)))) s = word_join (K 61) (K 60) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*31)))) s = word_join (K 63) (K 62) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*32)))) s = word_join (K 65) (K 64) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*33)))) s = word_join (K 67) (K 66) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*34)))) s = word_join (K 69) (K 68) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*35)))) s = word_join (K 71) (K 70) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*36)))) s = word_join (K 73) (K 72) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*37)))) s = word_join (K 75) (K 74) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*38)))) s = word_join (K 77) (K 76) /\ 
    read (memory :> bytes128 (word_add ktbl_base (word (16*39)))) s = word_join (K 79) (K 78))`;;

(* ------------------------------------------------------------------------- *)
(* Finally, the correctness proof.                                           *)
(* ------------------------------------------------------------------------- *)

(* Augment the OCaml reference variable that stores rewrite rules that will be
   applied after each step of symbolic simulation. *)          
extra_word_CONV := 
   (GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; 
                        REV64_BITMANIP_SIMP_LEMMAS; 
                        SHA512SU1_SU0; SHA512H_RULE; SHA512H2_RULE]) ::
                        !extra_word_CONV;;          


arm_print_log := false;;
components_print_log := true;;

g`forall pc retpc sp num_blocks hash_base ktbl_base input_base   
  // input message
(m:num->num->int64) 
input
// final hash
hash.
// a b c d e f g h.
// The number of blocks (each 16 * 64 bits wide) to hash must be at least 1.
0 < num_blocks /\
// The total number of blocks cannot exceed the entire memory.
num_blocks * 16 * 8 < 2 EXP 64 /\
// No aliasing among all memory regions of interest.
PAIRWISE nonoverlapping
  [(word sp:int64, 128); (word pc:int64, LENGTH sha512_hw_mc); 
   (word hash_base:int64, 64);
   (word input_base:int64, 16 * 8 * num_blocks);
   (word ktbl_base:int64, 80 * 8)] /\
hash = sha512 m num_blocks
==>
ensures arm
  // Precondition
  (\s. aligned_bytes_loaded s (word pc) sha512_hw_mc /\       
       read PC s  = word pc  /\
       aligned 16 (word sp:int64) /\ 
       read X30 s = word retpc /\
       read X0 s  = word hash_base /\
       read X1 s  = word input_base /\
       read X3 s  = word ktbl_base /\
       read X2 s  = word num_blocks /\
       read SP s  = word_add (word sp) (word 128) /\
       // KTbl constants are in the memory.
       ktbl_in_mem_p (word ktbl_base) s /\
       // Input is in the memory.
       (forall ib. 
          (0 <= ib /\ ib < num_blocks) ==> 
          (input_blocks_in_mem_p ib (word input_base) m s)) /\
       // init_hash is stored at address hash_base.
       read (memory :> bytes128 (word hash_base))                      s = word_join h_b h_a /\
       read (memory :> bytes128 (word_add (word hash_base) (word 16))) s = word_join h_d h_c /\
       read (memory :> bytes128 (word_add (word hash_base) (word 32))) s = word_join h_f h_e /\
       read (memory :> bytes128 (word_add (word hash_base) (word 48))) s = word_join h_h h_g)
  // Postcondition
  (\s. read PC s = word retpc /\
       // X0 still has the hash_base.
       read X0 s = word hash_base /\
       // X1 points past the input region.
       read X1 s = word input_base + (word_mul (word num_blocks) (word 128)) /\
       // No more blocks are left to hash.
       read X2 s = word 0 /\
       // x3 points to the base address of the KTbl.
       read X3 s = word ktbl_base /\
       // The address hash_base now contains the final hash.
       read (memory :> bytes128 (word hash_base)) s = 
        word_join (SHA512_B hash) (SHA512_A hash) /\
       read (memory :> bytes128 (word_add (word hash_base) (word 16))) s = 
        word_join (SHA512_D hash) (SHA512_C hash) /\
       read (memory :> bytes128 (word_add (word hash_base) (word 32))) s = 
        word_join (SHA512_F hash) (SHA512_E hash) /\
       read (memory :> bytes128 (word_add (word hash_base) (word 48))) s = 
        word_join (SHA512_H hash) (SHA512_G hash) /\
       // Registers Q0-Q3 also contain the final hash.
       read Q0 s = word_join (SHA512_B hash) (SHA512_A hash) /\
       read Q1 s = word_join (SHA512_D hash) (SHA512_C hash) /\
       read Q2 s = word_join (SHA512_F hash) (SHA512_E hash) /\
       read Q3 s = word_join (SHA512_H hash) (SHA512_G hash))  
  // Registers (and memory locations) that may change after execution.
  // (FIXME) Minimize this. Also, ENSURES_WHILE... tactic doesn't 
  // work with 
  // (\s s'. T)
  // because MAYCHANGE_IDEMPOT_TAC is not general enough.
  (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8;
              X9; X10; X11; X12; X13; X14; X15; X16;
              X17; X19; X20; X21; X22; X23; X24; 
              X25; X26; X27; X28; X29; SP] ,,
             MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7;
                        Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15;
                        Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23;
                        Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31] ,,
             MAYCHANGE [memory :> bytes64 (word sp + word 112);
                        memory :> bytes64 (word sp + word 120)] ,,
             MAYCHANGE [memory :> bytes128 (word hash_base); 
                        memory :> bytes128 (word_add (word hash_base) (word 16));
                        memory :> bytes128 (word_add (word hash_base) (word 32));
                        memory :> bytes128 (word_add (word hash_base) (word 48))] ,,
             MAYCHANGE SOME_FLAGS)`;;

e(REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; 
              fst SHA512_HW_EXEC; SOME_FLAGS;
              BIGNUM_FROM_MEMORY_BYTES]);;
e(CONV_TAC (TOP_DEPTH_CONV NUM_RED_CONV));;
(* Make sure that the first argument of nonoverlapping_modulo is 2 EXP 64 
   instead of 18446744073709551616 because the tactics expect the former. *)
e(REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 64`)]);;
e(REPEAT STRIP_TAC);;

e(ENSURES_WHILE_PADOWN_TAC
  `num_blocks:num` (* counter begin number *)
  `0:num`          (* counter end number *)  
  (*
  (List.nth sha512_hw_prog_asm 23);;
  (1019282552, "ldr\t   q24, [x3], #16")
  23 * 4 = 92.
  *)
  `pc + 92`        (* loop body start PC *)
  (* 
     (List.nth sha512_hw_prog_asm 507);;
     (3053437826, "cbnz    x2, 0xe80 <sha512_block_data_order_hw+0x40") 
      507 * 4 = 2028
  *)
  `pc + 2028`      (* loop backedge branch PC *)
  (* loop invariant *)
  `\i s. 
         (let num_blocks_hashed = num_blocks - i in
          let num_bytes_hashed = (word_mul (word num_blocks_hashed) (word 128)) in
          let hash' = sha512 m num_blocks_hashed in
          // SP is still aligned.
          aligned 16 (word sp:int64) /\
          // KTbl constants are still in the memory, unchanged.
          ktbl_in_mem_p (word ktbl_base) s /\
          // Input is still in the memory, unchanged.          
          (forall ib.
              (0 <= ib /\ ib < num_blocks) ==> 
              (input_blocks_in_mem_p ib (word input_base) m s)) /\
          // X0 still contains hash_base.
          read X0 s = word hash_base /\
          // In the loop body, we start loading in the NEXT message
          // block into q16-23 iff more blocks remain to be
          // hashed. Otherwise, we load in the LAST message block
          // (again) into q16-23.
          read X1 s = word_add (word input_base)   
                     (if (i:num = 0) then num_bytes_hashed
                     else (word_add num_bytes_hashed (word 128))) /\
          read X2 s = word i /\
          read X3 s = word ktbl_base /\
          read X29 s = word_add (word sp) (word 112) /\
          read X30 s = word retpc /\
          read SP s = word_add (word sp) (word 112) /\
          read (memory :> bytes64 (word_add (word sp) (word 112))) s = word_add (word sp) (word 112) /\
          read (memory :> bytes64 (word_add (word sp) (word 120))) s = word retpc /\
          read Q0 s = word_join (SHA512_B hash') (SHA512_A hash') /\
          read Q1 s = word_join (SHA512_D hash') (SHA512_C hash') /\
          read Q2 s = word_join (SHA512_F hash') (SHA512_E hash') /\
          read Q3 s = word_join (SHA512_H hash') (SHA512_G hash') /\  
          read Q16 s = (word_join (m num_blocks_hashed  1 :(64)word) (m num_blocks_hashed  0 :(64)word)) /\
          read Q17 s = (word_join (m num_blocks_hashed  3 :(64)word) (m num_blocks_hashed  2 :(64)word)) /\
          read Q18 s = (word_join (m num_blocks_hashed  5 :(64)word) (m num_blocks_hashed  4 :(64)word)) /\
          read Q19 s = (word_join (m num_blocks_hashed  7 :(64)word) (m num_blocks_hashed  6 :(64)word)) /\
          read Q20 s = (word_join (m num_blocks_hashed  9 :(64)word) (m num_blocks_hashed  8 :(64)word)) /\
          read Q21 s = (word_join (m num_blocks_hashed 11 :(64)word) (m num_blocks_hashed 10 :(64)word)) /\
          read Q22 s = (word_join (m num_blocks_hashed 13 :(64)word) (m num_blocks_hashed 12 :(64)word)) /\
          read Q23 s = (word_join (m num_blocks_hashed 15 :(64)word) (m num_blocks_hashed 14 :(64)word))) 
          /\ // loop backedge condition         
         (read ZF s <=> i = 0)`);;

e(REPEAT CONJ_TAC);;
(* 5 subgoals *)

(* ---------------------------------------------------------------------- *)

(* 
  Subgoal with the conclusion 
  `0 < num_blocks`
*)
e(ASM_REWRITE_TAC[]);;

(* ---------------------------------------------------------------------- *)

(* 
  Simulation from PC to PC+92 (i.e., basic block preceding the loop).
  Note that num_blocks_hashed = 0.
*)

e(ONCE_REWRITE_TAC[sha512; KTBL_IN_MEM_P_DEF]);;
e(CONV_TAC(TOP_DEPTH_CONV let_CONV));;
e(REWRITE_TAC[SUB_REFL; WORD_ADD_0; h_init; PAIR_EQ]);;
e(CONV_TAC(TOP_DEPTH_CONV let_CONV));;
e(IMP_REWRITE_TAC[ARITH_RULE `0 < num_blocks ==> ~(num_blocks = 0)`]);;
e(CONV_TAC(TOP_DEPTH_CONV WORD_RED_CONV));; 
e(CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV));; 
e(ENSURES_INIT_TAC "s0");;  
(* Need to instantiate ib = 0 to preserve the effects of 
   the load instructions in the following assumption:

   `forall ib.
          0 <= ib /\ ib < num_blocks
          ==> input_blocks_in_mem_p ib (word input_base) m s0`
*)
(* e(NAME_ASSUMS_TAC);;  *)
(* e(USE_THEN "H5" (fun asm -> (ASSUME_TAC (ISPECL [`0:num`] asm))));; *)
e(EVERY_ASSUM
  (fun asm ->
    if fst (strip_comb (snd (strip_imp (snd (strip_forall (concl asm)))))) = 
       `input_blocks_in_mem_p` then
          let new_asm = (SIMP_RULE [LE_0; INPUT_BLOCKS_IN_MEM_P_DEF] (ISPECL [`0:num`] asm)) in
          let new_asm = (CONV_RULE (TOP_DEPTH_CONV NUM_RED_CONV) new_asm) in
          let new_asm = ASM_REWRITE_RULE [WORD_ADD_0; ASSUME `0 < num_blocks`] new_asm in
          (LABEL_TAC "H_m0" new_asm)
    else ALL_TAC));;
e(UNDISCH_LABEL_TAC "H_m0" THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC));;

e(ARM_STEPS_TAC SHA512_HW_EXEC (1--14));;
e(MAP_EVERY (fun n ->
              ARM_STEPS_TAC SHA512_HW_EXEC [n] THEN 
              RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
              RULE_ASSUM_TAC(REWRITE_RULE[WORD_BITMANIP_SIMP_LEMMAS; REV64_BITMANIP_SIMP_LEMMAS]))
           (15--22));;
(* Simulate the unconditional branch instruction. *)
e(ARM_STEPS_TAC SHA512_HW_EXEC (23--23));;
e(ENSURES_FINAL_STATE_TAC);;
e(ASM_REWRITE_TAC[SHA512_A; SHA512_B; SHA512_C; SHA512_D; SHA512_E; SHA512_F; SHA512_G; SHA512_H]);;
(* TODO: prove input_blocks_in_mem_p conclusion. *)
e(CHEAT_TAC);;

(* ---------------------------------------------------------------------- *)

(*
Simulation of the loop body: from pc+92 to pc+2028.
*)
e(REPEAT STRIP_TAC);;
e(CONV_TAC(TOP_DEPTH_CONV let_CONV));;
e(REWRITE_TAC[ARITH_RULE `~(i + 1 = 0)`]);;
e(ONCE_SIMP_TAC[KTBL_IN_MEM_P_DEF]);;
e(CONV_TAC(TOP_DEPTH_CONV WORD_RED_CONV));; 
e(CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV));; 
e(ENSURES_INIT_TAC "s23");;

e(SUBGOAL_THEN `0 < num_blocks - i` ASSUME_TAC);;
e(ASM_ARITH_TAC);;

e(ONCE_ASM_SIMP_TAC [ISPECL [`m:num->num->int64`; `(num_blocks - i):num`] SHA512_UNWIND_RULE]);;
e(REWRITE_TAC[ARITH_RULE `(num_blocks - i - 1) = (num_blocks - (i + 1))`]);;

e(ABBREV_TAC `hash' = (sha512 m (num_blocks - (i + 1)))`);;
e(ABBREV_TAC `hash'' = (add8 (compression 0 hash' (m (num_blocks - (i + 1)))) hash')`);;


(* #### Expand and simplify the specification function compression. #### *)
(* 
   Hyp: 
  `add8 (compression 0 hash' (m (num_blocks - (i + 1)))) hash' = hash''` 
*)

e(COMPRESSION_EXPAND_INIT_TAC);;

e(MAP_EVERY (fun i -> (COMPRESSION_EXPAND_TAC THEN
                       ABBREV_FIRST_UNABBREV_OCC_IN_ASM_TAC i "ct1_" `compression_t1` THEN
                       ABBREV_FIRST_UNABBREV_OCC_IN_ASM_TAC i "ct2_" `compression_t2`))
            (0--15));;
            
e(ABBREV_FIRST_UNABBREV_OCC_IN_ASM_TAC 16 "ms_" `message_schedule`);;
e(LABEL_TAC "H_ms_16" 
              (ASSUME `(message_schedule (m (num_blocks - (i + 1))) 16) = ms_16`));;
e(REMOVE_THEN "H_ms_16" 
            (fun th -> 
              let th' = REWRITE_RULE [MESSAGE_SCHEDULE_16_RULE] th in
              ASSUME_TAC th'));;

e(COMPRESSION_EXPAND_TAC THEN
  ABBREV_FIRST_UNABBREV_OCC_IN_ASM_TAC 16 "ct1_" `compression_t1` THEN
  ABBREV_FIRST_UNABBREV_OCC_IN_ASM_TAC 16 "ct2_" `compression_t2`);; 
e(ABBREV_FIRST_UNABBREV_OCC_IN_ASM_TAC 17 "ms_" `message_schedule`);;
e(LABEL_TAC "H_ms_17" 
            (ASSUME `(message_schedule (m (num_blocks - (i + 1))) 17) = ms_17`));;
e(REMOVE_THEN "H_ms_17" 
            (fun th -> 
                let th' = REWRITE_RULE [MESSAGE_SCHEDULE_17_RULE] th in
                ASSUME_TAC th'));;

(* Snorkeling COMPRESSION_UNWIND_TAC for a better interactive experience. *)
e(MAP_EVERY (fun n -> COMPRESSION_UNWIND_TAC n) (18--40));;
e(MAP_EVERY (fun n -> COMPRESSION_UNWIND_TAC n) (41--60));;
e(MAP_EVERY (fun n -> COMPRESSION_UNWIND_TAC n) (61--79));;

e(COMPRESSION_EXPAND_TAC);;
e(ABBREV_FIRST_UNABBREV_OCC_IN_ASM_TAC 79 "ct1_" `compression_t1` THEN
  ABBREV_FIRST_UNABBREV_OCC_IN_ASM_TAC 79 "ct2_" `compression_t2`);;
(* We don't need abbreviations for message_schedule anymore -- we've 
simplified away all message_schedule calls. *)  
e(DISCARD_MATCHING_ASSUMPTIONS [`message_schedule m i = var`]);;  
e(RULE_ASSUM_TAC(REWRITE_RULE[add8; PAIR_EQ]));;
e(RULE_ASSUM_TAC(CONV_RULE (TOP_DEPTH_CONV let_CONV)));;
e(RULE_ASSUM_TAC(ONCE_REWRITE_RULE[SHA512_A; SHA512_B; SHA512_C; SHA512_D; SHA512_E; SHA512_F; SHA512_G; SHA512_H]));;
(* Normalize w.r.t. word_add *)
e(RULE_ASSUM_TAC(PURE_REWRITE_RULE[WORD_ADD_AC; WORD_ADD_0]));;

(* ############### End of simplification of compression. ############### *)


(* #### Begin Symbolic Simulation. #### *)

(* Make sure that the first argument of nonoverlapping_modulo is 2 EXP 64 
   instead of 18446744073709551616 because the tactics expect the former. *)
e(RULE_ASSUM_TAC(REWRITE_RULE[SYM(NUM_REDUCE_CONV `2 EXP 64`)]));;

(* 0x3cc10478;  ldr q24, [x3], #16 *)
e(ARM_STEPS_TAC SHA512_HW_EXEC (24--31));;
(* A crude but quick way of checking if structure sharing is broken: 
   the following functions ought to occur in the goal the specified number of 
   times (stemming from the specification). If the count is more, then 
   the program isn't generating identical terms. 

   compression_t1: 80
   compression_t2: 80
   message_schedule_word: 64
*)
(* 32 12-instruction sub-blocks: let's snorkel the simulation. *)
e(MAP_EVERY (fun n ->
              let start = 12*(n-1) + 32 in
              let stop = start + 11 in
              ARM_STEPS_TAC SHA512_HW_EXEC (start--stop) THEN
              REPEAT_N 2 (RULE_ASSUM_TAC(PURE_REWRITE_RULE[WORD_ADD_AC]) THEN 
                          ABBREV_CT1_CT2_IN_STATE_COMPONENTS_TAC))
            (1--5));;
e(MAP_EVERY (fun n ->
              let start = 12*(n-1) + 92 in
              let stop = start + 11 in
              ARM_STEPS_TAC SHA512_HW_EXEC (start--stop) THEN
              REPEAT_N 2 (RULE_ASSUM_TAC(PURE_REWRITE_RULE[WORD_ADD_AC]) THEN 
                          ABBREV_CT1_CT2_IN_STATE_COMPONENTS_TAC))
            (1--5));;            
e(MAP_EVERY (fun n ->
              let start = 12*(n-1) + 152 in
              let stop = start + 11 in
              ARM_STEPS_TAC SHA512_HW_EXEC (start--stop) THEN
              REPEAT_N 2 (RULE_ASSUM_TAC(PURE_REWRITE_RULE[WORD_ADD_AC]) THEN 
                          ABBREV_CT1_CT2_IN_STATE_COMPONENTS_TAC))
            (1--5));;       
e(MAP_EVERY (fun n ->
              let start = 12*(n-1) + 212 in
              let stop = start + 11 in
              ARM_STEPS_TAC SHA512_HW_EXEC (start--stop) THEN
              REPEAT_N 2 (RULE_ASSUM_TAC(PURE_REWRITE_RULE[WORD_ADD_AC]) THEN 
                          ABBREV_CT1_CT2_IN_STATE_COMPONENTS_TAC))
            (1--5));;                   
e(MAP_EVERY (fun n ->
              let start = 12*(n-1) + 272 in
              let stop = start + 11 in
              ARM_STEPS_TAC SHA512_HW_EXEC (start--stop) THEN
              REPEAT_N 2 (RULE_ASSUM_TAC(PURE_REWRITE_RULE[WORD_ADD_AC]) THEN 
                          ABBREV_CT1_CT2_IN_STATE_COMPONENTS_TAC))
            (1--5));;
e(MAP_EVERY (fun n ->
              let start = 12*(n-1) + 332 in
              let stop = start + 11 in
              ARM_STEPS_TAC SHA512_HW_EXEC (start--stop) THEN
              REPEAT_N 2 (RULE_ASSUM_TAC(PURE_REWRITE_RULE[WORD_ADD_AC]) THEN 
                          ABBREV_CT1_CT2_IN_STATE_COMPONENTS_TAC))
            (1--7));;

(* (1--7)/7: 7  11-instruction sub-blocks *)
e(MAP_EVERY (fun n ->
              let start = 11*(n-1) + 416 in
              let stop = start + 10 in
              ARM_STEPS_TAC SHA512_HW_EXEC (start--stop) THEN
              RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
              RULE_ASSUM_TAC(REWRITE_RULE[WORD_BITMANIP_SIMP_LEMMAS; REV64_BITMANIP_SIMP_LEMMAS]) THEN
              REPEAT_N 2 (RULE_ASSUM_TAC(PURE_REWRITE_RULE[WORD_ADD_AC]) THEN 
                          ABBREV_CT1_CT2_IN_STATE_COMPONENTS_TAC))
            (1--7));;

(* 1/1: 1  11-instruction sub-block *)
e(ARM_STEPS_TAC SHA512_HW_EXEC (493--503) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_BITMANIP_SIMP_LEMMAS; REV64_BITMANIP_SIMP_LEMMAS]) THEN
  REPEAT_N 2 (RULE_ASSUM_TAC(PURE_REWRITE_RULE[WORD_ADD_AC]) THEN 
              ABBREV_CT1_CT2_IN_STATE_COMPONENTS_TAC));;

(* 1/1: 1  Last sub-block in loop (without the CBNZ instruction) *)
e(ARM_STEPS_TAC SHA512_HW_EXEC (504--507) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_BITMANIP_SIMP_LEMMAS; REV64_BITMANIP_SIMP_LEMMAS]) THEN
  REPEAT_N 2 (RULE_ASSUM_TAC(PURE_REWRITE_RULE[WORD_ADD_AC]) THEN 
              ABBREV_CT1_CT2_IN_STATE_COMPONENTS_TAC));;

(* Now we are at the end of the loop. *)            

e(ENSURES_FINAL_STATE_TAC);;
e(ASM_REWRITE_TAC[]);;
e(IMP_REWRITE_TAC[VAL_EQ_0; WORD_ADD; WORD_SUB_ADD; WORD_EQ_0; DIMINDEX_64]);;
e(IMP_REWRITE_TAC [ARITH_RULE `num_blocks * 128 < 2 EXP 64 /\ i < num_blocks ==> i < 2 EXP 64`]);;

e(ASM_CASES_TAC `i = 0`);;

e(ASM_REWRITE_TAC[]);;
e(CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV));;
e(REWRITE_TAC[SUB_0]);;
e(ASM_REWRITE_TAC[WORD_SUB]);;
e(IMP_REWRITE_TAC [ARITH_RULE `0 < num_blocks ==> 1 <= num_blocks`]);;
e(EXPAND_TAC "hash''");;
e(ONCE_REWRITE_TAC[SHA512_A; SHA512_B; SHA512_C; SHA512_D; SHA512_E; SHA512_F; SHA512_G; SHA512_H]);;
e(SIMP_TAC[sha512_loop_inv_helper_lemma_1]);;
e(CHEAT_TAC);;

e(ASM_REWRITE_TAC[]);;
(* e(IMP_REWRITE_TAC [ARITH_RULE `~(i + 1 = 0)`]);; *)
e(ASM_REWRITE_TAC[WORD_SUB]);;
e(IMP_REWRITE_TAC[ARITH_RULE `i < num_blocks ==> i + 1 <= num_blocks /\ i <= num_blocks`]);;
e(EXPAND_TAC "hash''");;
e(ONCE_REWRITE_TAC[SHA512_A; SHA512_B; SHA512_C; SHA512_D; SHA512_E; SHA512_F; SHA512_G; SHA512_H]);;
e(SIMP_TAC[sha512_loop_inv_helper_lemma_2]);;
e(CHEAT_TAC);;

(* ---------------------------------------------------------------------- *)

(*
Simulation of the loop backjump -- (pc + 2028) to (pc + 92).
*)
e(ONCE_SIMP_TAC[KTBL_IN_MEM_P_DEF]);;
e(CONV_TAC(TOP_DEPTH_CONV let_CONV));;
e(CONV_TAC(TOP_DEPTH_CONV WORD_RED_CONV));;
e(CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV));;
e(REPEAT STRIP_TAC);;
e(ENSURES_INIT_TAC "s507");;
e(ARM_STEPS_TAC SHA512_HW_EXEC (508--508));;
e(RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD; DIMINDEX_64]));;
e(ASSUME_TAC (ARITH_RULE `num_blocks * 128 < 2 EXP 64 /\ i < num_blocks ==> i < 2 EXP 64`));;
e(UNDISCH_TAC `num_blocks * 128 < 2 EXP 64 /\ i < num_blocks ==> i < 2 EXP 64`);;
e(ASM_REWRITE_TAC[]);;
e(DISCH_TAC);;
e(UNDISCH_TAC `read PC s508 =
               (if ~(i MOD 2 EXP 64 = 0) then word (pc + 92) else word (pc + 2032))`);;
e(IMP_REWRITE_TAC[MOD_LT]);;
e(DISCH_TAC);;
e(ENSURES_FINAL_STATE_TAC);;
e(ASM_REWRITE_TAC[]);;
(* TODO: prove input_blocks_in_mem_p conclusion. *)
e(CHEAT_TAC);;

(* ---------------------------------------------------------------------- *)

(*
Simulation of the basic block following the loop -- (pc + 2028) until after 
the ret instruction.
*)
e(ONCE_SIMP_TAC[KTBL_IN_MEM_P_DEF]);;
e(CONV_TAC(TOP_DEPTH_CONV let_CONV));;
e(CONV_TAC(TOP_DEPTH_CONV WORD_RED_CONV));;
e(CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV));;
e(REPEAT STRIP_TAC);;
e(REWRITE_TAC[SUB_0]);;
e(ENSURES_INIT_TAC "s507");;
e(ARM_STEPS_TAC SHA512_HW_EXEC (508--514));;
e(ENSURES_FINAL_STATE_TAC);;
e(ASM_REWRITE_TAC[]);;

(* ---------------------------------------------------------------------- *)