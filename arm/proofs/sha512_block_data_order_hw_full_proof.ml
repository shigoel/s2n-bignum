(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA512 with hardware intrinsics.                                          *)
(* ========================================================================= *)

needs "arm/proofs/sha512_block_data_order_hw.ml";;

(* ------------------------------------------------------------------------- *)

(* FIXME: Not implemented in HOL Light? *)
let strip_imp = splitlist dest_imp;;

(* Augment the OCaml reference variable that stores rewrite rules that will be
   applied after each step of symbolic simulation. *)

extra_word_CONV := 
   (GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; 
                        REV64_BITMANIP_SIMP_LEMMAS; 
                        SHA512SU1_SU0; SHA512H_RULE; SHA512H2_RULE]) ::
                        !extra_word_CONV;;
 
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

arm_print_log := false;;
components_print_log := true;;

g`forall pc retpc sp num_blocks hash_base ktbl_base input_base   
  // input message
  (m:num->num->int64)
  // 0 <= ib < num_blocks: used to iterate over all input blocks.
  // 0 <= ib /\ ib < num_blocks /\
  // final hash
  a b c d e f g h.
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
(a, b, c, d, e, f, g, h) = sha512 m num_blocks
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
       read (memory :> bytes128 (word hash_base)) s = word_join b a /\
       read (memory :> bytes128 (word_add (word hash_base) (word 16))) s = word_join d c /\
       read (memory :> bytes128 (word_add (word hash_base) (word 32))) s = word_join f e /\
       read (memory :> bytes128 (word_add (word hash_base) (word 48))) s = word_join h g /\
       // Registers Q0-Q3 also contain the final hash.
       read Q0 s = word_join b a /\
       read Q1 s = word_join d c /\
       read Q2 s = word_join f e /\
       read Q3 s = word_join h g)  
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
             MAYCHANGE SOME_FLAGS)
  `;;

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
  `pc + 92`        (* loop body start PC *)
  `pc + 2028`      (* loop backedge branch PC *)
  (* loop invariant *)
  `\i s.
         (let num_blocks_hashed = num_blocks - i in
          let num_bytes_hashed = (word_mul (word num_blocks_hashed) (word 128)) in
          let (a', b', c', d', e', f', g', h') = sha512 m num_blocks_hashed in
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
          read Q0 s = word_join b' a' /\
          read Q1 s = word_join d' c' /\
          read Q2 s = word_join f' e' /\
          read Q3 s = word_join h' g' /\  
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
e(ASM_REWRITE_TAC[]);;
(* TODO: prove input_blocks_in_mem_p conclusion. *)

(* ---------------------------------------------------------------------- *)

(*
Simulation of the loop body: from pc+92 to PC+2028.
*)
(* e(UNDISCH_TAC `a,b,c,d,e,f,g,h = sha512 m num_blocks`);; *)
(* e(ONCE_ASM_SIMP_TAC[SHA512_UNWIND_RULE]);; *)
(* e(DISCH_TAC);; *)
e(ONCE_SIMP_TAC[KTBL_IN_MEM_P_DEF]);;
e(CONV_TAC(TOP_DEPTH_CONV let_CONV));;
e(CONV_TAC(TOP_DEPTH_CONV WORD_RED_CONV));;
e(CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV));;
e(REPEAT STRIP_TAC);;
e(ENSURES_INIT_TAC "s23");;

e(ARM_STEPS_TAC SHA512_HW_EXEC (24--100));;
e(ARM_STEPS_TAC SHA512_HW_EXEC (101--200));;
e(ARM_STEPS_TAC SHA512_HW_EXEC (201--300));;
e(ARM_STEPS_TAC SHA512_HW_EXEC (301--400));;
e(ARM_STEPS_TAC SHA512_HW_EXEC (401--500));;
e(ARM_STEPS_TAC SHA512_HW_EXEC (501--507));;
e(ENSURES_FINAL_STATE_TAC);;
e(IMP_REWRITE_TAC[VAL_EQ_0; WORD_ADD; WORD_SUB_ADD; WORD_EQ_0; DIMINDEX_64]);;
e(IMP_REWRITE_TAC [ARITH_RULE `num_blocks * 128 < 2 EXP 64 /\ i < num_blocks ==> i < 2 EXP 64`]);;
e(ASM_CASES_TAC `i = 0`);;

e(ASM_REWRITE_TAC[]);;
e(CONV_TAC(TOP_DEPTH_CONV NUM_RED_CONV));;
e(REWRITE_TAC[SUB_0]);;
e(ASM_REWRITE_TAC[WORD_SUB]);;
e(IMP_REWRITE_TAC [ARITH_RULE `0 < num_blocks ==> 1 <= num_blocks`]);;
e(CONV_TAC WORD_BLAST);;

e(ASM_REWRITE_TAC[]);;
e(IMP_REWRITE_TAC [ARITH_RULE `~(i + 1 = 0)`]);;
e(ASM_REWRITE_TAC[WORD_SUB]);;
e(IMP_REWRITE_TAC[ARITH_RULE `i < num_blocks ==> i + 1 <= num_blocks /\ i <= num_blocks`]);;
e(CONV_TAC WORD_BLAST);;

(* ---------------------------------------------------------------------- *)

(*
Simulation of the loop backjump -- (pc + 2028) to (pc + 92).
*)
e(ONCE_SIMP_TAC[KTBL_IN_MEM_P_DEF]);;
e(CONV_TAC(TOP_DEPTH_CONV let_CONV));;
e(CONV_TAC(TOP_DEPTH_CONV WORD_RED_CONV));;
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

(* ---------------------------------------------------------------------- *)

(*
Simulation of the basic block following the loop.
*)
(* .. TODO .. *)

(* ---------------------------------------------------------------------- *)