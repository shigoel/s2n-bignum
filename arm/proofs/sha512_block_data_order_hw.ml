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

let MAJ_ABC_EQ_CAB = prove(
  `!(a:(64)word) (b:(64)word) (c:(64)word).
    Maj(a,b,c) = Maj(c,a,b)`,
    REWRITE_TAC[Maj_DEF] THEN
    CONV_TAC WORD_BLAST);;  

let SHA512H2_RULE = prove(
`!(x1:(64)word) (x0:(64)word) 
  (y1:(64)word) (y0:(64)word)
  (z1:(64)word) (z0:(64)word).
  sha512h2 (word_join x1 x0) (word_join y1 y0) (word_join z1 z0) = 
  word_join ((compression_t2 z0 y0 z1) + x1) 
            ((compression_t2 ((compression_t2 z0 y0 z1) + x1) z0 z1) + x0) :(128)word`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sha512h2; compression_t2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_BITMANIP_SIMP_LEMMAS; REV64_BITMANIP_SIMP_LEMMAS] THEN
  REWRITE_TAC[WORD_ADD_AC] THEN
  SUBST1_TAC(ISPECL [`y0:64 word`; `z1:64 word`;`z0:64 word`] MAJ_ABC_EQ_CAB) THEN
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

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

arm_print_log := false;;
components_print_log := true;;

(* let tmp = WORD_REDUCE_CONV `word_bytereverse (word 0x11223344556677889900AABBCCDDEEFF):int128`;; *)
(* let tmp = WORD_REDUCE_CONV `(word_join (word_bytereverse (word 0x1122334455667788):int64) (word_bytereverse (word 0xAABBCCDDEEFF0011):int64)) : 128 word`;; *)
(* Printf.printf "%x\n" 857870592;; *)

g`forall pc retpc sp num_blocks hash_base ktbl_base input_base   
  // input_block 
  i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15.
// We fix the number of blocks to be hashed to 1 for now.
num_blocks = 1 /\
// No aliasing among all memory regions of interest.
PAIRWISE nonoverlapping
  [(word sp:int64, 128); (word pc:int64, LENGTH sha512_hw_mc); 
   (word hash_base:int64, 64);
   (word input_base:int64, 16 * 8 * num_blocks);
   (word ktbl_base:int64, 80 * 8)]
// (a, b, c, d, e, f, g, h) = 
//     sha512 (\i:num j:num. EL j 
//               [i0; i1; i2; i3; i4; i5; i6; i7; i8; i9;i10; i11; i12; i13; i14; i15]) 
//             1
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
       read (memory :> bytes128 (word ktbl_base))                           s = word_join  K_1  K_0 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word 16)))      s = word_join  K_3  K_2 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*2))))  s = word_join  K_5  K_4 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*3))))  s = word_join  K_7  K_6 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*4))))  s = word_join  K_9  K_8 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*5))))  s = word_join K_11 K_10 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*6))))  s = word_join K_13 K_12 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*7))))  s = word_join K_15 K_14 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*8))))  s = word_join K_17 K_16 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*9))))  s = word_join K_19 K_18 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*10)))) s = word_join K_21 K_20 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*11)))) s = word_join K_23 K_22 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*12)))) s = word_join K_25 K_24 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*13)))) s = word_join K_27 K_26 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*14)))) s = word_join K_29 K_28 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*15)))) s = word_join K_31 K_30 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*16)))) s = word_join K_33 K_32 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*17)))) s = word_join K_35 K_34 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*18)))) s = word_join K_37 K_36 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*19)))) s = word_join K_39 K_38 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*20)))) s = word_join K_41 K_40 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*21)))) s = word_join K_43 K_42 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*22)))) s = word_join K_45 K_44 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*23)))) s = word_join K_47 K_46 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*24)))) s = word_join K_49 K_48 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*25)))) s = word_join K_51 K_50 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*26)))) s = word_join K_53 K_52 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*27)))) s = word_join K_55 K_54 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*28)))) s = word_join K_57 K_56 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*29)))) s = word_join K_59 K_58 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*30)))) s = word_join K_61 K_60 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*31)))) s = word_join K_63 K_62 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*32)))) s = word_join K_65 K_64 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*33)))) s = word_join K_67 K_66 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*34)))) s = word_join K_69 K_68 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*35)))) s = word_join K_71 K_70 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*36)))) s = word_join K_73 K_72 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*37)))) s = word_join K_75 K_74 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*38)))) s = word_join K_77 K_76 /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*39)))) s = word_join K_79 K_78 /\ 
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
       read (memory :> bytes128 (word_add (word hash_base) (word 48))) s = word_join h_h h_g
       // (a, b, c, d, e, f, g, h) = 
       //    sha512 (\i:num j:num. (word (bignum_from_memory (word (input_base + 16*8*i + 8*j), 1) s)))
       //            1
       )
  // Postcondition
  (\s. read PC s = word retpc /\       
       read X1 s = word input_base + word 128 /\
       // No more blocks are left to hash.
       read X2 s = word 0 /\ 
       // x3 points to the base address of the KTbl.
       read X3 s = word ktbl_base
       // read (memory :> bytes128 (word hash_base)) s = word_join a b
       )
  // Registers (and memory locations) that may change after execution.
  (\s s'. T)
  `;;

e(REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; fst SHA512_HW_EXEC; BIGNUM_FROM_MEMORY_BYTES]);;
e(REPEAT STRIP_TAC);;
e(ENSURES_INIT_TAC "s0");;

(* e(BIGNUM_DIGITIZE_TAC "i_" `read (memory :> bytes (word input_base, 8 * 16)) s0`);; *)
(* e(BIGNUM_DIGITIZE_TAC "h_" `read (memory :> bytes (word hash_base, 8 * 8)) s0`);; *)
(* e(BIGNUM_DIGITIZE_TAC "k_" `read (memory :> bytes (word ktbl_base, 8 * 80)) s0`);; *)

(* e(ARM_STEPS_TAC SHA512_HW_EXEC (1--514));; *)
(* e(ARM_VSTEPS_TAC SHA512_HW_EXEC (1--3));; *)

e(ARM_STEPS_TAC SHA512_HW_EXEC (1--14));;
(* Simulate and simplify the REV64 instructions. *)
e(MAP_EVERY (fun n -> ARM_STEPS_TAC SHA512_HW_EXEC [n] THEN 
                    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
                    RULE_ASSUM_TAC(REWRITE_RULE[WORD_BITMANIP_SIMP_LEMMAS; REV64_BITMANIP_SIMP_LEMMAS]))
           (15--22));;
(* Simulate the unconditional branch instruction. *)
e(ARM_STEPS_TAC SHA512_HW_EXEC (16--16));;
(* Now, we are poised to execute the body of the loop. *)

(* 0x3cc10478;  ldr	   q24, [x3], #16 *)
e(ARM_STEPS_TAC SHA512_HW_EXEC (17--25));; 
e(RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)));;
e(RULE_ASSUM_TAC(REWRITE_RULE[WORD_BITMANIP_SIMP_LEMMAS; REV64_BITMANIP_SIMP_LEMMAS]));;

(* 1/32: 12 instruction sub-block beginning at
    0x3cc10479;  ldr	   q25, [x3], #16  *)
e(ARM_STEPS_TAC SHA512_HW_EXEC (26--37));; 
e(RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)));;
e(RULE_ASSUM_TAC(REWRITE_RULE[WORD_BITMANIP_SIMP_LEMMAS; REV64_BITMANIP_SIMP_LEMMAS; 
                               SHA512SU1_SU0; SHA512H_RULE; SHA512H2_RULE]));;

(* 2/32: 12 instruction sub-block beginning at
   0x3cc10478; ldr	   q24, [x3], #16 *)
e(ARM_STEPS_TAC SHA512_HW_EXEC (38--49));; 
e(RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)));;
e(RULE_ASSUM_TAC(REWRITE_RULE[WORD_BITMANIP_SIMP_LEMMAS; REV64_BITMANIP_SIMP_LEMMAS; 
                              SHA512SU1_SU0; SHA512H_RULE; SHA512H2_RULE]));;

(* ... *)
e(ENSURES_FINAL_STATE_TAC);;
e(ASM_REWRITE_TAC[]);;
