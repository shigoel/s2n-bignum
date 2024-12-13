(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA512 with hardware intrinsics.                                          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/neon_helper.ml";;
needs "arm/proofs/sha512_spec.ml";;

(* --------------------------------------------------------------- *)

(*

Program inputs:
    [x0]: in-memory hash
    [x1]: input blocks    
    x2:   number of blocks to hash
    [x3]: KTbl constants

Program outputs:
    [x0]: final hash. 
    Registers q0, q1, q2, and q3 should also have the final hash.

    Memory regions of interest, so we need 5C2 = 10 non-overlapping constraints.
    1) program
    2) stack
    3) init hash
    4) ktbl constants
    5) input

Loop structure (loop begins immediately following the unconditional branch instruction):

1. Prelude: 8 instructions
   ldr (originally, ld1)
   subs
   sub
   mov
   mov
   mov
   mov
   csel

2. The following sequence of 12 instructions are repeated 32 times:
   add
   ldr (originally, ld1)
   ext
   ext
   ext
   add
   sha512su0
   ext
   sha512h
   sha512su1
   add
   sha512h2

3. The following sequence of 11 instructions are repeated 7 times:
   ldr (originally, ld1)
   add
   ldr (originally, ld1)
   ext
   ext
   ext
   add
   sha512h
   rev64
   add
   sha512h2

4. The following sequence of 11 instructions appears once:
   sub
   add
   ldr (originally, ld1)
   ext
   ext
   ext
   add
   sha512h
   rev64
   add
   sha512h2


5. Epilogue:   
   add
   add
   add
   add
   cbnz
*)

(* --------------------------------------------------------------- *)

(**
print_literal_from_elf "arm/sha512/sha512-armv8.S.o";;
Exception: Failure "ELF contains relocations".
*)

let sha512_hw_prog:int list =
  [
    (* 0xa9bf7bfd;  (*      stp     x29, x30, [sp, #-16]!                               *) *)
    (* 0x910003fd;  (*      mov     x29, sp                                             *) *)   
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 
      We replace the following three currently unsupported load instructions with 
      semantically equivalent and supported load instructions.
    *)
    (*  0x4cdf2030;  (*      ld1     { v16.16b, v17.16b, v18.16b, v19.16b }, [x1], #64   *) *) 
    (*  0x4cdf2034;  (*      ld1     { v20.16b, v21.16b, v22.16b, v23.16b }, [x1], #64   *) *)
    (*  0x4c402c00;  (*      ld1     { v0.2d, v1.2d, v2.2d, v3.2d }, [x0]                *) *)    
    0x3cc10430;      (*      ldr     q16, [x1], #16                                  *)
    0x3cc10431; 	   (*      ldr	   q17, [x1], #16                                  *)                                  
    0x3cc10432; 	   (*      ldr	   q18, [x1], #16                                  *)    
    0x3cc10433; 	   (*      ldr	   q19, [x1], #16                                  *)
    0x3cc10434; 	   (*      ldr	   q20, [x1], #16                                  *)
    0x3cc10435; 	   (*      ldr	   q21, [x1], #16                                  *)
    0x3cc10436; 	   (*      ldr	   q22, [x1], #16                                  *)
    0x3cc10437; 	   (*      ldr	   q23, [x1], #16                                  *)
    0x3dc00000; 	   (*      ldr	   q0,  [x0]                                       *)
    0x3dc00401; 	   (*      ldr	   q1,  [x0, #16]                                  *)
    0x3dc00802; 	   (*      ldr	   q2,  [x0, #32]                                  *)
    0x3dc00c03; 	   (*      ldr	   q3,  [x0, #48]                                  *)   
    (*        
       We will assume that x3 contains the location of the KTbl constants, instead of 
       computing that address in the program.
    *)
    (*  0x90000003;  (*      adrp    x3, 0x0 <sha512_block_data_order_hw+0x14>           *) *)
    (*  0x91000063;  (*      add     x3, x3, #0                                          *) *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x4e200a10;  (*      rev64   v16.16b, v16.16b                                    *)
    0x4e200a31;  (*      rev64   v17.16b, v17.16b                                    *)
    0x4e200a52;  (*      rev64   v18.16b, v18.16b                                    *)
    0x4e200a73;  (*      rev64   v19.16b, v19.16b                                    *)
    0x4e200a94;  (*      rev64   v20.16b, v20.16b                                    *)
    0x4e200ab5;  (*      rev64   v21.16b, v21.16b                                    *)
    0x4e200ad6;  (*      rev64   v22.16b, v22.16b                                    *)
    0x4e200af7;  (*      rev64   v23.16b, v23.16b                                    *)    
    0x14000001;  (*      b       0xe80 <sha512_block_data_order_hw+0x40>             *)   
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                            *) *)    
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0xf1000442;  (*      subs    x2, x2, #1                                          *)
    0xd1020024;  (*      sub     x4, x1, #128                                        *)
    0x4ea01c1a;  (*      mov     v26.16b, v0.16b                                     *)
    0x4ea11c3b;  (*      mov     v27.16b, v1.16b                                     *)
    0x4ea21c5c;  (*      mov     v28.16b, v2.16b                                     *)
    0x4ea31c7d;  (*      mov     v29.16b, v3.16b                                     *)
    0x9a841021;  (*      csel    x1, x1, x4, ne                                      *)
    0x4ef08718;  (*      add     v24.2d, v24.2d, v16.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (*      ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e034045;  (*      ext     v5.16b, v2.16b, v3.16b, #8                          *)
    0x6e024026;  (*      ext     v6.16b, v1.16b, v2.16b, #8                          *)
    0x4ef88463;  (*      add     v3.2d, v3.2d, v24.2d                                *)
    0xcec08230;  (*      sha512su0       v16.2d, v17.2d                              *)
    0x6e154287;  (*      ext     v7.16b, v20.16b, v21.16b, #8                        *)
    0xce6680a3;  (*      sha512h q3, q5, v6.2d                                       *)
    0xce678af0;  (*      sha512su1       v16.2d, v23.2d, v7.2d                       *)
    0x4ee38424;  (*      add     v4.2d, v1.2d, v3.2d                                 *)
    0xce608423;  (*      sha512h2        q3, q1, v0.2d                               *)
    0x4ef18739;  (*      add     v25.2d, v25.2d, v17.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e024085;  (*      ext     v5.16b, v4.16b, v2.16b, #8                          *)
    0x6e044006;  (*      ext     v6.16b, v0.16b, v4.16b, #8                          *)
    0x4ef98442;  (*      add     v2.2d, v2.2d, v25.2d                                *)
    0xcec08251;  (*      sha512su0       v17.2d, v18.2d                              *)
    0x6e1642a7;  (*      ext     v7.16b, v21.16b, v22.16b, #8                        *)
    0xce6680a2;  (*      sha512h q2, q5, v6.2d                                       *)
    0xce678a11;  (*      sha512su1       v17.2d, v16.2d, v7.2d                       *)
    0x4ee28401;  (*      add     v1.2d, v0.2d, v2.2d                                 *)
    0xce638402;  (*      sha512h2        q2, q0, v3.2d                               *)
    0x4ef28718;  (*      add     v24.2d, v24.2d, v18.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e044025;  (*      ext     v5.16b, v1.16b, v4.16b, #8                          *)
    0x6e014066;  (*      ext     v6.16b, v3.16b, v1.16b, #8                          *)
    0x4ef88484;  (*      add     v4.2d, v4.2d, v24.2d                                *)
    0xcec08272;  (*      sha512su0       v18.2d, v19.2d                              *)
    0x6e1742c7;  (*      ext     v7.16b, v22.16b, v23.16b, #8                        *)
    0xce6680a4;  (*      sha512h q4, q5, v6.2d                                       *)
    0xce678a32;  (*      sha512su1       v18.2d, v17.2d, v7.2d                       *)
    0x4ee48460;  (*      add     v0.2d, v3.2d, v4.2d                                 *)
    0xce628464;  (*      sha512h2        q4, q3, v2.2d                               *)
    0x4ef38739;  (*      add     v25.2d, v25.2d, v19.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e014005;  (*      ext     v5.16b, v0.16b, v1.16b, #8                          *)
    0x6e004046;  (*      ext     v6.16b, v2.16b, v0.16b, #8                          *)
    0x4ef98421;  (*      add     v1.2d, v1.2d, v25.2d                                *)
    0xcec08293;  (*      sha512su0       v19.2d, v20.2d                              *)
    0x6e1042e7;  (*      ext     v7.16b, v23.16b, v16.16b, #8                        *)
    0xce6680a1;  (*      sha512h q1, q5, v6.2d                                       *)
    0xce678a53;  (*      sha512su1       v19.2d, v18.2d, v7.2d                       *)
    0x4ee18443;  (*      add     v3.2d, v2.2d, v1.2d                                 *)
    0xce648441;  (*      sha512h2        q1, q2, v4.2d                               *)
    0x4ef48718;  (*      add     v24.2d, v24.2d, v20.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e004065;  (*      ext     v5.16b, v3.16b, v0.16b, #8                          *)
    0x6e034086;  (*      ext     v6.16b, v4.16b, v3.16b, #8                          *)
    0x4ef88400;  (*      add     v0.2d, v0.2d, v24.2d                                *)
    0xcec082b4;  (*      sha512su0       v20.2d, v21.2d                              *)
    0x6e114207;  (*      ext     v7.16b, v16.16b, v17.16b, #8                        *)
    0xce6680a0;  (*      sha512h q0, q5, v6.2d                                       *)
    0xce678a74;  (*      sha512su1       v20.2d, v19.2d, v7.2d                       *)
    0x4ee08482;  (*      add     v2.2d, v4.2d, v0.2d                                 *)
    0xce618480;  (*      sha512h2        q0, q4, v1.2d                               *)
    0x4ef58739;  (*      add     v25.2d, v25.2d, v21.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e034045;  (*      ext     v5.16b, v2.16b, v3.16b, #8                          *)
    0x6e024026;  (*      ext     v6.16b, v1.16b, v2.16b, #8                          *)
    0x4ef98463;  (*      add     v3.2d, v3.2d, v25.2d                                *)
    0xcec082d5;  (*      sha512su0       v21.2d, v22.2d                              *)
    0x6e124227;  (*      ext     v7.16b, v17.16b, v18.16b, #8                        *)
    0xce6680a3;  (*      sha512h q3, q5, v6.2d                                       *)
    0xce678a95;  (*      sha512su1       v21.2d, v20.2d, v7.2d                       *)
    0x4ee38424;  (*      add     v4.2d, v1.2d, v3.2d                                 *)
    0xce608423;  (*      sha512h2        q3, q1, v0.2d                               *)
    0x4ef68718;  (*      add     v24.2d, v24.2d, v22.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e024085;  (*      ext     v5.16b, v4.16b, v2.16b, #8                          *)
    0x6e044006;  (*      ext     v6.16b, v0.16b, v4.16b, #8                          *)
    0x4ef88442;  (*      add     v2.2d, v2.2d, v24.2d                                *)
    0xcec082f6;  (*      sha512su0       v22.2d, v23.2d                              *)
    0x6e134247;  (*      ext     v7.16b, v18.16b, v19.16b, #8                        *)
    0xce6680a2;  (*      sha512h q2, q5, v6.2d                                       *)
    0xce678ab6;  (*      sha512su1       v22.2d, v21.2d, v7.2d                       *)
    0x4ee28401;  (*      add     v1.2d, v0.2d, v2.2d                                 *)
    0xce638402;  (*      sha512h2        q2, q0, v3.2d                               *)
    0x4ef78739;  (*      add     v25.2d, v25.2d, v23.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e044025;  (*      ext     v5.16b, v1.16b, v4.16b, #8                          *)
    0x6e014066;  (*      ext     v6.16b, v3.16b, v1.16b, #8                          *)
    0x4ef98484;  (*      add     v4.2d, v4.2d, v25.2d                                *)
    0xcec08217;  (*      sha512su0       v23.2d, v16.2d                              *)
    0x6e144267;  (*      ext     v7.16b, v19.16b, v20.16b, #8                        *)
    0xce6680a4;  (*      sha512h q4, q5, v6.2d                                       *)
    0xce678ad7;  (*      sha512su1       v23.2d, v22.2d, v7.2d                       *)
    0x4ee48460;  (*      add     v0.2d, v3.2d, v4.2d                                 *)
    0xce628464;  (*      sha512h2        q4, q3, v2.2d                               *)
    0x4ef08718;  (*      add     v24.2d, v24.2d, v16.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e014005;  (*      ext     v5.16b, v0.16b, v1.16b, #8                          *)
    0x6e004046;  (*      ext     v6.16b, v2.16b, v0.16b, #8                          *)
    0x4ef88421;  (*      add     v1.2d, v1.2d, v24.2d                                *)
    0xcec08230;  (*      sha512su0       v16.2d, v17.2d                              *)
    0x6e154287;  (*      ext     v7.16b, v20.16b, v21.16b, #8                        *)
    0xce6680a1;  (*      sha512h q1, q5, v6.2d                                       *)
    0xce678af0;  (*      sha512su1       v16.2d, v23.2d, v7.2d                       *)
    0x4ee18443;  (*      add     v3.2d, v2.2d, v1.2d                                 *)
    0xce648441;  (*      sha512h2        q1, q2, v4.2d                               *)
    0x4ef18739;  (*      add     v25.2d, v25.2d, v17.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e004065;  (*      ext     v5.16b, v3.16b, v0.16b, #8                          *)
    0x6e034086;  (*      ext     v6.16b, v4.16b, v3.16b, #8                          *)
    0x4ef98400;  (*      add     v0.2d, v0.2d, v25.2d                                *)
    0xcec08251;  (*      sha512su0       v17.2d, v18.2d                              *)
    0x6e1642a7;  (*      ext     v7.16b, v21.16b, v22.16b, #8                        *)
    0xce6680a0;  (*      sha512h q0, q5, v6.2d                                       *)
    0xce678a11;  (*      sha512su1       v17.2d, v16.2d, v7.2d                       *)
    0x4ee08482;  (*      add     v2.2d, v4.2d, v0.2d                                 *)
    0xce618480;  (*      sha512h2        q0, q4, v1.2d                               *)
    0x4ef28718;  (*      add     v24.2d, v24.2d, v18.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e034045;  (*      ext     v5.16b, v2.16b, v3.16b, #8                          *)
    0x6e024026;  (*      ext     v6.16b, v1.16b, v2.16b, #8                          *)
    0x4ef88463;  (*      add     v3.2d, v3.2d, v24.2d                                *)
    0xcec08272;  (*      sha512su0       v18.2d, v19.2d                              *)
    0x6e1742c7;  (*      ext     v7.16b, v22.16b, v23.16b, #8                        *)
    0xce6680a3;  (*      sha512h q3, q5, v6.2d                                       *)
    0xce678a32;  (*      sha512su1       v18.2d, v17.2d, v7.2d                       *)
    0x4ee38424;  (*      add     v4.2d, v1.2d, v3.2d                                 *)
    0xce608423;  (*      sha512h2        q3, q1, v0.2d                               *)
    0x4ef38739;  (*      add     v25.2d, v25.2d, v19.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e024085;  (*      ext     v5.16b, v4.16b, v2.16b, #8                          *)
    0x6e044006;  (*      ext     v6.16b, v0.16b, v4.16b, #8                          *)
    0x4ef98442;  (*      add     v2.2d, v2.2d, v25.2d                                *)
    0xcec08293;  (*      sha512su0       v19.2d, v20.2d                              *)
    0x6e1042e7;  (*      ext     v7.16b, v23.16b, v16.16b, #8                        *)
    0xce6680a2;  (*      sha512h q2, q5, v6.2d                                       *)
    0xce678a53;  (*      sha512su1       v19.2d, v18.2d, v7.2d                       *)
    0x4ee28401;  (*      add     v1.2d, v0.2d, v2.2d                                 *)
    0xce638402;  (*      sha512h2        q2, q0, v3.2d                               *)
    0x4ef48718;  (*      add     v24.2d, v24.2d, v20.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e044025;  (*      ext     v5.16b, v1.16b, v4.16b, #8                          *)
    0x6e014066;  (*      ext     v6.16b, v3.16b, v1.16b, #8                          *)
    0x4ef88484;  (*      add     v4.2d, v4.2d, v24.2d                                *)
    0xcec082b4;  (*      sha512su0       v20.2d, v21.2d                              *)
    0x6e114207;  (*      ext     v7.16b, v16.16b, v17.16b, #8                        *)
    0xce6680a4;  (*      sha512h q4, q5, v6.2d                                       *)
    0xce678a74;  (*      sha512su1       v20.2d, v19.2d, v7.2d                       *)
    0x4ee48460;  (*      add     v0.2d, v3.2d, v4.2d                                 *)
    0xce628464;  (*      sha512h2        q4, q3, v2.2d                               *)
    0x4ef58739;  (*      add     v25.2d, v25.2d, v21.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e014005;  (*      ext     v5.16b, v0.16b, v1.16b, #8                          *)
    0x6e004046;  (*      ext     v6.16b, v2.16b, v0.16b, #8                          *)
    0x4ef98421;  (*      add     v1.2d, v1.2d, v25.2d                                *)
    0xcec082d5;  (*      sha512su0       v21.2d, v22.2d                              *)
    0x6e124227;  (*      ext     v7.16b, v17.16b, v18.16b, #8                        *)
    0xce6680a1;  (*      sha512h q1, q5, v6.2d                                       *)
    0xce678a95;  (*      sha512su1       v21.2d, v20.2d, v7.2d                       *)
    0x4ee18443;  (*      add     v3.2d, v2.2d, v1.2d                                 *)
    0xce648441;  (*      sha512h2        q1, q2, v4.2d                               *)
    0x4ef68718;  (*      add     v24.2d, v24.2d, v22.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e004065;  (*      ext     v5.16b, v3.16b, v0.16b, #8                          *)
    0x6e034086;  (*      ext     v6.16b, v4.16b, v3.16b, #8                          *)
    0x4ef88400;  (*      add     v0.2d, v0.2d, v24.2d                                *)
    0xcec082f6;  (*      sha512su0       v22.2d, v23.2d                              *)
    0x6e134247;  (*      ext     v7.16b, v18.16b, v19.16b, #8                        *)
    0xce6680a0;  (*      sha512h q0, q5, v6.2d                                       *)
    0xce678ab6;  (*      sha512su1       v22.2d, v21.2d, v7.2d                       *)
    0x4ee08482;  (*      add     v2.2d, v4.2d, v0.2d                                 *)
    0xce618480;  (*      sha512h2        q0, q4, v1.2d                               *)
    0x4ef78739;  (*      add     v25.2d, v25.2d, v23.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e034045;  (*      ext     v5.16b, v2.16b, v3.16b, #8                          *)
    0x6e024026;  (*      ext     v6.16b, v1.16b, v2.16b, #8                          *)
    0x4ef98463;  (*      add     v3.2d, v3.2d, v25.2d                                *)
    0xcec08217;  (*      sha512su0       v23.2d, v16.2d                              *)
    0x6e144267;  (*      ext     v7.16b, v19.16b, v20.16b, #8                        *)
    0xce6680a3;  (*      sha512h q3, q5, v6.2d                                       *)
    0xce678ad7;  (*      sha512su1       v23.2d, v22.2d, v7.2d                       *)
    0x4ee38424;  (*      add     v4.2d, v1.2d, v3.2d                                 *)
    0xce608423;  (*      sha512h2        q3, q1, v0.2d                               *)
    0x4ef08718;  (*      add     v24.2d, v24.2d, v16.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e024085;  (*      ext     v5.16b, v4.16b, v2.16b, #8                          *)
    0x6e044006;  (*      ext     v6.16b, v0.16b, v4.16b, #8                          *)
    0x4ef88442;  (*      add     v2.2d, v2.2d, v24.2d                                *)
    0xcec08230;  (*      sha512su0       v16.2d, v17.2d                              *)
    0x6e154287;  (*      ext     v7.16b, v20.16b, v21.16b, #8                        *)
    0xce6680a2;  (*      sha512h q2, q5, v6.2d                                       *)
    0xce678af0;  (*      sha512su1       v16.2d, v23.2d, v7.2d                       *)
    0x4ee28401;  (*      add     v1.2d, v0.2d, v2.2d                                 *)
    0xce638402;  (*      sha512h2        q2, q0, v3.2d                               *)
    0x4ef18739;  (*      add     v25.2d, v25.2d, v17.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e044025;  (*      ext     v5.16b, v1.16b, v4.16b, #8                          *)
    0x6e014066;  (*      ext     v6.16b, v3.16b, v1.16b, #8                          *)
    0x4ef98484;  (*      add     v4.2d, v4.2d, v25.2d                                *)
    0xcec08251;  (*      sha512su0       v17.2d, v18.2d                              *)
    0x6e1642a7;  (*      ext     v7.16b, v21.16b, v22.16b, #8                        *)
    0xce6680a4;  (*      sha512h q4, q5, v6.2d                                       *)
    0xce678a11;  (*      sha512su1       v17.2d, v16.2d, v7.2d                       *)
    0x4ee48460;  (*      add     v0.2d, v3.2d, v4.2d                                 *)
    0xce628464;  (*      sha512h2        q4, q3, v2.2d                               *)
    0x4ef28718;  (*      add     v24.2d, v24.2d, v18.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e014005;  (*      ext     v5.16b, v0.16b, v1.16b, #8                          *)
    0x6e004046;  (*      ext     v6.16b, v2.16b, v0.16b, #8                          *)
    0x4ef88421;  (*      add     v1.2d, v1.2d, v24.2d                                *)
    0xcec08272;  (*      sha512su0       v18.2d, v19.2d                              *)
    0x6e1742c7;  (*      ext     v7.16b, v22.16b, v23.16b, #8                        *)
    0xce6680a1;  (*      sha512h q1, q5, v6.2d                                       *)
    0xce678a32;  (*      sha512su1       v18.2d, v17.2d, v7.2d                       *)
    0x4ee18443;  (*      add     v3.2d, v2.2d, v1.2d                                 *)
    0xce648441;  (*      sha512h2        q1, q2, v4.2d                               *)
    0x4ef38739;  (*      add     v25.2d, v25.2d, v19.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e004065;  (*      ext     v5.16b, v3.16b, v0.16b, #8                          *)
    0x6e034086;  (*      ext     v6.16b, v4.16b, v3.16b, #8                          *)
    0x4ef98400;  (*      add     v0.2d, v0.2d, v25.2d                                *)
    0xcec08293;  (*      sha512su0       v19.2d, v20.2d                              *)
    0x6e1042e7;  (*      ext     v7.16b, v23.16b, v16.16b, #8                        *)
    0xce6680a0;  (*      sha512h q0, q5, v6.2d                                       *)
    0xce678a53;  (*      sha512su1       v19.2d, v18.2d, v7.2d                       *)
    0x4ee08482;  (*      add     v2.2d, v4.2d, v0.2d                                 *)
    0xce618480;  (*      sha512h2        q0, q4, v1.2d                               *)
    0x4ef48718;  (*      add     v24.2d, v24.2d, v20.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e034045;  (*      ext     v5.16b, v2.16b, v3.16b, #8                          *)
    0x6e024026;  (*      ext     v6.16b, v1.16b, v2.16b, #8                          *)
    0x4ef88463;  (*      add     v3.2d, v3.2d, v24.2d                                *)
    0xcec082b4;  (*      sha512su0       v20.2d, v21.2d                              *)
    0x6e114207;  (*      ext     v7.16b, v16.16b, v17.16b, #8                        *)
    0xce6680a3;  (*      sha512h q3, q5, v6.2d                                       *)
    0xce678a74;  (*      sha512su1       v20.2d, v19.2d, v7.2d                       *)
    0x4ee38424;  (*      add     v4.2d, v1.2d, v3.2d                                 *)
    0xce608423;  (*      sha512h2        q3, q1, v0.2d                               *)
    0x4ef58739;  (*      add     v25.2d, v25.2d, v21.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e024085;  (*      ext     v5.16b, v4.16b, v2.16b, #8                          *)
    0x6e044006;  (*      ext     v6.16b, v0.16b, v4.16b, #8                          *)
    0x4ef98442;  (*      add     v2.2d, v2.2d, v25.2d                                *)
    0xcec082d5;  (*      sha512su0       v21.2d, v22.2d                              *)
    0x6e124227;  (*      ext     v7.16b, v17.16b, v18.16b, #8                        *)
    0xce6680a2;  (*      sha512h q2, q5, v6.2d                                       *)
    0xce678a95;  (*      sha512su1       v21.2d, v20.2d, v7.2d                       *)
    0x4ee28401;  (*      add     v1.2d, v0.2d, v2.2d                                 *)
    0xce638402;  (*      sha512h2        q2, q0, v3.2d                               *)
    0x4ef68718;  (*      add     v24.2d, v24.2d, v22.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e044025;  (*      ext     v5.16b, v1.16b, v4.16b, #8                          *)
    0x6e014066;  (*      ext     v6.16b, v3.16b, v1.16b, #8                          *)
    0x4ef88484;  (*      add     v4.2d, v4.2d, v24.2d                                *)
    0xcec082f6;  (*      sha512su0       v22.2d, v23.2d                              *)
    0x6e134247;  (*      ext     v7.16b, v18.16b, v19.16b, #8                        *)
    0xce6680a4;  (*      sha512h q4, q5, v6.2d                                       *)
    0xce678ab6;  (*      sha512su1       v22.2d, v21.2d, v7.2d                       *)
    0x4ee48460;  (*      add     v0.2d, v3.2d, v4.2d                                 *)
    0xce628464;  (*      sha512h2        q4, q3, v2.2d                               *)
    0x4ef78739;  (*      add     v25.2d, v25.2d, v23.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e014005;  (*      ext     v5.16b, v0.16b, v1.16b, #8                          *)
    0x6e004046;  (*      ext     v6.16b, v2.16b, v0.16b, #8                          *)
    0x4ef98421;  (*      add     v1.2d, v1.2d, v25.2d                                *)
    0xcec08217;  (*      sha512su0       v23.2d, v16.2d                              *)
    0x6e144267;  (*      ext     v7.16b, v19.16b, v20.16b, #8                        *)
    0xce6680a1;  (*      sha512h q1, q5, v6.2d                                       *)
    0xce678ad7;  (*      sha512su1       v23.2d, v22.2d, v7.2d                       *)
    0x4ee18443;  (*      add     v3.2d, v2.2d, v1.2d                                 *)
    0xce648441;  (*      sha512h2        q1, q2, v4.2d                               *)
    0x4ef08718;  (*      add     v24.2d, v24.2d, v16.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e004065;  (*      ext     v5.16b, v3.16b, v0.16b, #8                          *)
    0x6e034086;  (*      ext     v6.16b, v4.16b, v3.16b, #8                          *)
    0x4ef88400;  (*      add     v0.2d, v0.2d, v24.2d                                *)
    0xcec08230;  (*      sha512su0       v16.2d, v17.2d                              *)
    0x6e154287;  (*      ext     v7.16b, v20.16b, v21.16b, #8                        *)
    0xce6680a0;  (*      sha512h q0, q5, v6.2d                                       *)
    0xce678af0;  (*      sha512su1       v16.2d, v23.2d, v7.2d                       *)
    0x4ee08482;  (*      add     v2.2d, v4.2d, v0.2d                                 *)
    0xce618480;  (*      sha512h2        q0, q4, v1.2d                               *)
    0x4ef18739;  (*      add     v25.2d, v25.2d, v17.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e034045;  (*      ext     v5.16b, v2.16b, v3.16b, #8                          *)
    0x6e024026;  (*      ext     v6.16b, v1.16b, v2.16b, #8                          *)
    0x4ef98463;  (*      add     v3.2d, v3.2d, v25.2d                                *)
    0xcec08251;  (*      sha512su0       v17.2d, v18.2d                              *)
    0x6e1642a7;  (*      ext     v7.16b, v21.16b, v22.16b, #8                        *)
    0xce6680a3;  (*      sha512h q3, q5, v6.2d                                       *)
    0xce678a11;  (*      sha512su1       v17.2d, v16.2d, v7.2d                       *)
    0x4ee38424;  (*      add     v4.2d, v1.2d, v3.2d                                 *)
    0xce608423;  (*      sha512h2        q3, q1, v0.2d                               *)
    0x4ef28718;  (*      add     v24.2d, v24.2d, v18.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e024085;  (*      ext     v5.16b, v4.16b, v2.16b, #8                          *)
    0x6e044006;  (*      ext     v6.16b, v0.16b, v4.16b, #8                          *)
    0x4ef88442;  (*      add     v2.2d, v2.2d, v24.2d                                *)
    0xcec08272;  (*      sha512su0       v18.2d, v19.2d                              *)
    0x6e1742c7;  (*      ext     v7.16b, v22.16b, v23.16b, #8                        *)
    0xce6680a2;  (*      sha512h q2, q5, v6.2d                                       *)
    0xce678a32;  (*      sha512su1       v18.2d, v17.2d, v7.2d                       *)
    0x4ee28401;  (*      add     v1.2d, v0.2d, v2.2d                                 *)
    0xce638402;  (*      sha512h2        q2, q0, v3.2d                               *)
    0x4ef38739;  (*      add     v25.2d, v25.2d, v19.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e044025;  (*      ext     v5.16b, v1.16b, v4.16b, #8                          *)
    0x6e014066;  (*      ext     v6.16b, v3.16b, v1.16b, #8                          *)
    0x4ef98484;  (*      add     v4.2d, v4.2d, v25.2d                                *)
    0xcec08293;  (*      sha512su0       v19.2d, v20.2d                              *)
    0x6e1042e7;  (*      ext     v7.16b, v23.16b, v16.16b, #8                        *)
    0xce6680a4;  (*      sha512h q4, q5, v6.2d                                       *)
    0xce678a53;  (*      sha512su1       v19.2d, v18.2d, v7.2d                       *)
    0x4ee48460;  (*      add     v0.2d, v3.2d, v4.2d                                 *)
    0xce628464;  (*      sha512h2        q4, q3, v2.2d                               *)
    0x4ef48718;  (*      add     v24.2d, v24.2d, v20.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e014005;  (*      ext     v5.16b, v0.16b, v1.16b, #8                          *)
    0x6e004046;  (*      ext     v6.16b, v2.16b, v0.16b, #8                          *)
    0x4ef88421;  (*      add     v1.2d, v1.2d, v24.2d                                *)
    0xcec082b4;  (*      sha512su0       v20.2d, v21.2d                              *)
    0x6e114207;  (*      ext     v7.16b, v16.16b, v17.16b, #8                        *)
    0xce6680a1;  (*      sha512h q1, q5, v6.2d                                       *)
    0xce678a74;  (*      sha512su1       v20.2d, v19.2d, v7.2d                       *)
    0x4ee18443;  (*      add     v3.2d, v2.2d, v1.2d                                 *)
    0xce648441;  (*      sha512h2        q1, q2, v4.2d                               *)
    0x4ef58739;  (*      add     v25.2d, v25.2d, v21.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e004065;  (*      ext     v5.16b, v3.16b, v0.16b, #8                          *)
    0x6e034086;  (*      ext     v6.16b, v4.16b, v3.16b, #8                          *)
    0x4ef98400;  (*      add     v0.2d, v0.2d, v25.2d                                *)
    0xcec082d5;  (*      sha512su0       v21.2d, v22.2d                              *)
    0x6e124227;  (*      ext     v7.16b, v17.16b, v18.16b, #8                        *)
    0xce6680a0;  (*      sha512h q0, q5, v6.2d                                       *)
    0xce678a95;  (*      sha512su1       v21.2d, v20.2d, v7.2d                       *)
    0x4ee08482;  (*      add     v2.2d, v4.2d, v0.2d                                 *)
    0xce618480;  (*      sha512h2        q0, q4, v1.2d                               *)
    0x4ef68718;  (*      add     v24.2d, v24.2d, v22.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e034045;  (*      ext     v5.16b, v2.16b, v3.16b, #8                          *)
    0x6e024026;  (*      ext     v6.16b, v1.16b, v2.16b, #8                          *)
    0x4ef88463;  (*      add     v3.2d, v3.2d, v24.2d                                *)
    0xcec082f6;  (*      sha512su0       v22.2d, v23.2d                              *)
    0x6e134247;  (*      ext     v7.16b, v18.16b, v19.16b, #8                        *)
    0xce6680a3;  (*      sha512h q3, q5, v6.2d                                       *)
    0xce678ab6;  (*      sha512su1       v22.2d, v21.2d, v7.2d                       *)
    0x4ee38424;  (*      add     v4.2d, v1.2d, v3.2d                                 *)
    0xce608423;  (*      sha512h2        q3, q1, v0.2d                               *)
    0x4ef78739;  (*      add     v25.2d, v25.2d, v23.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e024085;  (*      ext     v5.16b, v4.16b, v2.16b, #8                          *)
    0x6e044006;  (*      ext     v6.16b, v0.16b, v4.16b, #8                          *)
    0x4ef98442;  (*      add     v2.2d, v2.2d, v25.2d                                *)
    0xcec08217;  (*      sha512su0       v23.2d, v16.2d                              *)
    0x6e144267;  (*      ext     v7.16b, v19.16b, v20.16b, #8                        *)
    0xce6680a2;  (*      sha512h q2, q5, v6.2d                                       *)
    0xce678ad7;  (*      sha512su1       v23.2d, v22.2d, v7.2d                       *)
    0x4ee28401;  (*      add     v1.2d, v0.2d, v2.2d                                 *)
    0xce638402;  (*      sha512h2        q2, q0, v3.2d                               *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x4ef08718;  (*      add     v24.2d, v24.2d, v16.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7030;  (*      ld1     { v16.16b }, [x1], #16                              *) *)
    0x3cc10430;  (*      ldr	q16, [x1], #16                                         *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e044025;  (*      ext     v5.16b, v1.16b, v4.16b, #8                          *)
    0x6e014066;  (*      ext     v6.16b, v3.16b, v1.16b, #8                          *)
    0x4ef88484;  (*      add     v4.2d, v4.2d, v24.2d                                *)
    0xce6680a4;  (*      sha512h q4, q5, v6.2d                                       *)
    0x4e200a10;  (*      rev64   v16.16b, v16.16b                                    *)
    0x4ee48460;  (*      add     v0.2d, v3.2d, v4.2d                                 *)
    0xce628464;  (*      sha512h2        q4, q3, v2.2d                               *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x4ef18739;  (*      add     v25.2d, v25.2d, v17.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7031;  (*      ld1     { v17.16b }, [x1], #16                              *) *)
    0x3cc10431;  (*      ldr	q17, [x1], #16                                         *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e014005;  (*      ext     v5.16b, v0.16b, v1.16b, #8                          *)
    0x6e004046;  (*      ext     v6.16b, v2.16b, v0.16b, #8                          *)
    0x4ef98421;  (*      add     v1.2d, v1.2d, v25.2d                                *)
    0xce6680a1;  (*      sha512h q1, q5, v6.2d                                       *)
    0x4e200a31;  (*      rev64   v17.16b, v17.16b                                    *)
    0x4ee18443;  (*      add     v3.2d, v2.2d, v1.2d                                 *)
    0xce648441;  (*      sha512h2        q1, q2, v4.2d                               *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x4ef28718;  (*      add     v24.2d, v24.2d, v18.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7032;  (*      ld1     { v18.16b }, [x1], #16                              *) *)
    0x3cc10432;  (*      ldr	   q18, [x1], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e004065;  (*      ext     v5.16b, v3.16b, v0.16b, #8                          *)
    0x6e034086;  (*      ext     v6.16b, v4.16b, v3.16b, #8                          *)
    0x4ef88400;  (*      add     v0.2d, v0.2d, v24.2d                                *)
    0xce6680a0;  (*      sha512h q0, q5, v6.2d                                       *)
    0x4e200a52;  (*      rev64   v18.16b, v18.16b                                    *)
    0x4ee08482;  (*      add     v2.2d, v4.2d, v0.2d                                 *)
    0xce618480;  (*      sha512h2        q0, q4, v1.2d                               *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x4ef38739;  (*      add     v25.2d, v25.2d, v19.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7033;  (*      ld1     { v19.16b }, [x1], #16                              *) *)
    0x3cc10433;  (*      ldr	   q19, [x1], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e034045;  (*      ext     v5.16b, v2.16b, v3.16b, #8                          *)
    0x6e024026;  (*      ext     v6.16b, v1.16b, v2.16b, #8                          *)
    0x4ef98463;  (*      add     v3.2d, v3.2d, v25.2d                                *)
    0xce6680a3;  (*      sha512h q3, q5, v6.2d                                       *)
    0x4e200a73;  (*      rev64   v19.16b, v19.16b                                    *)
    0x4ee38424;  (*      add     v4.2d, v1.2d, v3.2d                                 *)
    0xce608423;  (*      sha512h2        q3, q1, v0.2d                               *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x4ef48718;  (*      add     v24.2d, v24.2d, v20.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7034;  (*      ld1     { v20.16b }, [x1], #16                              *) *)
    0x3cc10434;  (*      ldr     q20, [x1], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e024085;  (*      ext     v5.16b, v4.16b, v2.16b, #8                          *)
    0x6e044006;  (*      ext     v6.16b, v0.16b, v4.16b, #8                          *)
    0x4ef88442;  (*      add     v2.2d, v2.2d, v24.2d                                *)
    0xce6680a2;  (*      sha512h q2, q5, v6.2d                                       *)
    0x4e200a94;  (*      rev64   v20.16b, v20.16b                                    *)
    0x4ee28401;  (*      add     v1.2d, v0.2d, v2.2d                                 *)
    0xce638402;  (*      sha512h2        q2, q0, v3.2d                               *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c78;  (*      ld1     { v24.2d }, [x3], #16                               *) *)
    0x3cc10478;  (*      ldr	   q24, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x4ef58739;  (*      add     v25.2d, v25.2d, v21.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7035;  (*      ld1     { v21.16b }, [x1], #16                              *) *)
    0x3cc10435;  (*      ldr	   q21, [x1], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e044025;  (*      ext     v5.16b, v1.16b, v4.16b, #8                          *)
    0x6e014066;  (*      ext     v6.16b, v3.16b, v1.16b, #8                          *)
    0x4ef98484;  (*      add     v4.2d, v4.2d, v25.2d                                *)
    0xce6680a4;  (*      sha512h q4, q5, v6.2d                                       *)
    0x4e200ab5;  (*      rev64   v21.16b, v21.16b                                    *)
    0x4ee48460;  (*      add     v0.2d, v3.2d, v4.2d                                 *)
    0xce628464;  (*      sha512h2        q4, q3, v2.2d                               *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7c79;  (*      ld1     { v25.2d }, [x3], #16                               *) *)
    0x3cc10479;  (* 	   ldr	   q25, [x3], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x4ef68718;  (*      add     v24.2d, v24.2d, v22.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7036;  (*      ld1     { v22.16b }, [x1], #16                              *) *)
    0x3cc10436;  (*	     ldr	   q22, [x1], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e184318;  (*      ext     v24.16b, v24.16b, v24.16b, #8                       *)
    0x6e014005;  (*      ext     v5.16b, v0.16b, v1.16b, #8                          *)
    0x6e004046;  (*      ext     v6.16b, v2.16b, v0.16b, #8                          *)
    0x4ef88421;  (*      add     v1.2d, v1.2d, v24.2d                                *)
    0xce6680a1;  (*      sha512h q1, q5, v6.2d                                       *)
    0x4e200ad6;  (*      rev64   v22.16b, v22.16b                                    *)
    0x4ee18443;  (*      add     v3.2d, v2.2d, v1.2d                                 *)
    0xce648441;  (*      sha512h2        q1, q2, v4.2d                               *)
    0xd10a0063;  (*      sub     x3, x3, #640                                        *)
    0x4ef78739;  (*      add     v25.2d, v25.2d, v23.2d                              *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4cdf7037;  (*      ld1     { v23.16b }, [x1], #16                              *) *)
    0x3cc10437;  (*      ldr	   q23, [x1], #16                                      *)
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0x6e194339;  (*      ext     v25.16b, v25.16b, v25.16b, #8                       *)
    0x6e004065;  (*      ext     v5.16b, v3.16b, v0.16b, #8                          *)
    0x6e034086;  (*      ext     v6.16b, v4.16b, v3.16b, #8                          *)
    0x4ef98400;  (*      add     v0.2d, v0.2d, v25.2d                                *)
    0xce6680a0;  (*      sha512h q0, q5, v6.2d                                       *)
    0x4e200af7;  (*      rev64   v23.16b, v23.16b                                    *)
    0x4ee08482;  (*      add     v2.2d, v4.2d, v0.2d                                 *)
    0xce618480;  (*      sha512h2        q0, q4, v1.2d                               *)
    0x4efa8400;  (*      add     v0.2d, v0.2d, v26.2d                                *)
    0x4efb8421;  (*      add     v1.2d, v1.2d, v27.2d                                *)
    0x4efc8442;  (*      add     v2.2d, v2.2d, v28.2d                                *)
    0x4efd8463;  (*      add     v3.2d, v3.2d, v29.2d                                *)    
    0xb5ffc382;  (*      cbnz    x2, 0xe80 <sha512_block_data_order_hw+0x40>         *)
    (* -------------------------------  Begin tweaks ------------------------------- *)
    (* 0x4c002c00;  (*      st1     { v0.2d, v1.2d, v2.2d, v3.2d }, [x0]                *) *)
    0x3d800000;  (*      str	q0, [x0]                                               *) 
    0x3d800401;  (*      str	q1, [x0, #16]                                          *)
    0x3d800802;  (*      str	q2, [x0, #32]                                          *)
    0x3d800c03;  (*      str	q3, [x0, #48]                                          *)      
    (* -------------------------------  End  tweaks  ------------------------------- *)
    0xf84107fd;  (*      ldr     x29, [sp], #16                                      *)
    0xd65f03c0;  (*      ret                                                         *)
  ];;

let sha512_hw_mc =
  let charlist = List.concat_map
    (fun op32 ->
      [Char.chr (Int.logand op32 255);
       Char.chr (Int.logand (Int.shift_right op32 8) 255);
       Char.chr (Int.logand (Int.shift_right op32 16) 255);
       Char.chr (Int.logand (Int.shift_right op32 24) 255)])
    sha512_hw_prog in
  let byte_list = Bytes.init (List.length charlist) (fun i -> List.nth charlist i) in
  define_word_list "sha512_hw_mc" (term_of_bytes byte_list);;

let SHA512_HW_EXEC = ARM_MK_EXEC_RULE sha512_hw_mc;;
let len_sha512_hw_exec = fst SHA512_HW_EXEC;;
let num_insts = dest_small_numeral (rhs (concl len_sha512_hw_exec)) / 4;;

(* --------------------------------------------------------------- *)


(* Concrete Test *)

(*
g`
num_blocks = 1 /\
pc = 0x0 /\
ktbl_base = 0x1b4300 /\
hash_base = 0x6000 /\
input_base = 0x400 /\
i0  = word 0x6162638000000000 /\
i1  = word 0x0000000000000000 /\
i2  = word 0x0000000000000000 /\
i3  = word 0x0000000000000000 /\
i4  = word 0x0000000000000000 /\
i5  = word 0x0000000000000000 /\
i6  = word 0x0000000000000000 /\
i7  = word 0x0000000000000000 /\
i8  = word 0x0000000000000000 /\
i9  = word 0x0000000000000000 /\
i10 = word 0x0000000000000000 /\
i11 = word 0x0000000000000000 /\
i12 = word 0x0000000000000000 /\
i13 = word 0x0000000000000000 /\
i14 = word 0x0000000000000000 /\
i15 = word 0x0000000000000018 /\
PAIRWISE nonoverlapping
  [(word pc:int64, LENGTH sha512_hw_mc); 
   (word hash_base:int64, 64);
   (word input_base:int64, 16 * 8 * num_blocks);
   (word ktbl_base:int64, 80 * 8)]
==>
ensures arm
  // Precondition
  (\s. aligned_bytes_loaded s (word pc) sha512_hw_mc /\       
       read PC s  = word pc  /\
       read X30 s = word retpc /\
       read X0 s  = word hash_base /\
       read X1 s  = word input_base /\
       read X3 s  = word ktbl_base /\
       read X2 s  = word num_blocks /\       
       // KTbl constants are in memory.
       // bignum_from_memory (word ktbl_base, 80) s = ktbl_bignum /\
       read (memory :> bytes128 (word ktbl_base))                           s = word_join  (word K_1 : 64 word)  (word K_0 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word 16)))      s = word_join  (word K_3 : 64 word)  (word K_2 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*2))))  s = word_join  (word K_5 : 64 word)  (word K_4 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*3))))  s = word_join  (word K_7 : 64 word)  (word K_6 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*4))))  s = word_join  (word K_9 : 64 word)  (word K_8 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*5))))  s = word_join (word K_11 : 64 word) (word K_10 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*6))))  s = word_join (word K_13 : 64 word) (word K_12 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*7))))  s = word_join (word K_15 : 64 word) (word K_14 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*8))))  s = word_join (word K_17 : 64 word) (word K_16 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*9))))  s = word_join (word K_19 : 64 word) (word K_18 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*10)))) s = word_join (word K_21 : 64 word) (word K_20 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*11)))) s = word_join (word K_23 : 64 word) (word K_22 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*12)))) s = word_join (word K_25 : 64 word) (word K_24 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*13)))) s = word_join (word K_27 : 64 word) (word K_26 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*14)))) s = word_join (word K_29 : 64 word) (word K_28 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*15)))) s = word_join (word K_31 : 64 word) (word K_30 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*16)))) s = word_join (word K_33 : 64 word) (word K_32 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*17)))) s = word_join (word K_35 : 64 word) (word K_34 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*18)))) s = word_join (word K_37 : 64 word) (word K_36 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*19)))) s = word_join (word K_39 : 64 word) (word K_38 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*20)))) s = word_join (word K_41 : 64 word) (word K_40 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*21)))) s = word_join (word K_43 : 64 word) (word K_42 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*22)))) s = word_join (word K_45 : 64 word) (word K_44 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*23)))) s = word_join (word K_47 : 64 word) (word K_46 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*24)))) s = word_join (word K_49 : 64 word) (word K_48 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*25)))) s = word_join (word K_51 : 64 word) (word K_50 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*26)))) s = word_join (word K_53 : 64 word) (word K_52 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*27)))) s = word_join (word K_55 : 64 word) (word K_54 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*28)))) s = word_join (word K_57 : 64 word) (word K_56 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*29)))) s = word_join (word K_59 : 64 word) (word K_58 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*30)))) s = word_join (word K_61 : 64 word) (word K_60 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*31)))) s = word_join (word K_63 : 64 word) (word K_62 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*32)))) s = word_join (word K_65 : 64 word) (word K_64 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*33)))) s = word_join (word K_67 : 64 word) (word K_66 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*34)))) s = word_join (word K_69 : 64 word) (word K_68 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*35)))) s = word_join (word K_71 : 64 word) (word K_70 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*36)))) s = word_join (word K_73 : 64 word) (word K_72 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*37)))) s = word_join (word K_75 : 64 word) (word K_74 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*38)))) s = word_join (word K_77 : 64 word) (word K_76 : 64 word) /\ 
       read (memory :> bytes128 (word_add (word ktbl_base) (word (16*39)))) s = word_join (word K_79 : 64 word) (word K_78 : 64 word) /\ 
       // One input block is in memory.       
       // bignum_from_memory (word input_base, 16) s = input_block /\
       // We use word_bytereverse below for each input word i0-i15 because they 
       // are in big-endian format, and this Arm machine is little-endian.
       //
       // The SHA512 specification expects the input as a big-endian value, and
       // REV64 instructions in the program change the endianness of 
       // the input words, so we will subsequently see 
       // (word_bytereverse (word_bytereverse i0)) = i0 in the rest of the program.
       read (memory :> bytes128 (word input_base))                       s = word_join (word_bytereverse (i1 : 64 word))   (word_bytereverse (i0 : 64 word)) /\
       read (memory :> bytes128 (word_add (word input_base) (word  16))) s = word_join (word_bytereverse (i3 : 64 word))   (word_bytereverse (i2 : 64 word)) /\
       read (memory :> bytes128 (word_add (word input_base) (word  32))) s = word_join (word_bytereverse (i5 : 64 word))   (word_bytereverse (i4 : 64 word)) /\
       read (memory :> bytes128 (word_add (word input_base) (word  48))) s = word_join (word_bytereverse (i7 : 64 word))   (word_bytereverse (i6 : 64 word)) /\
       read (memory :> bytes128 (word_add (word input_base) (word  64))) s = word_join (word_bytereverse (i9 : 64 word))   (word_bytereverse (i8 : 64 word)) /\
       read (memory :> bytes128 (word_add (word input_base) (word  80))) s = word_join (word_bytereverse (i11 : 64 word))  (word_bytereverse (i10 : 64 word)) /\
       read (memory :> bytes128 (word_add (word input_base) (word  96))) s = word_join (word_bytereverse (i13 : 64 word))  (word_bytereverse (i12 : 64 word)) /\
       read (memory :> bytes128 (word_add (word input_base) (word 112))) s = word_join (word_bytereverse (i15 : 64 word))  (word_bytereverse (i14 : 64 word)) /\
       // init_hash is stored at address hash_base.
       // bignum_from_memory (word hash_base, 8) s = init_hash
       read (memory :> bytes128 (word hash_base))                      s = word_join (word h_b : 64 word) (word h_a : 64 word) /\
       read (memory :> bytes128 (word_add (word hash_base) (word 16))) s = word_join (word h_d : 64 word) (word h_c : 64 word) /\
       read (memory :> bytes128 (word_add (word hash_base) (word 32))) s = word_join (word h_f : 64 word) (word h_e : 64 word) /\
       read (memory :> bytes128 (word_add (word hash_base) (word 48))) s = word_join (word h_h : 64 word) (word h_g : 64 word)
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

e(ARM_VSTEPS_TAC SHA512_HW_EXEC (1--1));;
e(ARM_VSTEPS_TAC SHA512_HW_EXEC (2--2));;


e(ARM_STEPS_TAC SHA512_HW_EXEC (2--514));;
*)