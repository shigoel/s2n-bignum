(* ========================================================================= *)
(* Some definitions for SHA-512.                                             *)
(* ========================================================================= *)

needs "Library/words.ml";;
needs "arm/proofs/sha512.ml";;

(* ------------------------------------------------------------------------- *)
(* Section 4.2.3                                                             *)
(*                                                                           *)
(* In principle these have a more concise mathematical definition            *)
(* (first 64 fractional bit of cube roots of the first 80 primes)            *)
(* but it's easier just to use them as magic numbers. This is again          *)
(* coped from TweetNaCL                                                      *)
(* ------------------------------------------------------------------------- *)

let  K_0  = new_definition  `K_0 : (64)word = word 0x428a2f98d728ae22`;;
let  K_1  = new_definition  `K_1 : (64)word = word 0x7137449123ef65cd`;;
let  K_2  = new_definition  `K_2 : (64)word = word 0xb5c0fbcfec4d3b2f`;;
let  K_3  = new_definition  `K_3 : (64)word = word 0xe9b5dba58189dbbc`;;
let  K_4  = new_definition  `K_4 : (64)word = word 0x3956c25bf348b538`;;
let  K_5  = new_definition  `K_5 : (64)word = word 0x59f111f1b605d019`;;
let  K_6  = new_definition  `K_6 : (64)word = word 0x923f82a4af194f9b`;;
let  K_7  = new_definition  `K_7 : (64)word = word 0xab1c5ed5da6d8118`;;
let  K_8  = new_definition  `K_8 : (64)word = word 0xd807aa98a3030242`;;
let  K_9  = new_definition  `K_9 : (64)word = word 0x12835b0145706fbe`;;
let K_10  = new_definition `K_10 : (64)word = word 0x243185be4ee4b28c`;;
let K_11  = new_definition `K_11 : (64)word = word 0x550c7dc3d5ffb4e2`;;
let K_12  = new_definition `K_12 : (64)word = word 0x72be5d74f27b896f`;;
let K_13  = new_definition `K_13 : (64)word = word 0x80deb1fe3b1696b1`;;
let K_14  = new_definition `K_14 : (64)word = word 0x9bdc06a725c71235`;;
let K_15  = new_definition `K_15 : (64)word = word 0xc19bf174cf692694`;;
let K_16  = new_definition `K_16 : (64)word = word 0xe49b69c19ef14ad2`;;
let K_17  = new_definition `K_17 : (64)word = word 0xefbe4786384f25e3`;;
let K_18  = new_definition `K_18 : (64)word = word 0x0fc19dc68b8cd5b5`;;
let K_19  = new_definition `K_19 : (64)word = word 0x240ca1cc77ac9c65`;;
let K_20  = new_definition `K_20 : (64)word = word 0x2de92c6f592b0275`;;
let K_21  = new_definition `K_21 : (64)word = word 0x4a7484aa6ea6e483`;;
let K_22  = new_definition `K_22 : (64)word = word 0x5cb0a9dcbd41fbd4`;;
let K_23  = new_definition `K_23 : (64)word = word 0x76f988da831153b5`;;
let K_24  = new_definition `K_24 : (64)word = word 0x983e5152ee66dfab`;;
let K_25  = new_definition `K_25 : (64)word = word 0xa831c66d2db43210`;;
let K_26  = new_definition `K_26 : (64)word = word 0xb00327c898fb213f`;;
let K_27  = new_definition `K_27 : (64)word = word 0xbf597fc7beef0ee4`;;
let K_28  = new_definition `K_28 : (64)word = word 0xc6e00bf33da88fc2`;;
let K_29  = new_definition `K_29 : (64)word = word 0xd5a79147930aa725`;;
let K_30  = new_definition `K_30 : (64)word = word 0x06ca6351e003826f`;;
let K_31  = new_definition `K_31 : (64)word = word 0x142929670a0e6e70`;;
let K_32  = new_definition `K_32 : (64)word = word 0x27b70a8546d22ffc`;;
let K_33  = new_definition `K_33 : (64)word = word 0x2e1b21385c26c926`;;
let K_34  = new_definition `K_34 : (64)word = word 0x4d2c6dfc5ac42aed`;;
let K_35  = new_definition `K_35 : (64)word = word 0x53380d139d95b3df`;;
let K_36  = new_definition `K_36 : (64)word = word 0x650a73548baf63de`;;
let K_37  = new_definition `K_37 : (64)word = word 0x766a0abb3c77b2a8`;;
let K_38  = new_definition `K_38 : (64)word = word 0x81c2c92e47edaee6`;;
let K_39  = new_definition `K_39 : (64)word = word 0x92722c851482353b`;;
let K_40  = new_definition `K_40 : (64)word = word 0xa2bfe8a14cf10364`;;
let K_41  = new_definition `K_41 : (64)word = word 0xa81a664bbc423001`;;
let K_42  = new_definition `K_42 : (64)word = word 0xc24b8b70d0f89791`;;
let K_43  = new_definition `K_43 : (64)word = word 0xc76c51a30654be30`;;
let K_44  = new_definition `K_44 : (64)word = word 0xd192e819d6ef5218`;;
let K_45  = new_definition `K_45 : (64)word = word 0xd69906245565a910`;;
let K_46  = new_definition `K_46 : (64)word = word 0xf40e35855771202a`;;
let K_47  = new_definition `K_47 : (64)word = word 0x106aa07032bbd1b8`;;
let K_48  = new_definition `K_48 : (64)word = word 0x19a4c116b8d2d0c8`;;
let K_49  = new_definition `K_49 : (64)word = word 0x1e376c085141ab53`;;
let K_50  = new_definition `K_50 : (64)word = word 0x2748774cdf8eeb99`;;
let K_51  = new_definition `K_51 : (64)word = word 0x34b0bcb5e19b48a8`;;
let K_52  = new_definition `K_52 : (64)word = word 0x391c0cb3c5c95a63`;;
let K_53  = new_definition `K_53 : (64)word = word 0x4ed8aa4ae3418acb`;;
let K_54  = new_definition `K_54 : (64)word = word 0x5b9cca4f7763e373`;;
let K_55  = new_definition `K_55 : (64)word = word 0x682e6ff3d6b2b8a3`;;
let K_56  = new_definition `K_56 : (64)word = word 0x748f82ee5defb2fc`;;
let K_57  = new_definition `K_57 : (64)word = word 0x78a5636f43172f60`;;
let K_58  = new_definition `K_58 : (64)word = word 0x84c87814a1f0ab72`;;
let K_59  = new_definition `K_59 : (64)word = word 0x8cc702081a6439ec`;;
let K_60  = new_definition `K_60 : (64)word = word 0x90befffa23631e28`;;
let K_61  = new_definition `K_61 : (64)word = word 0xa4506cebde82bde9`;;
let K_62  = new_definition `K_62 : (64)word = word 0xbef9a3f7b2c67915`;;
let K_63  = new_definition `K_63 : (64)word = word 0xc67178f2e372532b`;;
let K_64  = new_definition `K_64 : (64)word = word 0xca273eceea26619c`;;
let K_65  = new_definition `K_65 : (64)word = word 0xd186b8c721c0c207`;;
let K_66  = new_definition `K_66 : (64)word = word 0xeada7dd6cde0eb1e`;;
let K_67  = new_definition `K_67 : (64)word = word 0xf57d4f7fee6ed178`;;
let K_68  = new_definition `K_68 : (64)word = word 0x06f067aa72176fba`;;
let K_69  = new_definition `K_69 : (64)word = word 0x0a637dc5a2c898a6`;;
let K_70  = new_definition `K_70 : (64)word = word 0x113f9804bef90dae`;;
let K_71  = new_definition `K_71 : (64)word = word 0x1b710b35131c471b`;;
let K_72  = new_definition `K_72 : (64)word = word 0x28db77f523047d84`;;
let K_73  = new_definition `K_73 : (64)word = word 0x32caab7b40c72493`;;
let K_74  = new_definition `K_74 : (64)word = word 0x3c9ebe0a15c9bebc`;;
let K_75  = new_definition `K_75 : (64)word = word 0x431d67c49c100d4c`;;
let K_76  = new_definition `K_76 : (64)word = word 0x4cc5d4becb3e42b6`;;
let K_77  = new_definition `K_77 : (64)word = word 0x597f299cfc657e2a`;;
let K_78  = new_definition `K_78 : (64)word = word 0x5fcb6fab3ad6faec`;;
let K_79  = new_definition `K_79 : (64)word = word 0x6c44198c4a475817`;;

let ktbl_list = new_definition `ktbl_list : ((64)word)list =
              [  K_0;  K_1;  K_2;  K_3;  K_4;  K_5;  K_6;  K_7;  K_8;  K_9;
                 K_10; K_11; K_12; K_13; K_14; K_15; K_16; K_17; K_18; K_19;
                 K_20; K_21; K_22; K_23; K_24; K_25; K_26; K_27; K_28; K_29;
                 K_30; K_31; K_32; K_33; K_34; K_35; K_36; K_37; K_38; K_39;
                 K_40; K_41; K_42; K_43; K_44; K_45; K_46; K_47; K_48; K_49;
                 K_50; K_51; K_52; K_53; K_54; K_55; K_56; K_57; K_58; K_59;
                 K_60; K_61; K_62; K_63; K_64; K_65; K_66; K_67; K_68; K_69;
                 K_70; K_71; K_72; K_73; K_74; K_75; K_76; K_77; K_78; K_79 ]`;;

(*
let ktbl_bignum = new_definition 
  `ktbl_bignum = bignum_of_list ktbl_list`;;
*)  

let K_DEF = new_definition `K i:int64 = EL i ktbl_list`;;

(*
let K_CLAUSES =
  end_itlist CONJ
   (map (fun i ->
    CONV_RULE(RAND_CONV(RAND_CONV
     (LAND_CONV(TOP_DEPTH_CONV num_CONV) THENC
      GEN_REWRITE_CONV TOP_DEPTH_CONV [EL;TL;HD])))
     (SPEC (mk_small_numeral i) K_DEF))
   (0--79));;
*)   

(* ------------------------------------------------------------------------- *)
(* Section 5.3.5: the initial value of the 8 hash variables.                 *)
(* ------------------------------------------------------------------------- *)

let h_a = new_definition `h_a : (64)word = word 0x6a09e667f3bcc908`;;
let h_b = new_definition `h_b : (64)word = word 0xbb67ae8584caa73b`;;
let h_c = new_definition `h_c : (64)word = word 0x3c6ef372fe94f82b`;;
let h_d = new_definition `h_d : (64)word = word 0xa54ff53a5f1d36f1`;; 
let h_e = new_definition `h_e : (64)word = word 0x510e527fade682d1`;;
let h_f = new_definition `h_f : (64)word = word 0x9b05688c2b3e6c1f`;;
let h_g = new_definition `h_g : (64)word = word 0x1f83d9abfb41bd6b`;; 
let h_h = new_definition `h_h : (64)word = word 0x5be0cd19137e2179`;;

let h_init = new_definition
  `h_init = h_a, h_b, h_c, h_d, h_e, h_f, h_g, h_h`;;

(* ------------------------------------------------------------------------- *)
(* Main inner loop iteration.                                                *)
(* ------------------------------------------------------------------------- *)

let message_schedule_word = define
  `message_schedule_word w1 w2 w3 w4 =
    sigma1 w1 + w2 + sigma0 w3 + w4`;;

let message_schedule = define
 `message_schedule (m:num->int64) (i:num) : int64 =
      if i < 16 then m i
      else message_schedule_word (message_schedule m (i - 2))
                                 (message_schedule m (i - 7))
                                 (message_schedule m (i - 15))
                                 (message_schedule m (i - 16))`;;

(*
let compression_t1 = define
  `compression_t1 e f g h kt wt = h + Sigma1(e) + Ch(e,f,g) + kt + wt`;;
*)

let compression_t1 = define
  `compression_t1 e f g h = h + Sigma1(e) + Ch(e,f,g)`;;

let compression_t2 = define
  `compression_t2 a b c = Sigma0(a) + Maj(a,b,c)`;;

let SHA512_A = define 
  `SHA512_A(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = a`;;
let SHA512_B = define 
  `SHA512_B(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = b`;;
let SHA512_C = define 
  `SHA512_C(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = c`;;
let SHA512_D = define 
  `SHA512_D(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = d`;;
let SHA512_E = define 
  `SHA512_E(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = e`;;
let SHA512_F = define 
  `SHA512_F(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = f`;;
let SHA512_G = define 
  `SHA512_G(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = g`;;
let SHA512_H = define 
  `SHA512_H(a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64) = h`;;                

(*
let compression_update = define
 `compression_update (a,b,c,d,e,f,g,h) ki wi =
    let t1 = (compression_t1 e f g h) + ki + wi in
    let t2 = compression_t2 a b c in
    (t1 + t2, a, b, c, d + t1, e, f, g)`;;
*)

let compression_update = define
 `compression_update hash ki wi =
    let a = SHA512_A hash in
    let b = SHA512_B hash in
    let c = SHA512_C hash in
    let d = SHA512_D hash in
    let e = SHA512_E hash in
    let f = SHA512_F hash in
    let g = SHA512_G hash in
    let h = SHA512_H hash in
    let t1 = (compression_t1 e f g h) + ki + wi in
    let t2 = compression_t2 a b c in
    (t1 + t2, a, b, c, d + t1, e, f, g)`;;

(*
let compression = define
  `compression (i:num) (a,b,c,d,e,f,g,h) (m:num->int64) =
      if i < 80 then
        let ki = K i in
        let wi = message_schedule m i in
        let update = compression_update (a,b,c,d,e,f,g,h) (K i) wi in
        compression (i + 1) update m
      else 
        (a,b,c,d,e,f,g,h)`;;
*)        
let compression = define
  `compression (i:num) hash (m:num->int64) =
      if i < 80 then
        let ki = K i in
        let wi = message_schedule m i in
        let update = compression_update hash (K i) wi in
        compression (i + 1) update m
      else 
        hash`;;

(*
let add8 = define
 `add8 (a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64)
        (a',b',c',d',e',f',g',h') =
       (a+a',b+b',c+c',d+d',e+e',f+f',g+g',h+h')`;;
*)

let add8 = define 
 `add8 hash hash' = 
  let a = SHA512_A hash in
  let b = SHA512_B hash in
  let c = SHA512_C hash in
  let d = SHA512_D hash in
  let e = SHA512_E hash in
  let f = SHA512_F hash in
  let g = SHA512_G hash in
  let h = SHA512_H hash in
  let a' = SHA512_A hash' in
  let b' = SHA512_B hash' in
  let c' = SHA512_C hash' in
  let d' = SHA512_D hash' in
  let e' = SHA512_E hash' in
  let f' = SHA512_F hash' in
  let g' = SHA512_G hash' in
  let h' = SHA512_H hash' in
  (a+a',b+b',c+c',d+d',e+e',f+f',g+g',h+h')`;;

let sha512_block = define
 `sha512_block (m:num->int64) hash =
    let hash' = compression 0 hash m in
    add8 hash' hash`;;

let sha512 = define 
  `sha512 (m:num->num->int64) (i:num) = 
    if i = 0 then h_init
    else sha512_block (m (i - 1)) (sha512 m (i - 1))`;;

(*
let sha512_iter = new_definition
 `sha512_iter (w:num->int64) (a,b,c,d,e,f,g,h) (i:num) =
    let t1 = compression_t1 e f g h (K i) (w i) in
    let t2 = compression_t2 a b c in
    (t1 + t2, a, b, c, d + t1, e, f, g)`;;

let sha_inner = define
 `sha_inner (w:num->int64) (a,b,c,d,e,f,g,h) (i:num) =
        if i = 0 then (a, b, c, d, e, f, g, h)
        else sha512_iter w (sha_inner w (a, b, c, d, e, f, g, h) (i - 1)) i`;;

let sha_block = define
 `sha_block (m:num->int64) hashes =
        add8 (sha_inner (message_schedule m) hashes 80) hashes`;;

let sha512_alt = define
 `sha512_alt (m:num->num->int64) (i:num) =
    if i = 0 then h_init
    else sha_block (m (i - 1)) (sha512_alt m (i - 1))`;;    
*)

(* --------------------------------------------------------------- *)
(*     Conversions for reducing SHA512 specification functions     *)
(* --------------------------------------------------------------- *)

let h_init_RED_CONV =
  REWRITE_CONV [h_init; h_a; h_b; h_c; h_d; h_e; h_f; h_g; h_h];;

(* let tmp = h_init_RED_CONV `h_init`;; *)

let K_DEF_RED_CONV =
  REWRITE_CONV 
     [K_DEF; ktbl_list; EL_CONS] THENC 
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let K_RED_CONV =
  REWRITE_CONV 
     [K_DEF; ktbl_list; 
      K_0;  K_1;  K_2;  K_3;  K_4;  K_5;  K_6;  K_7;  K_8;  K_9;
      K_10; K_11; K_12; K_13; K_14; K_15; K_16; K_17; K_18; K_19;
      K_20; K_21; K_22; K_23; K_24; K_25; K_26; K_27; K_28; K_29;
      K_30; K_31; K_32; K_33; K_34; K_35; K_36; K_37; K_38; K_39;
      K_40; K_41; K_42; K_43; K_44; K_45; K_46; K_47; K_48; K_49;
      K_50; K_51; K_52; K_53; K_54; K_55; K_56; K_57; K_58; K_59;
      K_60; K_61; K_62; K_63; K_64; K_65; K_66; K_67; K_68; K_69;
      K_70; K_71; K_72; K_73; K_74; K_75; K_76; K_77; K_78; K_79;
      EL_CONS] THENC 
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

(* let tmp = K_RED_CONV `K 0`;; *)
(* let tmp = K_RED_CONV `K 1`;; *)
(* let tmp = K_RED_CONV `K 8`;; *)
(* let tmp = K_RED_CONV `K 79`;; *)

let MESSAGE_SCHEDULE_WORD_RED_CONV =
  REWR_CONV message_schedule_word THENC
  DEPTH_CONV sigma1_RED_CONV THENC
  DEPTH_CONV sigma0_RED_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

(* let tmp = MESSAGE_SCHEDULE_WORD_RED_CONV `message_schedule_word (word 0xaa) (word 0xbb) (word 0xcc) (word 0xdd)`;; *)

(*
let tmp = sha512_sched_RED_CONV 
          `sha512_sched (\i. EL i [word 0x6162638000000000;
                                   word 0x0000000000000000;
                                   word 0x0000000000000000;
                                   word 0x0000000000000000;
                                   word 0x0000000000000000;
                                   word 0x0000000000000000;
                                   word 0x0000000000000000;
                                   word 0x0000000000000000;
                                   word 0x0000000000000000;
                                   word 0x0000000000000000;
                                   word 0x0000000000000000;
                                   word 0x0000000000000000;
                                   word 0x0000000000000000;
                                   word 0x0000000000000000;
                                   word 0x0000000000000000;
                                   word 0x0000000000000018])
                          15`;;  
*)

let COMPRESSION_T1_RED_CONV =
  REWR_CONV compression_t1 THENC
  DEPTH_CONV Sigma1_RED_CONV THENC
  DEPTH_CONV Ch_RED_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;  

(* let tmp = COMPRESSION_T1_RED_CONV `compression_t1 (word 0xaa) (word 0xbb) (word 0xcc) (word 0xdd)`;; *)

let COMPRESSION_T2_RED_CONV =
  REWR_CONV compression_t2 THENC
  DEPTH_CONV Sigma0_RED_CONV THENC
  DEPTH_CONV Maj_RED_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

(* let tmp = COMPRESSION_T2_RED_CONV `compression_t2 (word 0xaa) (word 0xbb) (word 0xcc)`;;   *)

let compression_update_RED_CONV =
  REWR_CONV compression_update THENC 
  REWRITE_CONV [SHA512_A; SHA512_B; SHA512_C; SHA512_D; SHA512_E; SHA512_F; SHA512_G; SHA512_H] THENC  
  REPEATC let_CONV THENC 
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC 
  TOP_DEPTH_CONV COMPRESSION_T1_RED_CONV THENC 
  TOP_DEPTH_CONV COMPRESSION_T2_RED_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

(*  
let tmp = compression_update_RED_CONV 
  `compression_update 
      (word 0, word 1, word 2, word 3, word 4, word 5, word 6, word 7) 
      (word 0xaa)
      (word 0xbb)`;;
*)      

(*  
let tmp = compression_update_RED_CONV 
    `compression_update (\i. EL i ([(word 0xaa); (word 0xbb); (word 0xcc); (word 0xdd)]:((64)word)list)) 
                 (word 0, word 1, word 2, word 3, word 4, word 5, word 6, word 7) 
                 2`;;
*)