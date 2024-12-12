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

let  K_0  = new_definition  `K_0  = 0x428a2f98d728ae22:num`;;
let  K_1  = new_definition  `K_1  = 0x7137449123ef65cd:num`;;
let  K_2  = new_definition  `K_2  = 0xb5c0fbcfec4d3b2f:num`;;
let  K_3  = new_definition  `K_3  = 0xe9b5dba58189dbbc:num`;;
let  K_4  = new_definition  `K_4  = 0x3956c25bf348b538:num`;;
let  K_5  = new_definition  `K_5  = 0x59f111f1b605d019:num`;;
let  K_6  = new_definition  `K_6  = 0x923f82a4af194f9b:num`;;
let  K_7  = new_definition  `K_7  = 0xab1c5ed5da6d8118:num`;;
let  K_8  = new_definition  `K_8  = 0xd807aa98a3030242:num`;;
let  K_9  = new_definition  `K_9  = 0x12835b0145706fbe:num`;;
let K_10  = new_definition `K_10  = 0x243185be4ee4b28c:num`;;
let K_11  = new_definition `K_11  = 0x550c7dc3d5ffb4e2:num`;;
let K_12  = new_definition `K_12  = 0x72be5d74f27b896f:num`;;
let K_13  = new_definition `K_13  = 0x80deb1fe3b1696b1:num`;;
let K_14  = new_definition `K_14  = 0x9bdc06a725c71235:num`;;
let K_15  = new_definition `K_15  = 0xc19bf174cf692694:num`;;
let K_16  = new_definition `K_16  = 0xe49b69c19ef14ad2:num`;;
let K_17  = new_definition `K_17  = 0xefbe4786384f25e3:num`;;
let K_18  = new_definition `K_18  = 0x0fc19dc68b8cd5b5:num`;;
let K_19  = new_definition `K_19  = 0x240ca1cc77ac9c65:num`;;
let K_20  = new_definition `K_20  = 0x2de92c6f592b0275:num`;;
let K_21  = new_definition `K_21  = 0x4a7484aa6ea6e483:num`;;
let K_22  = new_definition `K_22  = 0x5cb0a9dcbd41fbd4:num`;;
let K_23  = new_definition `K_23  = 0x76f988da831153b5:num`;;
let K_24  = new_definition `K_24  = 0x983e5152ee66dfab:num`;;
let K_25  = new_definition `K_25  = 0xa831c66d2db43210:num`;;
let K_26  = new_definition `K_26  = 0xb00327c898fb213f:num`;;
let K_27  = new_definition `K_27  = 0xbf597fc7beef0ee4:num`;;
let K_28  = new_definition `K_28  = 0xc6e00bf33da88fc2:num`;;
let K_29  = new_definition `K_29  = 0xd5a79147930aa725:num`;;
let K_30  = new_definition `K_30  = 0x06ca6351e003826f:num`;;
let K_31  = new_definition `K_31  = 0x142929670a0e6e70:num`;;
let K_32  = new_definition `K_32  = 0x27b70a8546d22ffc:num`;;
let K_33  = new_definition `K_33  = 0x2e1b21385c26c926:num`;;
let K_34  = new_definition `K_34  = 0x4d2c6dfc5ac42aed:num`;;
let K_35  = new_definition `K_35  = 0x53380d139d95b3df:num`;;
let K_36  = new_definition `K_36  = 0x650a73548baf63de:num`;;
let K_37  = new_definition `K_37  = 0x766a0abb3c77b2a8:num`;;
let K_38  = new_definition `K_38  = 0x81c2c92e47edaee6:num`;;
let K_39  = new_definition `K_39  = 0x92722c851482353b:num`;;
let K_40  = new_definition `K_40  = 0xa2bfe8a14cf10364:num`;;
let K_41  = new_definition `K_41  = 0xa81a664bbc423001:num`;;
let K_42  = new_definition `K_42  = 0xc24b8b70d0f89791:num`;;
let K_43  = new_definition `K_43  = 0xc76c51a30654be30:num`;;
let K_44  = new_definition `K_44  = 0xd192e819d6ef5218:num`;;
let K_45  = new_definition `K_45  = 0xd69906245565a910:num`;;
let K_46  = new_definition `K_46  = 0xf40e35855771202a:num`;;
let K_47  = new_definition `K_47  = 0x106aa07032bbd1b8:num`;;
let K_48  = new_definition `K_48  = 0x19a4c116b8d2d0c8:num`;;
let K_49  = new_definition `K_49  = 0x1e376c085141ab53:num`;;
let K_50  = new_definition `K_50  = 0x2748774cdf8eeb99:num`;;
let K_51  = new_definition `K_51  = 0x34b0bcb5e19b48a8:num`;;
let K_52  = new_definition `K_52  = 0x391c0cb3c5c95a63:num`;;
let K_53  = new_definition `K_53  = 0x4ed8aa4ae3418acb:num`;;
let K_54  = new_definition `K_54  = 0x5b9cca4f7763e373:num`;;
let K_55  = new_definition `K_55  = 0x682e6ff3d6b2b8a3:num`;;
let K_56  = new_definition `K_56  = 0x748f82ee5defb2fc:num`;;
let K_57  = new_definition `K_57  = 0x78a5636f43172f60:num`;;
let K_58  = new_definition `K_58  = 0x84c87814a1f0ab72:num`;;
let K_59  = new_definition `K_59  = 0x8cc702081a6439ec:num`;;
let K_60  = new_definition `K_60  = 0x90befffa23631e28:num`;;
let K_61  = new_definition `K_61  = 0xa4506cebde82bde9:num`;;
let K_62  = new_definition `K_62  = 0xbef9a3f7b2c67915:num`;;
let K_63  = new_definition `K_63  = 0xc67178f2e372532b:num`;;
let K_64  = new_definition `K_64  = 0xca273eceea26619c:num`;;
let K_65  = new_definition `K_65  = 0xd186b8c721c0c207:num`;;
let K_66  = new_definition `K_66  = 0xeada7dd6cde0eb1e:num`;;
let K_67  = new_definition `K_67  = 0xf57d4f7fee6ed178:num`;;
let K_68  = new_definition `K_68  = 0x06f067aa72176fba:num`;;
let K_69  = new_definition `K_69  = 0x0a637dc5a2c898a6:num`;;
let K_70  = new_definition `K_70  = 0x113f9804bef90dae:num`;;
let K_71  = new_definition `K_71  = 0x1b710b35131c471b:num`;;
let K_72  = new_definition `K_72  = 0x28db77f523047d84:num`;;
let K_73  = new_definition `K_73  = 0x32caab7b40c72493:num`;;
let K_74  = new_definition `K_74  = 0x3c9ebe0a15c9bebc:num`;;
let K_75  = new_definition `K_75  = 0x431d67c49c100d4c:num`;;
let K_76  = new_definition `K_76  = 0x4cc5d4becb3e42b6:num`;;
let K_77  = new_definition `K_77  = 0x597f299cfc657e2a:num`;;
let K_78  = new_definition `K_78  = 0x5fcb6fab3ad6faec:num`;;
let K_79  = new_definition `K_79  = 0x6c44198c4a475817:num`;;

let ktbl_list = new_definition
`ktbl_list : num list =
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

let K_DEF = new_definition
 `K i:int64 =
  word(EL i ktbl_list)`;;

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

let h_a = new_definition 
 `h_a = 0x6a09e667f3bcc908:num`;;
let h_b = new_definition 
 `h_b = 0xbb67ae8584caa73b:num`;;
let h_c = new_definition 
 `h_c = 0x3c6ef372fe94f82b:num`;;
let h_d = new_definition 
 `h_d = 0xa54ff53a5f1d36f1:num`;; 
let h_e = new_definition 
 `h_e = 0x510e527fade682d1:num`;;
let h_f = new_definition 
 `h_f = 0x9b05688c2b3e6c1f:num`;;
let h_g = new_definition 
 `h_g = 0x1f83d9abfb41bd6b:num`;; 
let h_h = new_definition 
 `h_h = 0x5be0cd19137e2179:num`;;

let h_init = new_definition
  `h_init =
        word(h_a):int64,
        word(h_b):int64,
        word(h_c):int64,
        word(h_d):int64,
        word(h_e):int64,
        word(h_f):int64,
        word(h_g):int64,
        word(h_h):int64`;;

(* ------------------------------------------------------------------------- *)
(* Main inner loop iteration.                                                *)
(* ------------------------------------------------------------------------- *)

let sha512_sched = define
 `sha512_sched (m:num->int64) (i:num) : int64 =
      if i < 16 then m i
      else sigma1(sha512_sched m (i - 2)) +
           sha512_sched m (i - 7) +
           sigma0(sha512_sched m (i - 15)) +
           sha512_sched m (i - 16)`;;

let sha512_iter = new_definition
 `sha512_iter (w:num->int64) (a,b,c,d,e,f,g,h) (i:num) =
    let t1 = h + Sigma1(e) + Ch(e,f,g) + K i + w i in
    let t2 = Sigma0(a) + Maj(a,b,c) in
    (t1 + t2, a, b, c, d + t1, e, f, g)`;;

let sha_inner = define
 `sha_inner (w:num->int64) (a,b,c,d,e,f,g,h) (i:num) =
        if i = 0 then (a, b, c, d, e, f, g, h)
        else sha512_iter w (sha_inner w (a, b, c, d, e, f, g, h) (i - 1)) i`;;

let add8 = define
 `add8 (a:int64,b:int64,c:int64,d:int64,e:int64,f:int64,g:int64,h:int64)
        (a',b',c',d',e',f',g',h') =
       (a+a',b+b',c+c',d+d',e+e',f+f',g+g',h+h')`;;

let sha_block = define
 `sha_block (m:num->int64) hashes =
        add8 (sha_inner (sha512_sched m) hashes 80) hashes`;;

let sha512 = define
 `sha512 (m:num->num->int64) (i:num) =
    if i = 0 then h_init
    else sha_block (m (i - 1)) (sha512 m (i - 1))`;;
