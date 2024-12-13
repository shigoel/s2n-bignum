(** Carl Kwan: ARM SHA512 intrinsics in HOL Light **)

needs "Library/words.ml";;

(*****************************************************************************)

parse_as_prefix "~~";;
override_interface("~~",`word_not:N word->N word`);;
parse_as_infix("&&",(13,"right"));;
override_interface("&&",`word_and:N word->N word->N word`);;
parse_as_infix("||",(13,"right"));;
override_interface("||",`word_or:N word->N word->N word`);;
parse_as_infix("^^",(13,"right"));;
override_interface("^^",`word_xor:N word->N word->N word`);;

overload_interface("+",`word_add:N word->N word->N word`);;

let Ch_DEF = new_definition
 `Ch(x,y,z):int64 = (x && y) ^^ (~~x && z)`;;

let Maj_DEF = new_definition
 `Maj(x,y,z):int64 = (x && y) ^^ (x && z) ^^ (y && z)`;;

let Sigma0_DEF = new_definition
 `Sigma0(x):int64 = word_ror x 28 ^^ word_ror x 34 ^^ word_ror x 39`;;

let Sigma1_DEF = new_definition
 `Sigma1(x):int64 = word_ror x 14 ^^ word_ror x 18 ^^ word_ror x 41`;;

let sigma0_DEF = new_definition
 `sigma0(x):int64 = word_ror x 1 ^^ word_ror x 8 ^^ word_ushr x 7`;;

let sigma1_DEF = new_definition
 `sigma1(x):int64 = word_ror x 19 ^^ word_ror x 61 ^^ word_ushr x 6`;;

unparse_as_prefix "~~";;
remove_interface("~~");;
unparse_as_infix("&&");;
remove_interface("&&");;
unparse_as_infix("||");;
remove_interface("||");;
unparse_as_infix("^^");;
remove_interface("^^");;
remove_interface("++");;

(*****************************************************************************)

(*************************)
(**                     **)
(**  SHA512 INTRINSICS  **)
(**                     **)
(*************************)

(**
 **  ARM pseudocode of sha512h
 **
 **    AArch64.CheckFPAdvSIMDEnabled();
 **
 **    bits(128) Vtmp;
 **    bits(64) MSigma1;
 **    bits(64) tmp;
 **    bits(128) X = V[n];
 **    bits(128) Y = V[m];
 **    bits(128) W = V[d];
 **
 **    MSigma1 = ROR(Y<127:64>, 14) EOR ROR(Y<127:64>, 18) EOR ROR(Y<127:64>, 41);
 **    Vtmp<127:64> = (Y<127:64> AND X<63:0>) EOR (NOT(Y<127:64>) AND X<127:64>);
 **    Vtmp<127:64> = (Vtmp<127:64> + MSigma1 + W<127:64>);
 **    tmp = Vtmp<127:64> + Y<63:0>;
 **    MSigma1 = ROR(tmp, 14) EOR ROR(tmp, 18) EOR ROR(tmp, 41);
 **    Vtmp<63:0> = (tmp AND Y<127:64>) EOR (NOT(tmp) AND X<63:0>);
 **    Vtmp<63:0> = (Vtmp<63:0> + MSigma1 + W<63:0>);
 **    V[d] = Vtmp;
 **
 **  See
 **    https://developer.arm.com/documentation/ddi0596/2020-12/SIMD-FP-Instructions/SHA512H--SHA512-Hash-update-part-1-
 **)

let sha512h = define
  `sha512h (d:int128) (n:int128) (m:int128) : int128 =
          let x = n in
          let y = m in
          let w = d in
          // let msig1 : 64 word = word_xor (word_ror (word_subword y (64, 64)) 14)
          //                                (word_xor (word_ror (word_subword y (64, 64)) 18)
          //                                          (word_ror (word_subword y (64, 64)) 41)) in
          let msig1 : 64 word = Sigma1 (word_subword y (64, 64)) in

          // let vtmp1 : 64 word = word_xor (word_and (word_subword y (64, 64))
          //                                          (word_subword x ( 0, 64)))
          //                                (word_and (word_not (word_subword y (64, 64)))
          //                                          (word_subword x (64, 64))) in
          let vtmp1 : 64 word = Ch((word_subword y (64, 64)),
                                   (word_subword x ( 0, 64)),
                                   (word_subword x (64, 64))) in
          let vtmp1 : 64 word = word_add vtmp1
                                         (word_add msig1
                                                   (word_subword w (64, 64))) in

          let tmp   : 64 word = word_add vtmp1 (word_subword y ( 0, 64)) in

          // let msig1 : 64 word = word_xor (word_ror tmp 14)
          //                                (word_xor (word_ror tmp 18)
          //                                          (word_ror tmp 41)) in
          let msig1 : 64 word = Sigma1 tmp in

          // let vtmp0 : 64 word = word_xor (word_and tmp (word_subword y (64, 64)))
          //                                (word_and (word_not tmp) (word_subword x ( 0, 64))) in
          let vtmp0 : 64 word = Ch(tmp, (word_subword y (64, 64)), (word_subword x (0, 64))) in
          let vtmp0 : 64 word = word_add vtmp0
                                         (word_add msig1
                                                   (word_subword w ( 0, 64))) in

          (word_join:64 word->64 word->128 word) vtmp1 vtmp0`;;

(**
 **  ARM pseudocode of sha512h2
 **
 **    AArch64.CheckFPAdvSIMDEnabled();
 **
 **    bits(128) Vtmp;
 **    bits(64) NSigma0;
 **    bits(128) X = V[n];
 **    bits(128) Y = V[m];
 **    bits(128) W = V[d];
 **
 **    NSigma0 = ROR(Y<63:0>, 28) EOR ROR(Y<63:0>, 34) EOR ROR(Y<63:0>, 39);
 **    Vtmp<127:64> = (X<63:0> AND Y<127:64>) EOR (X<63:0> AND Y<63:0>) EOR (Y<127:64> AND Y<63:0>);
 **    Vtmp<127:64> = (Vtmp<127:64> + NSigma0 + W<127:64>);
 **    NSigma0 = ROR(Vtmp<127:64>, 28) EOR ROR(Vtmp<127:64>, 34) EOR ROR(Vtmp<127:64>, 39);
 **    Vtmp<63:0> = (Vtmp<127:64> AND Y<63:0>) EOR (Vtmp<127:64> AND Y<127:64>) EOR (Y<127:64> AND Y<63:0>);
 **    Vtmp<63:0> = (Vtmp<63:0> + NSigma0 + W<63:0>);
 **
 **    V[d] = Vtmp;
 **
 **  See
 **    https://developer.arm.com/documentation/ddi0596/2020-12/SIMD-FP-Instructions/SHA512H2--SHA512-Hash-update-part-2-
 **)

let sha512h2 = define
  `sha512h2 (d:int128) (n:int128) (m:int128) : int128 =
          let x = n in
          let y = m in
          let w = d in
          // let nsig0 : 64 word = word_xor (word_ror (word_subword y ( 0, 64)) 28)
          //                                (word_xor (word_ror (word_subword y ( 0, 64)) 34)
          //                                          (word_ror (word_subword y ( 0, 64)) 39)) in
          let nsig0 : 64 word = Sigma0 (word_subword y (0, 64)) in
          
          // let vtmp1 : 64 word = word_xor (word_and (word_subword x ( 0, 64))
          //                                          (word_subword y (64, 64)))
          //                                (word_xor (word_and (word_subword x ( 0, 64))
          //                                                    (word_subword y ( 0, 64)))
          //                                          (word_and (word_subword y (64, 64))
          //                                                    (word_subword y ( 0, 64)))) in
          let vtmp1 : 64 word = Maj((word_subword x ( 0, 64)),
                                    (word_subword y (64, 64)),
                                    (word_subword y ( 0, 64))) in
          let vtmp1 : 64 word = word_add vtmp1
                                         (word_add nsig0
                                                   (word_subword w (64, 64))) in


          // let nsig0 : 64 word = word_xor (word_ror vtmp1 28)
          //                                (word_xor (word_ror vtmp1 34)
          //                                          (word_ror vtmp1 39)) in
          let nsig0 : 64 word = Sigma0 vtmp1 in

          // let vtmp0 : 64 word = word_xor (word_and vtmp1 (word_subword y ( 0, 64)))
          //                                (word_xor (word_and vtmp1
          //                                                    (word_subword y (64, 64)))
          //                                          (word_and (word_subword y (64, 64))
          //                                                    (word_subword y ( 0, 64)))) in
          let vtmp0 : 64 word = Maj(vtmp1, (word_subword y ( 0, 64)), (word_subword y (64, 64))) in
          let vtmp0 : 64 word = word_add vtmp0
                                         (word_add nsig0
                                                   (word_subword w ( 0, 64))) in

          (word_join:64 word->64 word->128 word) vtmp1 vtmp0`;;

(**
 **  ARM pseudocode of sha512su0
 **
 **    AArch64.CheckFPAdvSIMDEnabled();
 **
 **    bits(64) sig0;
 **    bits(128) Vtmp;
 **    bits(128) X = V[n];
 **    bits(128) W = V[d];
 **    sig0 = ROR(W<127:64>, 1) EOR ROR(W<127:64>, 8) EOR ('0000000':W<127:71>);
 **    Vtmp<63:0> = W<63:0> + sig0;
 **    sig0 = ROR(X<63:0>, 1) EOR ROR(X<63:0>, 8) EOR ('0000000':X<63:7>);
 **    Vtmp<127:64> = W<127:64> + sig0;
 **    V[d] = Vtmp;
 **
 **  See
 **    https://developer.arm.com/documentation/ddi0596/2020-12/SIMD-FP-Instructions/SHA512SU0--SHA512-Schedule-Update-0-
 **)

let sha512su0 = define
  `sha512su0 (d:int128) (n:int128) : int128 =
          let w = d in
          let x = n in
          // let sig0 : 64 word = word_xor (word_ror (word_subword w (64, 64)) 1)
          //                               (word_xor (word_ror (word_subword w (64, 64)) 8)
          //                                         ((word_join:7 word->57 word->64 word)
          //                                          (word 0 : 7 word)
          //                                          (word_subword w (71, 57)))) in
          let sig0 : 64 word = sigma0 (word_subword w (64, 64)) in
          let tmp0 : 64 word = word_add (word_subword w (0, 64)) sig0 in

          // let sig0 : 64 word = word_xor (word_ror (word_subword x (0, 64)) 1)
          //                               (word_xor (word_ror (word_subword x ( 0, 64)) 8)
          //                                         ((word_join:7 word->57 word->64 word)
          //                                          (word 0 : 7 word)
          //                                          (word_subword x (7, 57)))) in
          let sig0 : 64 word = sigma0 (word_subword x (0, 64)) in

          let tmp1 : 64 word = word_add (word_subword w (64, 64)) sig0 in

          (word_join:64 word->64 word->128 word) tmp1 tmp0`;;

(**
 **  ARM pseudocode of sha512su1
 **
 **    AArch64.CheckFPAdvSIMDEnabled();
 **
 **    bits(64) sig1;
 **    bits(128) Vtmp;
 **    bits(128) X = V[n];
 **    bits(128) Y = V[m];
 **    bits(128) W = V[d];
 **
 **    sig1 = ROR(X<127:64>, 19) EOR ROR(X<127:64>, 61) EOR ('000000':X<127:70>);
 **    Vtmp<127:64> = W<127:64> + sig1 + Y<127:64>;
 **    sig1 = ROR(X<63:0>, 19) EOR ROR(X<63:0>, 61) EOR ('000000':X<63:6>);
 **    Vtmp<63:0> = W<63:0> + sig1 + Y<63:0>;
 **    V[d] = Vtmp;
 **
 **  See
 **    https://developer.arm.com/documentation/ddi0596/2020-12/SIMD-FP-Instructions/SHA512SU1--SHA512-Schedule-Update-1-
 **)

let sha512su1 = define
  `sha512su1 (d:int128) (n:int128) (m:int128) : int128 =
          let x = n in
          let y = m in
          let w = d in
          // let sig1 : 64 word = word_xor (word_ror (word_subword x (64, 64)) 19)
          //                               (word_xor (word_ror (word_subword x (64, 64)) 61)
          //                                         ((word_join:6 word->58 word->64 word)
          //                                          (word 0 : 6 word)
          //                                          (word_subword x (70, 58)))) in
          let sig1 : 64 word = sigma1 (word_subword x (64, 64)) in

          let tmp1 : 64 word = word_add (word_subword w (64, 64))
                                        (word_add sig1
                                                  (word_subword y (64, 64))) in

          // let sig1 : 64 word = word_xor (word_ror (word_subword x (0, 64)) 19)
          //                               (word_xor (word_ror (word_subword x ( 0, 64)) 61)
          //                                         ((word_join:6 word->58 word->64 word)
          //                                          (word 0 : 6 word)
          //                                          (word_subword x (6, 58)))) in
          let sig1 : 64 word = sigma1 (word_subword x (0, 64)) in

          let tmp0 : 64 word = word_add (word_subword w ( 0, 64))
                                        (word_add sig1
                                                  (word_subword y ( 0, 64))) in

          (word_join:64 word->64 word->128 word) tmp1 tmp0`;;


(************************************************)
(**                                            **)
(** CONVERSIONS FOR REDUCING SHA512 INTRINSICS **)
(**                                            **)
(************************************************)

let Ch_RED_CONV =
  REWR_CONV Ch_DEF THENC
  DEPTH_CONV (let_CONV) THENC
  WORD_REDUCE_CONV;;

let Maj_RED_CONV =
  REWR_CONV Maj_DEF THENC
  DEPTH_CONV (let_CONV) THENC
  WORD_REDUCE_CONV;;
  
let Sigma0_RED_CONV =
  REWR_CONV Sigma0_DEF THENC
  DEPTH_CONV (let_CONV) THENC
  WORD_REDUCE_CONV;; 

let Sigma1_RED_CONV =
  REWR_CONV Sigma1_DEF THENC
  DEPTH_CONV (let_CONV) THENC
  WORD_REDUCE_CONV;; 
  
let sigma0_RED_CONV =
  REWR_CONV sigma0_DEF THENC
  DEPTH_CONV (let_CONV) THENC
  WORD_REDUCE_CONV;; 

let sigma1_RED_CONV =
  REWR_CONV sigma1_DEF THENC
  DEPTH_CONV (let_CONV) THENC
  WORD_REDUCE_CONV;;

let SHA512H_RED_CONV =
        REWR_CONV sha512h THENC
        DEPTH_CONV (let_CONV) THENC
        WORD_REDUCE_CONV;;

let SHA512H_REDUCE_CONV tm =
      match tm with
        Comb(Comb(Comb(Const("sha512h",_),
                  Comb(Const("word",_),d)),
                  Comb(Const("word",_),n)),
                  Comb(Const("word",_),m))
      when is_numeral d && is_numeral n && is_numeral m -> SHA512H_RED_CONV tm
    | _ -> failwith "SHA512H_CONV: inapplicable";;

let SHA512H2_RED_CONV =
        REWR_CONV sha512h2 THENC
        DEPTH_CONV (let_CONV) THENC
        WORD_REDUCE_CONV;;

let SHA512H2_REDUCE_CONV tm =
      match tm with
        Comb(Comb(Comb(Const("sha512h2",_),
                  Comb(Const("word",_),d)),
                  Comb(Const("word",_),n)),
                  Comb(Const("word",_),m))
      when is_numeral d && is_numeral n && is_numeral m -> SHA512H2_RED_CONV tm
    | _ -> failwith "SHA512H2_CONV: inapplicable";;

let SHA512SU0_RED_CONV =
        REWR_CONV sha512su0 THENC
        DEPTH_CONV (let_CONV) THENC
        WORD_REDUCE_CONV;;

let SHA512SU0_REDUCE_CONV tm =
  match tm with
    Comb(Comb(Const("sha512su0",_),Comb(Const("word",_),d)),
         Comb(Const("word",_),n))
    when is_numeral d && is_numeral n -> SHA512SU0_RED_CONV tm
  | _ -> failwith "SHA512SU0_CONV: inapplicable";;

let SHA512SU1_RED_CONV =
        REWR_CONV sha512su1 THENC
        DEPTH_CONV (let_CONV) THENC
        WORD_REDUCE_CONV;;

let SHA512SU1_REDUCE_CONV tm =
      match tm with
        Comb(Comb(Comb(Const("sha512su1",_),
                  Comb(Const("word",_),d)),
                  Comb(Const("word",_),n)),
                  Comb(Const("word",_),m))
      when is_numeral d && is_numeral n && is_numeral m -> SHA512SU1_RED_CONV tm
    | _ -> failwith "SHA512SU1_CONV: inapplicable";;

