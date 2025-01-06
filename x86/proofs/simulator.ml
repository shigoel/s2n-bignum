(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ------------------------------------------------------------------------- *)
(* Encoding the registers and flags as a 16-element list of numbers.         *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/base.ml";;

let regfile = new_definition
 `regfile s =
   [val(read RAX s); val(read RCX s); val(read RDX s); val(read RBX s);
    bitval(read CF s) +  4 * bitval(read PF s) + 16 * bitval(read AF s) +
    64 * bitval(read ZF s) + 128 * bitval(read SF s) +
    2048 * bitval(read OF s);
    val(read RBP s); val(read RSI s); val(read RDI s); val(read R8 s);
    val(read R9 s); val(read R10 s); val(read R11 s); val(read R12 s);
    val(read R13 s); val(read R14 s); val(read R15 s)]`;;

let FLAGENCODING_11 = prove
 (`bitval b0 + 4 * bitval b1 + 16 * bitval b2 +
   64 * bitval b3 + 128 * bitval b4 + 2048 * bitval b5 = n <=>
   n < 4096 /\
   (b0 <=> ODD n) /\
   ~ODD(n DIV 2) /\
   (b1 <=> ODD(n DIV 4)) /\
   ~ODD(n DIV 8) /\
   (b2 <=> ODD(n DIV 16)) /\
   ~ODD(n DIV 32) /\
   (b3 <=> ODD(n DIV 64)) /\
   (b4 <=> ODD(n DIV 128)) /\
   ~ODD(n DIV 256) /\
   ~ODD(n DIV 512) /\
   ~ODD(n DIV 1024) /\
   (b5 <=> ODD(n DIV 2048))`,
  REWRITE_TAC[bitval] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  (EQ_TAC THENL [DISCH_THEN(SUBST1_TAC o SYM) THEN ARITH_TAC; ALL_TAC]) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP MOD_LT) THEN
  REWRITE_TAC[ARITH_RULE
   `4096 = 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2`] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN REWRITE_TAC[DIV_DIV] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[MOD_2_CASES; GSYM NOT_ODD] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Random numbers with random bit density, random state for simulating.      *)
(* ------------------------------------------------------------------------- *)

let random_boold d = Random.int 64 < d;;

let randomnd n density =
    funpow n (fun n ->
      (if random_boold density then num_1 else num_0) +/ num_2 */ n) num_0;;

let random64() = randomnd 64 (Random.int 65);;

let random_regstate () =
  let d = Random.int 65 in
  map (fun _ -> randomnd 64 d) (0--3) @
  [num(Random.int 256 land 0b11010101)] @
  [num(4294967295)] @
  map (fun _ -> randomnd 64 d) (6--15);;

(* ------------------------------------------------------------------------- *)
(* Generate random instance of instruction class itself.                     *)
(* ------------------------------------------------------------------------- *)

let random_instruction iclasses =
  el (Random.int (length iclasses)) iclasses;;

(* ------------------------------------------------------------------------- *)
(* The iclasses to simulate.                                                 *)
(* x86-insns.ml is generated by 'make x86-insns.ml'.                         *)
(* ------------------------------------------------------------------------- *)

loadt "x86/x86-insns.ml";;

let iclasses = iclasses @

(*** The elements here were added manually for additional checks. ***)

[[0x48; 0x0f; 0xb7; 0xc2];  (* MOVZX (% rax) (% dx) *)
 [0x0f; 0xb7; 0xc2];        (* MOVZX (% eax) (% dx) *)
 [0x48; 0x0f; 0xb6; 0xc2];  (* MOVZX (% rax) (% dl) *)
 [0x0f; 0xb6; 0xc2];        (* MOVZX (% eax) (% dl) *)
 [0x0f; 0xb6; 0xc6];        (* MOVZX (% eax) (% dh) *)
 [0x48; 0x0f; 0xbf; 0xc2];  (* MOVSX (% rax) (% dx) *)
 [0x0f; 0xbf; 0xc2];        (* MOVSX (% eax) (% dx) *)
 [0x48; 0x0f; 0xbe; 0xc2];  (* MOVSX (% rax) (% dl) *)
 [0x0f; 0xbe; 0xc2];        (* MOVSX (% eax) (% dl) *)
 [0x0f; 0xbe; 0xc6];        (* MOVSX (% eax) (% dh) *)
 [0x48; 0x63; 0xc2];        (* MOVSX (% rax) (% edx) *)
 [0x63; 0xc2];              (* MOVSX (% eax) (% edx) *)
 [0x48; 0x0f; 0xb7; 0xc9];  (* MOVZX (% rcx) (% cx) *)
 [0x0f; 0xb7; 0xc9];        (* MOVZX (% ecx) (% cx) *)
 [0x48; 0x0f; 0xb6; 0xc9];  (* MOVZX (% rcx) (% cl) *)
 [0x0f; 0xb6; 0xc9];        (* MOVZX (% ecx) (% cl) *)
 [0x0f; 0xb6; 0xcd];        (* MOVZX (% ecx) (% ch) *)
 [0x48; 0x0f; 0xbf; 0xc9];  (* MOVSX (% rcx) (% cx) *)
 [0x0f; 0xbf; 0xc9];        (* MOVSX (% ecx) (% cx) *)
 [0x48; 0x0f; 0xbe; 0xc9];  (* MOVSX (% rcx) (% cl) *)
 [0x0f; 0xbe; 0xc9];        (* MOVSX (% ecx) (% cl) *)
 [0x0f; 0xbe; 0xcd];        (* MOVSX (% ecx) (% ch) *)
 [0x48; 0x63; 0xc9];        (* MOVSX (% rcx) (% ecx) *)
 [0x63; 0xc9];              (* MOVSX (% ecx) (% ecx) *)
 [0x48; 0x0f; 0xb7; 0xf7];  (* MOVZX (% rsi) (% di) *)
 [0x0f; 0xb7; 0xf7];        (* MOVZX (% esi) (% di) *)
 [0x48; 0x0f; 0xb6; 0xf7];  (* MOVZX (% rsi) (% dil) *)
 [0x40; 0x0f; 0xb6; 0xf7];  (* MOVZX (% esi) (% dil) *)
 [0x0f; 0xb6; 0xf6];        (* MOVZX (% esi) (% dh) *)
 [0x48; 0x0f; 0xbf; 0xf7];  (* MOVSX (% rsi) (% di) *)
 [0x0f; 0xbf; 0xf7];        (* MOVSX (% esi) (% di) *)
 [0x48; 0x0f; 0xbe; 0xf7];  (* MOVSX (% rsi) (% dil) *)
 [0x40; 0x0f; 0xbe; 0xf7];  (* MOVSX (% esi) (% dil) *)
 [0x0f; 0xbe; 0xf7];        (* MOVSX (% esi) (% bh) *)
 [0x48; 0x63; 0xf7];        (* MOVSX (% rsi) (% edi) *)
 [0x63; 0xf7];              (* MOVSX (% esi) (% edi) *)
 [0x4c; 0x0f; 0xb7; 0xfa];  (* MOVZX (% r15) (% dx) *)
 [0x44; 0x0f; 0xb7; 0xfa];  (* MOVZX (% r15d) (% dx) *)
 [0x4c; 0x0f; 0xb6; 0xfa];  (* MOVZX (% r15) (% dl) *)
 [0x44; 0x0f; 0xb6; 0xfa];  (* MOVZX (% r15d) (% dl) *)
 [0x4c; 0x0f; 0xbf; 0xfa];  (* MOVSX (% r15) (% dx) *)
 [0x44; 0x0f; 0xbf; 0xfa];  (* MOVSX (% r15d) (% dx) *)
 [0x4c; 0x0f; 0xbe; 0xfa];  (* MOVSX (% r15) (% dl) *)
 [0x44; 0x0f; 0xbe; 0xfa];  (* MOVSX (% r15d) (% dl) *)
 [0x4c; 0x63; 0xfa];        (* MOVSX (% r15) (% edx) *)
 [0x44; 0x63; 0xfa]         (* MOVSX (% r15d) (% edx) *)
];;

(*let iclasses =
  map (function (0x48::l::m) -> l::m | m -> m) iclasses;;*)

(* ------------------------------------------------------------------------- *)
(* Run a random example.                                                     *)
(* ------------------------------------------------------------------------- *)

let template =
 `ensures x86
     (\s. bytes_loaded s (word pc) ibytes /\
          read RIP s = word pc /\
          regfile s = input_state)
     (\s. regfile s = output_state)
     (MAYCHANGE [RIP; RAX; RCX; RDX; RBX; RBP; RSI; RDI;
                 R8; R9; R10; R11; R12; R13; R14; R15] ,,
      MAYCHANGE SOME_FLAGS)`;;

let num_two_to_64 = Num.num_of_string "18446744073709551616";;

let rec split_first_n (ls: 'a list) (n: int) =
  if n = 0 then ([], ls)
  else match ls with
    | h::t -> let l1, l2 = split_first_n t (n-1) in (h::l1, l2)
    | [] -> failwith "n cannot be smaller than the length of ls";;

let only_undefinedness =
  let zx_tm = `word_zx:int32->int64` in
  let is_undefname s =
     String.length s >= 10 && String.sub s 0 10 = "undefined_" in
  let is_undef t = is_var t && is_undefname (fst(dest_var t)) in
  let is_nundef tm = match tm with
      Comb(Comb(Const("=",_),l),r) when is_undef l -> true
    | Comb(Comb(Const("=",_),Comb(z,l)),r) when z = zx_tm && is_undef l -> true
    | Comb(Const("~",_),l) when is_undef l -> true
    | _ -> is_undef tm in
  forall is_nundef o conjuncts;;


let run_random_simulation () =
  let ibytes:int list = random_instruction iclasses in
  let icode = itlist (fun h t -> num h +/ num 256 */ t) ibytes num_0 in
  let _ = Format.print_string
   ("random inst: decode "^string_of_num icode ^ "\n") in

  let ibyteterm =
    mk_flist(map (curry mk_comb `word:num->byte` o mk_small_numeral) ibytes) in

  let input_state = random_regstate() in

  let outfile = Filename.temp_file "x86simulator" ".out" in

  let command =
    "x86/proofs/x86simulate '" ^
    end_itlist (fun s t -> s ^ "," ^ t) (map string_of_int ibytes) ^
    "' " ^
    end_itlist (fun s t -> s ^ " " ^ t) (map string_of_num input_state) ^
    " >" ^ outfile in

  let _ = Sys.command command in

  (*** This branch determines whether the actual simulation worked ***)
  (*** In each branch we try to confirm that we likewise do or don't ***)

  if strings_of_file outfile <> [] then
    let resultstring = string_of_file outfile in

    let output_state_raw =
      map (fun (Ident s) -> num_of_string s)
          (lex(explode resultstring)) in

    (* Synthesize q registers from two 64 ints *)
    let output_state = output_state_raw in

    let goal = subst
      [ibyteterm,`ibytes:byte list`;
       mk_flist(map mk_numeral input_state),`input_state:num list`;
       mk_flist(map mk_numeral output_state),`output_state:num list`]
      template in

    let execth = X86_MK_EXEC_RULE(REFL ibyteterm) in

    let inst_th = Option.get (snd execth).(0) in
    let decoded =
      rand(rand(snd(strip_forall(concl(inst_th))))) in

    let result =
      match
       (REWRITE_TAC[regfile; CONS_11; FLAGENCODING_11; VAL_WORD_GALOIS] THEN
        REWRITE_TAC[DIMINDEX_64; DIMINDEX_128] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[SOME_FLAGS] THEN
        X86_SIM_TAC execth [1] THEN
        (* Deal with the BSWAP instruction *)
        TRY (REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
          REWRITE_TAC[BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
          REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC EXPAND_CASES_CONV THEN
          CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
          FAIL_TAC "Not BSWAP, or BSWAP having more complicated "))
       ([],goal)
      with
        _,[_,endres],_ ->
         (if endres = `T` || only_undefinedness endres then
            (Format.print_string "Modulo undefinedness "; true)
          else
            let _,[_,gsd],_ =
             (REWRITE_TAC[regfile; CONS_11; FLAGENCODING_11; VAL_WORD_GALOIS] THEN
              REWRITE_TAC[DIMINDEX_64; DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
              REWRITE_TAC[SOME_FLAGS]) ([], goal) in
             (print_qterm gsd; Format.print_newline(); false))
     | _,[],_ -> true in
    (decoded,result)
  else
    let decoded = mk_numeral icode in
    decoded,not(can X86_MK_EXEC_RULE(REFL ibyteterm));;

(* ------------------------------------------------------------------------- *)
(* Keep running tests till a failure happens then return it.                 *)
(* ------------------------------------------------------------------------- *)

let time_limit_sec = 1800.0;;
let tested_instances = ref 0;;

let rec run_random_simulations start_t =
  let decoded,result = run_random_simulation() in
  if result then begin
    tested_instances := !tested_instances + 1;
    let fey = if is_numeral decoded
              then " (fails correctly) instruction code " else " " in
    let _ = Format.print_string("OK:" ^ fey ^ string_of_term decoded);
            Format.print_newline() in
    let now_t = Sys.time() in
    if now_t -. start_t > time_limit_sec then
      let _ = Printf.printf "Finished (time limit: %fs, tested instances: %d)\n"
          time_limit_sec !tested_instances in
      None
    else run_random_simulations start_t
  end
  else Some (decoded,result);;

(*** Depending on the degree of repeatability wanted.
 *** After a few experiments I'm now going full random.
 ***
 *** Random.init(Hashtbl.hash (Sys.getenv "HOST"));;
 ***)

Random.self_init();;

let start_t = Sys.time() (* unit is sec *) in
  match run_random_simulations start_t with
  | Some (t,_) -> Printf.printf "Error: term `%s`" (string_of_term t); failwith "simulator"
  | None -> ();;
