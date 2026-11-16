(* SPDX-FileCopyrightText: Copyright 2022-2023 Arm Limited and/or its affiliates <open-source-office@arm.com>
   SPDX-License-Identifier: BSD-3-Clause

   Actual AST extraction through pinned ASLRefEAC1's Builder and strict Typing.
   Source interfaces/notices: reference/aslref and reference/SOURCE.json.
   Local extension: one complete zero-argument function with one closed return.
   This source-to-AST producer is TCB, not a verified ASL parser or ISA model. *)
open Asllib
open AST

let pin = "ffad2692c4580538e8db7bf6631aa886edfc7423"
let phase = ref "arguments"
exception ExtractionRefusal of string
let json_string value =
  let result = Buffer.create (String.length value + 2) in
  Buffer.add_char result '"';
  String.iter (fun character -> match character with
    | '"' -> Buffer.add_string result "\\\""
    | '\\' -> Buffer.add_string result "\\\\"
    | character when Char.code character < 32 ->
        Buffer.add_string result (Printf.sprintf "\\u%04x" (Char.code character))
    | character -> Buffer.add_char result character) value;
  Buffer.add_char result '"'; Buffer.contents result
let refuse reason = raise (ExtractionRefusal ("ASL1 extraction refused: " ^ reason))
let v1 node = if node.version <> V1 then refuse "non-ASLv1 annotated node"
let byte buffer value =
  if value < 0 || value > 255 then refuse "byte outside range";
  Buffer.add_char buffer (Char.chr value)

let magnitude buffer value =
  if Z.sign value < 0 || Z.numbits value > 64 then
    refuse "literal magnitude exceeds the unsigned 64-bit wire profile";
  for index = 0 to 7 do byte buffer (Z.to_int (Z.extract value (8 * index) 8)) done

let name buffer value =
  let length = String.length value in
  if length = 0 || length > 255 then refuse "empty or oversized function name";
  byte buffer length;
  Buffer.add_string buffer value

let width node =
  v1 node;
  match node.desc with
  | E_Literal (L_Int value) when Z.sign value >= 0 && Z.leq value (Z.of_int 64) ->
      Z.to_int value
  | _ -> refuse "return bit width must be a concrete integer in 0..64"

let return_type buffer = function
  | Some ty ->
      v1 ty;
      (match ty.desc with
      | T_Int UnConstrained -> byte buffer 0
      | T_Bits (size, []) -> byte buffer 1; byte buffer (width size)
      | T_Bool -> byte buffer 2
      | _ -> refuse "unsupported return type, constraint, alias or bitfield")
  | None -> refuse "function has no return type"

let rec expression buffer depth node =
  if depth > 64 then refuse "expression depth exceeds 64";
  v1 node;
  match node.desc with
  | E_Literal (L_Int value) ->
      byte buffer 0;
      byte buffer (if Z.sign value < 0 then 1 else 0);
      magnitude buffer (Z.abs value)
  | E_Literal (L_BitVector value) ->
      let size = Bitvector.length value in
      if size < 0 || size > 64 then refuse "literal bit width exceeds 64";
      byte buffer 1; byte buffer size;
      magnitude buffer (Bitvector.to_z_unsigned value)
  | E_Literal (L_Bool value) -> byte buffer 2; byte buffer (if value then 1 else 0)
  | E_Binop ((`ADD | `SUB as operator), left, right) ->
      byte buffer 3; byte buffer (if operator = `ADD then 0 else 1);
      expression buffer (depth + 1) left;
      expression buffer (depth + 1) right
  | _ -> refuse "unsupported expression constructor or operator"

let function_of_complete_ast ast =
  match ast with
  | [ ({ desc = D_Func fn; _ } as declaration) ] ->
      v1 declaration;
      if fn.parameters <> [] || fn.args <> [] || fn.builtin
         || fn.subprogram_type <> ST_Function || fn.recurse_limit <> None
         || fn.override <> None
      then refuse "unsupported function parameter/body/signature attributes";
      (match fn.qualifier with
      | None | Some Pure -> ()
      | _ -> refuse "unsupported function qualifier");
      fn
  | _ -> refuse "the complete module must contain exactly one function declaration"

let return_expression fn =
  match fn.body with
  | SB_ASL statement ->
      v1 statement;
      (match statement.desc with
      | S_Return (Some value) -> value
      | _ -> refuse "the complete body must be one value-return statement")
  | SB_Primitive _ -> refuse "primitive function body"

let payload fn =
  let result = Buffer.create 128 in
  return_type result fn.return_type;
  expression result 0 (return_expression fn);
  Buffer.contents result

let main () =
  if Array.length Sys.argv <> 2 then refuse "expected exactly one ASL source path";
  let path = Sys.argv.(1) in
  if (Unix.stat path).Unix.st_size > 1048576 then refuse "source exceeds 1 MiB";
  phase := "parse";
  let parsed = Builder.from_file `ASLv1 path in
  phase := "parsed_profile";
  let parsed_fn = function_of_complete_ast parsed in
  ignore (return_expression parsed_fn);
  (* This is ASLRef's real strict typechecker, not a producer success premise. *)
  phase := "typecheck";
  let typed, global = Typing.TypeCheckDefault.type_check_ast parsed in
  phase := "export";
  let typed_fn = function_of_complete_ast typed in
  let parsed_signature = Buffer.create 8 and typed_signature = Buffer.create 8 in
  return_type parsed_signature parsed_fn.return_type;
  return_type typed_signature typed_fn.return_type;
  if Buffer.contents parsed_signature <> Buffer.contents typed_signature then
    refuse "typing changed the supported return signature";
  (* The real typechecker removes the parser's E_Tuple [e] parenthesis nodes.
     Export its actual returned AST, not a new local normalization of source.
     This source-to-typed-AST transformation remains part of the producer TCB. *)
  let typed_payload = payload typed_fn in
  (* The reference result uses ASLRef's actual Interpreter.Make/StaticBackend,
     through its public static evaluator. It is diagnostic and is NOT carried
     in the packet or allowed to select the Lean goal/result. *)
  phase := "reference_eval";
  let reference = StaticInterpreter.static_eval (StaticEnv.with_empty_local global)
    (return_expression typed_fn) in
  let reference_kind, reference_value = match reference with
    | L_Int value -> "integer", Z.to_string value
    | L_BitVector value -> "bits", Z.to_string (Bitvector.to_z_unsigned value)
    | L_Bool value -> "boolean", string_of_bool value
    | _ -> refuse "reference result outside supported literal carriers"
  in
  phase := "packet";
  let result = Buffer.create 256 in
  Buffer.add_string result "ASL1"; byte result 1;
  Buffer.add_string result pin;
  name result parsed_fn.name; name result typed_fn.name;
  Buffer.add_string result typed_payload;
  if Buffer.length result > 65536 then refuse "packet exceeds 64 KiB";
  Printf.eprintf "{\"pin\":%s,\"source_name\":%s,\"typed_name\":%s,\"declarations\":1,\"strict_typecheck\":\"TypeCheck\",\"reference_kind\":%s,\"reference_value\":%s}\n%!"
    (json_string pin) (json_string parsed_fn.name) (json_string typed_fn.name)
    (json_string reference_kind) (json_string reference_value);
  set_binary_mode_out stdout true;
  output_string stdout (Buffer.contents result);
  flush stdout

let () =
  try main () with
  | Error.ASLException error ->
      Printf.eprintf "ASLREF_REFUSAL phase=%s kind=asl_error label=%s\n%s\n%!"
        !phase (Error.error_label error.desc) (Error.error_to_string error);
      exit 3
  | ExtractionRefusal reason ->
      Printf.eprintf "ASLREF_REFUSAL phase=%s kind=profile_refusal reason=%s\n%!" !phase reason;
      exit 4
  | error ->
      Printf.eprintf "ASLREF_REFUSAL phase=%s kind=construction_error reason=%s\n%!"
        !phase (Printexc.to_string error);
      exit 2
