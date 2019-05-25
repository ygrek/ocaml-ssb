open Printf
open Sodium
open ExtLib
open Prelude

let secret = Sign.Bytes.to_secret_key @@ Bytes.of_string "\2335S\011\n\206\1273`4\174E\0294,\184\163\222\183\231\255\1984\022\131f5\165W\001Z\024\135P\027\137\220\239\n\229\130\201\178\222Yq\190G\187w\210\191he\228\015\1507\139\151\209\014\155\020"
(* h1AbidzvCuWCybLeWXG+R7t30r9oZeQPljeLl9EOmxQ= *)
let public = Sign.Bytes.to_public_key @@ Bytes.of_string "\135P\027\137\220\239\n\229\130\201\178\222Yq\190G\187w\210\191he\228\015\1507\139\151\209\014\155\020"

let concat_s l = String.concat "" (List.map Bytes.unsafe_to_string l)
let concat l = Bytes.unsafe_of_string @@ concat_s l

let sha256 x = Bytes.unsafe_of_string @@ Sha256.(to_bin @@ string @@ Bytes.to_string x)

let lwt_io_read ch n =
  assert (n > 0);
  let b = Bytes.create n in
  let%lwt () = Lwt_io.read_into_exactly ch b 0 n in
  Lwt.return b

let lwt_io_read_s ch n = Lwt.map Bytes.unsafe_to_string (lwt_io_read ch n)

module BoxStream = struct

  exception Goodbye

  type 'a stream = { ch : 'a Lwt_io.channel; key : Secret_box.secret_key; mutable nonce : Secret_box.nonce; }
  type t = { mutable input : Lwt_io.input stream option; mutable output : Lwt_io.output stream option; }

  let create (ic,oc) ~network_key ~server_pk ~server_epk ~pk ~epk key =
    let make_key pk = Secret_box.Bytes.to_key @@ sha256 @@ concat [sha256 @@ sha256 key; Sign.Bytes.of_public_key pk] in
    let make_nonce epk = Secret_box.Bytes.to_nonce @@ Bytes.sub Auth.Bytes.(of_auth @@ auth network_key (Box.Bytes.of_public_key epk)) 0 24 in
    {
      input = Some { ch = ic; key = make_key pk; nonce = make_nonce epk };
      output = Some { ch = oc; key = make_key server_pk; nonce = make_nonce server_epk }
    }

  let send s body =
    let size = String.length body in
    assert (size > 0);
    assert (size <= 4096);
    let nonce1 = s.nonce in
    let nonce2 = Secret_box.increment_nonce nonce1 in
    s.nonce <- Secret_box.increment_nonce nonce2;
    let box2 = Secret_box.Bytes.secret_box s.key (Bytes.unsafe_of_string body) nonce2 in
    assert (Bytes.length box2 = 16 + size);
    let header = Bytes.create 18 in
    EndianBytes.BigEndian.set_int16 header 0 size;
    Bytes.blit box2 0 header 2 16;
    let box1 = Secret_box.Bytes.secret_box s.key header nonce1 in
    assert (Bytes.length box1 = 16 + 18);
    Lwt_io.write s.ch (concat_s [box1; Bytes.sub box2 16 size])

  let send t s =
    match t.output with
    | None -> fail "BoxStream.send: output already closed"
    | Some stream ->
    let rec loop pos =
      if pos < String.length s then
        let len = min 4096 (String.length s - pos) in
        let%lwt () = send stream (String.sub s pos len) in
        loop (pos+len)
      else
        Lwt_io.flush stream.ch
    in
    loop 0

  let zero_header = Bytes.make 18 '\x00'

  let goodbye t =
    match t.output with
    | None -> fail "BoxStream.goodbye: already said goodbye"
    | Some s ->
      t.output <- None;
      let%lwt () = Lwt_io.write s.ch (Bytes.unsafe_to_string @@ Secret_box.Bytes.secret_box s.key zero_header s.nonce) in
      Lwt_io.flush s.ch

  let receive t =
    match t.input with
    | None -> fail "BoxStream.receive: input already closed"
    | Some s ->
      let%lwt header_box = lwt_io_read s.ch 34 in
      let header = Secret_box.Bytes.secret_box_open s.key header_box s.nonce in
      assert (Bytes.length header = 18);
      match Bytes.equal header zero_header with
      | true ->
        t.input <- None;
        Lwt.fail Goodbye
      | false ->
        s.nonce <- Secret_box.increment_nonce s.nonce;
        let body_size = EndianBytes.BigEndian.get_uint16 header 0 in
        assert (body_size > 0);
        assert (body_size <= 4096);
        let body_box = Bytes.create (16 + body_size) in
        Bytes.blit header 2 body_box 0 16;
        let%lwt () = Lwt_io.read_into_exactly s.ch body_box 16 body_size in
        let body = Secret_box.Bytes.secret_box_open s.key body_box s.nonce in
        s.nonce <- Secret_box.increment_nonce s.nonce;
        Lwt.return @@ Bytes.unsafe_to_string body

end

module Handshake = struct

(*
assert(length(msg2) == 64)

server_hmac = first_32_bytes(msg2)
server_ephemeral_pk = last_32_bytes(msg2)

assert_nacl_auth_verify(
  authenticator: server_hmac,
  msg: server_ephemeral_pk,
  key: network_identifier
)
*)
let verify_hello ~network_key s =
   if String.length s <> 64 then fail "verify_hello: length %d expected 64" (String.length s);
   let hmac = String.slice ~last:32 s in
   let pk = String.slice ~first:32 s in
   Auth.Bytes.(verify network_key (to_auth @@ Bytes.of_string hmac) (Bytes.of_string pk));
   Box.Bytes.to_public_key @@ Bytes.of_string pk

(*
shared_secret_ab = nacl_scalarmult(
  client_ephemeral_sk,
  server_ephemeral_pk
)

shared_secret_aB = nacl_scalarmult(
  client_ephemeral_sk,
  pk_to_curve25519(server_longterm_pk)
)

shared_secret_Ab = nacl_scalarmult(
  sk_to_curve25519(client_longterm_sk),
  server_ephemeral_pk
)
*)
let shared_secrets ~sk ~esk ~server_pk ~server_epk =
  let open Scalar_mult in
  let esk = Bytes.to_integer @@ Box.Bytes.of_secret_key esk in
  let server_epk = Bytes.to_group_elt @@ Box.Bytes.of_public_key server_epk in
  Bytes.of_group_elt @@ mult esk server_epk,
  Bytes.of_group_elt @@ mult esk (Bytes.to_group_elt @@ Box.Bytes.of_public_key @@ Sign.box_public_key server_pk),
  Bytes.of_group_elt @@ mult (Bytes.to_integer @@ Box.Bytes.of_secret_key @@ Sign.box_secret_key sk) server_epk

(*
detached_signature_A = nacl_sign_detached(
  msg: concat(
    network_identifier,
    server_longterm_pk,
    sha256(shared_secret_ab)
  ),
  key: client_longterm_sk
)
nacl_secret_box(
  msg: concat(
    detached_signature_A,
    client_longterm_pk
  ),
  nonce: 24_bytes_of_zeros,
  key: sha256(
    concat(
      network_identifier,
      shared_secret_ab,
      shared_secret_aB
    )
  )
)
*)
let client_auth ~network_key ~shared_secrets:(ss_ab,ss_aB,_) ~server_pk ~sk ~pk =
  let detached_sig_A = Sign.Bytes.sign_detached sk (concat [
    Auth.Bytes.of_key network_key;
    Sign.Bytes.of_public_key server_pk;
    sha256 @@ ss_ab;
  ])
  in
  let key = Secret_box.Bytes.to_key @@ sha256 @@ concat [
    Auth.Bytes.of_key network_key;
    ss_ab;
    ss_aB;
  ] in
  detached_sig_A,
  Secret_box.Bytes.secret_box key (concat [Sign.Bytes.of_signature detached_sig_A; Sign.Bytes.of_public_key pk]) (Secret_box.nonce_of_bytes @@ Bytes.make 24 '\x00')

(*
detached_signature_B = assert_nacl_secretbox_open(
  ciphertext: msg4,
  nonce: 24_bytes_of_zeros,
  key: sha256(
    concat(
      network_identifier,
      shared_secret_ab,
      shared_secret_aB,
      shared_secret_Ab
    )
  )
)
assert_nacl_sign_verify_detached(
  sig: detached_signature_B,
  msg: concat(
    network_identifier,
    detached_signature_A,
    client_longterm_pk,
    sha256(shared_secret_ab)
  ),
  key: server_longterm_pk
)
*)
let client_verify ~network_key ~shared_secrets:(ss_ab,ss_aB,ss_Ab) ~detached_sig_A ~pk ~server_pk msg =
  let key = concat [
    Auth.Bytes.of_key network_key;
    ss_ab;
    ss_aB;
    ss_Ab;
  ] in
  let detached_sig_B = Secret_box.Bytes.secret_box_open (Secret_box.Bytes.to_key @@ sha256 key) msg (Secret_box.nonce_of_bytes @@ Bytes.make 24 '\x00') in
  let verify = concat [
    Auth.Bytes.of_key network_key;
    Sign.Bytes.of_signature detached_sig_A;
    Sign.Bytes.of_public_key pk;
    sha256 ss_ab;
  ] in
  Sign.Bytes.verify server_pk (Sign.Bytes.to_signature detached_sig_B) verify;
  key

(*
concat(
  nacl_auth(
    msg: client_ephemeral_pk,
    key: network_identifier
  ),
  client_ephemeral_pk
)
*)
let client_hello ~network_key ~epk =
  let epk = Box.Bytes.of_public_key epk in
  concat_s [Auth.Bytes.(of_auth @@ auth network_key epk); epk]

let client_handshake ~network_key ~server_pk (ic,oc) =
  let (esk,epk) = Box.random_keypair () in
  let%lwt () = Lwt_io.write oc (client_hello ~network_key ~epk) in
  let%lwt server_epk = Lwt.map (verify_hello ~network_key) (lwt_io_read_s ic 64) in
  let shared_secrets = shared_secrets ~sk:secret ~esk ~server_pk ~server_epk in
  let (detached_sig_A,client_auth) = client_auth ~network_key ~shared_secrets ~server_pk ~sk:secret ~pk:public in
  assert (Bytes.length client_auth = 112);
  let%lwt () = Lwt_io.write oc (Bytes.unsafe_to_string client_auth) in
  let%lwt server_accept = lwt_io_read ic 80 in
  let shared_key = client_verify ~network_key ~shared_secrets ~detached_sig_A ~pk:public ~server_pk server_accept in
  Lwt.return @@ BoxStream.create (ic,oc) ~network_key ~server_pk ~server_epk ~pk:public ~epk shared_key

end (* Handshake *)


module RPC_raw = struct

type t = { input : Lwt_io.input_channel; output : Lwt_io.output_channel }

(* allocates too much *)
let create box_stream =
  let output = Lwt_io.make ~close:(fun () -> BoxStream.goodbye box_stream) ~mode:Lwt_io.output
    begin fun bytes ofs len ->
      let b = Bytes.create len in
      let () = Lwt_bytes.blit_to_bytes bytes ofs b 0 len in
      let%lwt () = BoxStream.send box_stream (Bytes.unsafe_to_string b) in
      Lwt.return len
    end
  in
  let buffer = ref "" in
  let input = Lwt_io.make ~mode:Lwt_io.input
    begin fun bytes ofs len ->
      let%lwt () =
        if !buffer = "" then
          Lwt.map ((:=) buffer) (try%lwt BoxStream.receive box_stream with BoxStream.Goodbye -> Lwt.return "")
        else
          Lwt.return_unit
      in
      match !buffer with
      | "" -> Lwt.return 0 (* End_of_file *)
      | _ ->
        let to_blit = min len (String.length !buffer) in
        Lwt_bytes.blit_from_bytes (Bytes.unsafe_of_string !buffer) 0 bytes ofs to_blit;
        buffer := String.sub !buffer to_blit (String.length !buffer - to_blit);
        Lwt.return to_blit
    end
  in
  { input; output }

type content_type = Binary | Utf8 | Json
type header = { stream : bool; end_or_error : bool; typ : content_type; size : int; req_id : int32; }

let read_header ch =
  let%lwt h = lwt_io_read_s ch 9 in
  let flags = Char.code h.[0] in
  let typ = match flags land 3 with 0 -> Binary | 1 -> Utf8 | 2 -> Json | _ -> fail "bad content type in header" in
  let stream = flags land 8 <> 0 in
  let end_or_error = flags land 4 <> 0 in
  let size = Unsigned.UInt32.(to_int @@ of_int32 @@ EndianString.BigEndian.get_int32 h 1) in
  let req_id = EndianString.BigEndian.get_int32 h 5 in
  Lwt.return { stream; end_or_error; typ; size; req_id; }

let serialize_header { stream; end_or_error; typ; size; req_id } =
  let h = Bytes.create 9 in
  h.[0] <- Char.chr @@ (match typ with Binary -> 0 | Utf8 -> 1 | Json -> 2) lor (if end_or_error then 4 else 0) lor (if stream then 8 else 0);
  EndianBytes.BigEndian.set_int32 h 1 Unsigned.UInt32.(to_int32 @@ of_int size);
  EndianBytes.BigEndian.set_int32 h 5 req_id;
  Bytes.unsafe_to_string h

let yes = function true -> "yes" | false -> "no"
let show_typ = function Binary -> "binary" | Utf8 -> "utf8" | Json -> "json"
let show_header h = sprintf "stream:%s end:%s typ:%s size:%d req:%ld" (yes h.stream) (yes h.end_or_error) (show_typ h.typ) h.size h.req_id

let read t =
  let%lwt h = read_header t.input in
  let%lwt s = lwt_io_read_s t.input h.size in
  printfn "> %s" (show_header h);
  printfn "> %s" s;
  Lwt.return (h,s)

let write t (h,msg) =
  printfn ": %s" (show_header h);
  printfn ": %s" msg;
  let%lwt () = Lwt_io.write t.output (serialize_header h) in
  let%lwt () = Lwt_io.write t.output msg in
  let%lwt () = Lwt_io.flush t.output in
  Lwt.return_unit

end

let show_feed_id pk =
  sprintf "@%s=.ed25519" @@ Base64.encode_string @@ Bytes.unsafe_to_string @@ Sign.Bytes.of_public_key pk

module RPC = struct

type conn = { mutable last_req : int32; rpc : RPC_raw.t; handlers : (int32, (RPC_raw.header -> string -> unit Lwt.t)) Hashtbl.t; stop : unit Lwt.u }

let start box_stream on_request =
  let rpc = RPC_raw.create box_stream in
  let handlers = Hashtbl.create 10 in
  let handle f h body =
    try%lwt
      f h body
    with exn ->
      eprintfn "W: req_id %ld handler exn : %s" h.RPC_raw.req_id (Printexc.to_string exn);
      Lwt.return_unit
  in
  let (should_stop, stop) = Lwt.wait () in
  let exception Break in
  Lwt.async begin fun () ->
    try%lwt
      while%lwt true do
        let%lwt (h,body) = Lwt.pick [Lwt.bind should_stop (fun () -> Lwt.fail Break); RPC_raw.read rpc] in
        match Int32.compare h.req_id 0l > 0 with
        | true -> handle on_request h body
        | false ->
        match Hashtbl.find handlers (Int32.neg h.req_id) with
        | exception Not_found -> eprintfn "W: req_id %ld unknown, ignoring" h.req_id; Lwt.return_unit
        | f -> handle f h body
      done
    with
    | Break -> Lwt.return_unit
    | exn -> eprintfn "E: RPC unexpected exn : %s" (Printexc.to_string exn); Lwt.return_unit
  end;
  { last_req = 0l; rpc; handlers; stop }

let stop rpc = Lwt.wakeup rpc.stop ()

let bracket rpc f = Lwt.finalize f (fun () -> stop rpc; Lwt.return_unit)

let new_request conn =
  conn.last_req <- Int32.succ conn.last_req;
  conn.last_req

let send_stream_end conn ?error req_id =
  let body = Option.map_default Yojson.Safe.to_string "true" error in
  let a = RPC_raw.{ stream=true; end_or_error=true; typ=Json; size=String.length body; req_id=Int32.neg req_id; } in
  RPC_raw.write conn.rpc (a,body)

let source conn body =
  let (stream,push) = Lwt_stream.create () in
  let req_id = new_request conn in
  Hashtbl.add conn.handlers req_id (fun h body -> push (Some (h,body)); Lwt.return_unit);
  let h = RPC_raw.{ stream=true; end_or_error=false; req_id; typ=Json; size=String.length body } in
  let%lwt () = RPC_raw.write conn.rpc (h,body) in
  Lwt.return (stream,req_id)

let source conn body =
  let%lwt (incoming,req_id) = source conn body in
  Lwt.return @@ Lwt_stream.from begin fun () ->
    let%lwt (h,body) = Lwt_stream.next incoming in
    if h.end_or_error then
    begin
      Hashtbl.remove conn.handlers req_id;
      let%lwt () = send_stream_end conn req_id in
      Lwt.return None
    end
    else
    if not h.stream then
    begin
      Hashtbl.remove conn.handlers req_id;
      let%lwt () = send_stream_end conn ~error:(`Assoc ["error",`String "expected stream"]) req_id in
      Lwt.return None (* FIXME should wait for end from the other side *)
    end
    else
    Lwt.return (Some body)
  end

end

let json_stringify json =
  let buf = Bi_outbuf.create 10 in
  let pr = Bi_outbuf.add_string buf in
  let indent level = pr @@ String.make level ' ' in
  let rec show level x =
    match x with
    | `String _ | `Int _ | `Null | `Bool _ | `Float _ -> Yojson.Basic.write_std_json buf x
    | `Assoc [] -> pr "{}"
    | `Assoc x ->
      pr "{\n";
      x |> List.iteri (fun i (k,v) -> indent (level + 2); show 0 (`String k); pr ": "; show (level + 2) v; if i + 1 <> List.length x then pr ","; pr "\n");
      indent level;
      pr "}"
    | `List [] -> pr "[]"
    | `List l ->
      pr "[\n";
      l |> List.iteri (fun i x -> indent (level + 2); show (level + 2) x; if i + 1 <> List.length l then pr ","; pr "\n");
      indent level;
      pr "]"
  in
  show 0 json;
  Bi_outbuf.contents buf

let createHistoryStream rpc pk =
  let body = Ssb_j.string_of_createHistoryStream {
    name=["createHistoryStream"];
    type_="source";
    args=[
      {
        id=show_feed_id pk;
        sequence=0;
        limit=None;
        old=true;
        live=true;
        keys=true;
      }
    ]
  }
  in
  RPC.source rpc body |> Lwt.map (Lwt_stream.map Ssb_j.kv_json_of_string)

let chop_suffix s suffix =
  if not (String.ends_with s suffix) then fail "no suffix %S" suffix;
  String.slice ~last:(-String.length suffix) s

let verify_message pk m =
  try
    let m = match m with `Assoc m -> m | _ -> fail "not an object" in
    let (signature,signature_s) =
      try
        let s = match List.assoc "signature" m with `String s -> s | _ -> fail "not a string" in
        Sign.Bytes.to_signature @@ Bytes.unsafe_of_string @@ Base64.decode_string @@ chop_suffix s "==.sig.ed25519", s
      with exn -> fail ~exn "bad signature"
    in
    (* FIXME duplicate and extra fields *)
    let canonical = json_stringify @@ `Assoc (List.filter (fun (k,_) -> k <> "signature") m) in
    Sign.Bytes.verify pk signature (Bytes.unsafe_of_string canonical);
    let key =
      let s = chop_suffix canonical "\n}" ^ ",\n  \"signature\": \"" ^ signature_s ^ "\"\n}" in
      sprintf "%%%s=.sha256" (Base64.encode_string @@ Sha256.(to_bin @@ string s))
    in
    key, Ssb_j.message_of_string canonical
  with exn ->
    fail ~exn "verify_message : bad message"

let with_stream_iter s k =
  try%lwt
    let%lwt s = s in
    Lwt_stream.iter k s
  with exn -> eprintfn "E: with_stream_iter : %s" (Printexc.to_string exn); Lwt.return_unit

let execute_client ~network_key ~server_pk c =
  let%lwt box_stream = Handshake.client_handshake ~network_key ~server_pk c in
  let rpc = RPC.start box_stream begin fun _ _ -> eprintfn "some new req"; Lwt.return_unit end in
  RPC.bracket rpc begin fun () ->
    let%lwt () = with_stream_iter (createHistoryStream rpc server_pk) begin fun body ->
      match verify_message server_pk body.value with
      | key, msg when String.equal key body.key -> eprintfn "got %s (signature ok, id matches)" (Yojson.Basic.to_string msg.content)
      | key, _ -> eprintfn "signature ok, but bad id on message %s : expected %s" (Yojson.Basic.to_string body.value) key
      | exception exn -> eprintfn "bad signature on message %s : %s" (Yojson.Basic.to_string body.value) (Printexc.to_string exn)
    end in
    Lwt.return_unit
  end

let test_main () =
(*     "\xd4\xa1\xcb\x88\xa6\x6f\x02\xf8\xdb\x63\x5c\xe2\x64\x41\xcc\x5d\xac\x1b\x08\x42\x0c\xea\xac\x23\x08\x39\xb7\x55\x84\x5a\x9f\xfb" *)
  let main_network = Auth.Bytes.to_key @@ Bytes.of_string @@ Base64.decode_string "1KHLiKZvAvjbY1ziZEHMXawbCEIM6qwjCDm3VYRan/s" in
  (* net:192.168.1.40:8008~shs:nRlzaYFcYB6X2QevJ3MZrgJnhozOesb4hrd7ENK4PS4= *)
  let server_pk = Sign.Bytes.to_public_key @@ Bytes.of_string @@ Base64.decode_string "nRlzaYFcYB6X2QevJ3MZrgJnhozOesb4hrd7ENK4PS4" in
  Lwt_io.with_connection Unix.(ADDR_INET (inet_addr_of_string "192.168.1.40",8008)) (execute_client ~network_key:main_network ~server_pk)

let test_test () =
  let my_testnet = Auth.Bytes.to_key @@ Bytes.of_string @@ Base64.decode_string "v8Ofith0tgBWOzodXDaX7V77onfyY5uHPUCaA4pUgZA" in
  (* net:192.168.1.40:8007~shs:HocXLrFajVIqsJRrz3aek+Sdk4I1mEAhZhthzHIz1+0= *)
  let server_pk = Sign.Bytes.to_public_key @@ Bytes.of_string @@ Base64.decode_string "HocXLrFajVIqsJRrz3aek+Sdk4I1mEAhZhthzHIz1+0" in
  let%lwt () = Lwt_io.with_connection Unix.(ADDR_INET (inet_addr_of_string "192.168.1.40",8007)) (execute_client ~network_key:my_testnet ~server_pk) in
  Lwt.return_unit

let () =
  match Sys.argv |> Array.to_list |> List.tl with
  | "-v"::[] -> print_endline Version.id
  | "main"::[] -> Lwt_main.run @@ test_main ()
  | "test"::[] -> Lwt_main.run @@ test_test ()
  | "stringify"::[] -> print_endline @@ json_stringify @@ Yojson.Basic.from_string @@ Std.input_all stdin
  | _ -> fail "wut?"
