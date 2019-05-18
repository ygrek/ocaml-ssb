open Sodium
open ExtLib
open Prelude

let secret = Sign.Bytes.to_secret_key @@ Bytes.of_string "\2335S\011\n\206\1273`4\174E\0294,\184\163\222\183\231\255\1984\022\131f5\165W\001Z\024\135P\027\137\220\239\n\229\130\201\178\222Yq\190G\187w\210\191he\228\015\1507\139\151\209\014\155\020"
(* h1AbidzvCuWCybLeWXG+R7t30r9oZeQPljeLl9EOmxQ= *)
let public = Sign.Bytes.to_public_key @@ Bytes.of_string "\135P\027\137\220\239\n\229\130\201\178\222Yq\190G\187w\210\191he\228\015\1507\139\151\209\014\155\020"

let main_network = Auth.Bytes.to_key @@ Bytes.of_string "\xd4\xa1\xcb\x88\xa6\x6f\x02\xf8\xdb\x63\x5c\xe2\x64\x41\xcc\x5d\xac\x1b\x08\x42\x0c\xea\xac\x23\x08\x39\xb7\x55\x84\x5a\x9f\xfb"

let concat_s l = String.concat "" (List.map Bytes.to_string l)
let concat l = Bytes.unsafe_of_string @@ concat_s l

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
let verify_hello s =
   if String.length s <> 64 then fail "verify_hello: length %d expected 64" (String.length s);
   let hmac = String.slice ~last:32 s in
   let pk = String.slice ~first:32 s in
   Auth.Bytes.(verify main_network (to_auth @@ Bytes.of_string hmac) (Bytes.of_string pk));
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

let sha256 x = Bytes.unsafe_of_string @@ Sha256.(to_bin @@ string @@ Bytes.to_string x)

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
let client_auth ~shared_secrets:(ss_ab,ss_aB,_) ~server_pk ~sk ~pk =
  let detached_sig_A = Sign.Bytes.sign_detached sk (concat [
    Auth.Bytes.of_key main_network;
    Sign.Bytes.of_public_key server_pk;
    sha256 @@ ss_ab;
  ])
  in
  let key = Secret_box.Bytes.to_key @@ sha256 @@ concat [
    Auth.Bytes.of_key main_network;
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
let client_verify ~shared_secrets:(ss_ab,ss_aB,ss_Ab) ~detached_sig_A ~pk ~server_pk msg =
  let key = concat [
    Auth.Bytes.of_key main_network;
    ss_ab;
    ss_aB;
    ss_Ab;
  ] in
  let detached_sig_B = Secret_box.Bytes.secret_box_open (Secret_box.Bytes.to_key @@ sha256 key) msg (Secret_box.nonce_of_bytes @@ Bytes.make 24 '\x00') in
  let verify = concat [
    Auth.Bytes.of_key main_network;
    Sign.Bytes.of_signature detached_sig_A;
    Sign.Bytes.of_public_key pk;
    sha256 ss_ab;
  ] in
  Sign.Bytes.verify server_pk (Sign.Bytes.to_signature detached_sig_B) verify;
  Secret_box.Bytes.to_key key

(*
concat(
  nacl_auth(
    msg: client_ephemeral_pk,
    key: network_identifier
  ),
  client_ephemeral_pk
)
*)
let client_hello ~epk =
  let epk = Box.Bytes.of_public_key epk in
  concat_s [Auth.Bytes.(of_auth @@ auth main_network epk); epk]

let client_handshake ~server_pk (ic,oc) =
  let (esk,epk) = Box.random_keypair () in
  let%lwt () = Lwt_io.write oc (client_hello ~epk) in
  let server_hello = Bytes.create 64 in
  let%lwt () = Lwt_io.read_into_exactly ic server_hello 0 64 in
  let server_epk = verify_hello @@ Bytes.to_string server_hello in
  let shared_secrets = shared_secrets ~sk:secret ~esk ~server_pk ~server_epk in
  let (detached_sig_A,client_auth) = client_auth ~shared_secrets ~server_pk ~sk:secret ~pk:public in
  assert (Bytes.length client_auth = 112);
  let%lwt () = Lwt_io.write oc (Bytes.unsafe_to_string client_auth) in
  let server_accept = Bytes.create 80 in
  let%lwt () = Lwt_io.read_into_exactly ic server_accept 0 80 in
  Lwt.return @@ client_verify ~shared_secrets ~detached_sig_A ~pk:public ~server_pk server_accept

let execute_client ~server_pk c =
  let _shared_key = client_handshake ~server_pk c in
  printfn "verified";
  Lwt.return_unit

let test () =
  (* net:192.168.1.40:8008~shs:nRlzaYFcYB6X2QevJ3MZrgJnhozOesb4hrd7ENK4PS4= *)
  let server_pk = Sign.Bytes.to_public_key @@ Bytes.of_string @@ Base64.decode_string "nRlzaYFcYB6X2QevJ3MZrgJnhozOesb4hrd7ENK4PS4" in
  Lwt_io.with_connection Unix.(ADDR_INET (inet_addr_of_string "192.168.1.40",8008)) (execute_client ~server_pk)

let () =
  match Sys.argv |> Array.to_list |> List.tl with
  | "-v"::[] -> print_endline Version.id
  | "test"::[] -> Lwt_main.run @@ test ()
  | _ -> fail "wut?"
