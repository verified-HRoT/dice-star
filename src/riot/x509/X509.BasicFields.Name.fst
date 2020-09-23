module X509.BasicFields.Name

open LowParse.Low.Base

open ASN1.Spec
open ASN1.Low

open X509.Base
open X509.BasicFields.RelativeDistinguishedName

open FStar.Integers

#set-options "--z3rlimit 32 --initial_fuel  2 --initial_ifuel  2"
(*)
let x509_name_pair_t
: Type = ( name: x501_name_t & t:directory_string_type { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } )

let valid_x501_name_list
  (l: list x509_name_pair_t)
: Type0
= 0 < List.length l

(* SHOULD BE PARTIAL EVALUATED OUT *)
let x501_name_list_t
: Type
= l: list x509_name_pair_t { valid_x501_name_list l }

#set-options "--fuel 2 --ifuel 2"

let rec x509_name_t
  (l: x501_name_list_t)
: Tot (Type)
  (decreases (List.length l))
= match l with
  | hd :: [] -> let name = dfst hd in
               let t: t: _ { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } = dsnd hd in
               get_parser_type (parse_RDN_name name t)
  | hd :: tl -> let name = dfst hd in
               let t: t: _ { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } = dsnd hd in
               (get_parser_type (parse_RDN_name name t)) `tuple2` (x509_name_t tl)

let rec parse_x509_name_kind
  (l: x501_name_list_t)
: Tot (parser_kind)
  (decreases (List.length l))
= match l with
  | hd :: [] -> let name = dfst hd in
               let t: t: _ { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } = dsnd hd in
               get_parser_kind (parse_RDN_name name t)
  | hd :: tl -> let name = dfst hd in
               let t: t: _ { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } = dsnd hd in
               (get_parser_kind (parse_RDN_name name t)) `and_then_kind` (parse_x509_name_kind tl)

let rec parse_x509_name
  (l: x501_name_list_t)
: Tot (parser (parse_x509_name_kind l) (x509_name_t l))
  (decreases (List.length l))
= match l with
  | hd :: [] -> let name = dfst hd in
               let t: t: _ { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } = dsnd hd in
               (x509_name_t l)
               `coerce_parser`
               parse_RDN_name name t
  | hd :: tl -> let name = dfst hd in
               let t: t: _ { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } = dsnd hd in
               (x509_name_t l)
               `coerce_parser`
               ((parse_RDN_name name t) `nondep_then` (parse_x509_name tl))

let test
  (l: x501_name_list_t { match l with hd :: [] -> True | _ -> False })
= let hd :: tl = l in
  let name = dfst hd in
  let t: t: _ { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } = dsnd hd in
//   // normalize_term (parse_x509_name l)
  assert (x509_name_t l == get_parser_type (parse_RDN_name name t));
  assert (parse_x509_name_kind l == get_parser_kind (parse_RDN_name name t));
  assert (parse_x509_name l == parse_RDN_name name t)
  // let p = (parse_RDN_name name t) in ()
  // assert_norm (get_parser_type (parse_RDN_name name t) == x509_name_t l)

let rec serialize_x509_name
  (l: x501_name_list_t)
: Tot (serializer (parse_x509_name l))
  (decreases (List.length l))
= match l with
  | hd :: [] ->
               let name = dfst hd in
               let t: t: _ { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } = dsnd hd in
               // let s = coerce_parser_serializer
               //   // (parse_x509_name l)
               //   (parse_RDN_name name t)
               //   (serialize_RDN_name name t)
               //   () in
               assert (x509_name_t l == get_parser_type (parse_RDN_name name t));
               assert (parse_x509_name l == parse_RDN_name name t);
               admit()
  | hd :: tl -> let name = dfst hd in
               let t: t: _ { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } = dsnd hd in
               admit()
              //  coerce_parser_serializer
              //    (parse_x509_name l)
              //    ((serialize_RDN_name name t) `serialize_nondep_then` (parse_x509_name_kind tl))
              //    ()
