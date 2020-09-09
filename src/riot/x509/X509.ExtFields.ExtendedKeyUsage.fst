module X509.ExtFields.ExtendedKeyUsage

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec
open ASN1.Low

open X509.Base
open FStar.Integers
module B32 = FStar.Bytes

module T = FStar.Tactics
module P = FStar.Pervasives

#set-options "--z3rlimit 32 --fuel 2 --ifuel 0"

(*
 * KeyPurposeIDs
 *)

noextract unfold
let valid_keyPurposeIDs
  (oids: list (datatype_of_asn1_type OID))
: Type0
= 0 < List.length oids /\ (List.length oids) < 10

let keyPurposeIDs_oids_t
: Type
= oids: list (datatype_of_asn1_type OID) { valid_keyPurposeIDs oids }

noextract inline_for_extraction
let rec x509_keyPurposeIDs_t
  (oids: keyPurposeIDs_oids_t)
: Tot (Type0)
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( get_parser_type (parse_asn1_oid_TLV_of oid) )
  | _  -> ( x509_keyPurposeIDs_t oids'
            `tuple2`
            get_parser_type (parse_asn1_oid_TLV_of oid) )

let lemma_x509_keyPurposeIDs_unique
  (oids: keyPurposeIDs_oids_t)
: Lemma
  (ensures forall (x1: x509_keyPurposeIDs_t oids)
             (x2: x509_keyPurposeIDs_t oids).
               x1 == x2 )
= let rec lemma_x509_keyPurposeIDs_unique_prf
    (oids: keyPurposeIDs_oids_t)
    (x1 x2: x509_keyPurposeIDs_t oids)
  : Lemma
    (ensures x1 == x2 )
    (decreases (List.length oids))
  = let oids', oid = List.Tot.Base.unsnoc oids in
    List.Tot.Properties.lemma_unsnoc_length oids;
    match oids' with
    | [] -> ( () )
    | _  -> ( let x1 = x1 <: x509_keyPurposeIDs_t oids' `tuple2` get_parser_type (parse_asn1_oid_TLV_of oid) in
              let x2 = x2 <: x509_keyPurposeIDs_t oids' `tuple2` get_parser_type (parse_asn1_oid_TLV_of oid) in
              assert ( snd x1 == snd x2 );
              lemma_x509_keyPurposeIDs_unique_prf oids' (fst x1) (fst x2) ) in
  Classical.forall_intro_2 (lemma_x509_keyPurposeIDs_unique_prf oids)

noextract inline_for_extraction
let rec get_x509_keyPurposeIDs
  (oids: keyPurposeIDs_oids_t)
: Tot (x509_keyPurposeIDs_t oids)
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( oid )
  | _  -> ( (get_x509_keyPurposeIDs oids', oid)
             <: x509_keyPurposeIDs_t oids'
                `tuple2`
                get_parser_type (parse_asn1_oid_TLV_of oid) )

let rec parse_x509_keyPurposeIDs_kind
  (oids: keyPurposeIDs_oids_t)
: Tot (k: parser_kind { Mkparser_kind'?.parser_kind_subkind k == Some ParserStrong })
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( get_parser_kind (parse_asn1_oid_TLV_of oid) )
  | _  -> ( parse_x509_keyPurposeIDs_kind oids'
            `and_then_kind`
            get_parser_kind (parse_asn1_oid_TLV_of oid) )

let rec parse_x509_keyPurposeIDs
  (oids: keyPurposeIDs_oids_t)
: Tot (parser (parse_x509_keyPurposeIDs_kind oids) (x509_keyPurposeIDs_t oids))
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( parse_asn1_oid_TLV_of oid )
  | _  -> ( parse_x509_keyPurposeIDs oids'
            `nondep_then`
            parse_asn1_oid_TLV_of oid )

let rec serialize_x509_keyPurposeIDs
  (oids: keyPurposeIDs_oids_t)
: Tot (serializer (parse_x509_keyPurposeIDs oids))
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( serialize_asn1_oid_TLV_of oid )
  | _  -> ( serialize_x509_keyPurposeIDs oids'
            `serialize_nondep_then`
            serialize_asn1_oid_TLV_of oid )

noextract
let rec serialize32_x509_keyPurposeIDs_backwards
  (oids: keyPurposeIDs_oids_t)
: Tot (serializer32_backwards (serialize_x509_keyPurposeIDs oids))
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( serialize32_asn1_oid_TLV_of_backwards oid )
  | _  -> ( serialize32_x509_keyPurposeIDs_backwards oids'
            `serialize32_nondep_then_backwards`
            serialize32_asn1_oid_TLV_of_backwards oid )

// [@@T.postprocess_with postprocess_listops]
let rec serialize_x509_keyPurposeIDs_unfold_spec
  (oids: keyPurposeIDs_oids_t)
  // (x: x509_keyPurposeIDs_t oids)
: GTot (_)
  (decreases (List.length oids))
= let x = get_x509_keyPurposeIDs oids in
  let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( serialize (serialize_asn1_oid_TLV_of oid) x )
  | _  -> ( let x = x <: x509_keyPurposeIDs_t oids' `tuple2` get_parser_type (parse_asn1_oid_TLV_of oid) in
            serialize_x509_keyPurposeIDs_unfold_spec oids'
            `Seq.append`
            serialize (serialize_asn1_oid_TLV_of oid) (snd x) )

// [@@T.postprocess_with postprocess_listops]
let rec lemma_serialize_x509_keyPurposeIDs_unfold
  (oids: keyPurposeIDs_oids_t)
  // (x: x509_keyPurposeIDs_t oids)
: Lemma (ensures
  serialize (serialize_x509_keyPurposeIDs oids) (get_x509_keyPurposeIDs oids) ==
  serialize_x509_keyPurposeIDs_unfold_spec oids
)
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ()
  | _  -> ( let x = (get_x509_keyPurposeIDs oids)
                     <: x509_keyPurposeIDs_t oids' `tuple2`
                        get_parser_type (parse_asn1_oid_TLV_of oid) in
            serialize_nondep_then_eq
            (* s1 *) (serialize_x509_keyPurposeIDs oids')
            (* s2 *) (serialize_asn1_oid_TLV_of oid)
            (* in *) x;
            lemma_serialize_x509_keyPurposeIDs_unfold oids' )

(*
 * Reveals the structure and size of all oids
 * Use with fuels or `lemma_serialize_x509_keyPurposeIDs_size_norm` (defined later)
 *)

let rec predicate_serialize_x509_keyPurposeIDs_size_oids
  (oids: keyPurposeIDs_oids_t)
  // (x: x509_keyPurposeIDs_t oids)
: GTot (Type0)
  (decreases (List.length oids))
= lemma_serialize_x509_keyPurposeIDs_unfold oids;
  let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( length_of_opaque_serialization (serialize_asn1_oid_TLV_of (get_x509_keyPurposeIDs oids)) (get_x509_keyPurposeIDs oids) ==
            length_of_TLV OID (length_of_oid (get_x509_keyPurposeIDs oids)) )
  | _  -> ( let x = (get_x509_keyPurposeIDs oids) <: x509_keyPurposeIDs_t oids' `tuple2` get_parser_type (parse_asn1_oid_TLV_of oid) in
            length_of_opaque_serialization (serialize_asn1_oid_TLV_of (snd x)) (snd x) ==
            length_of_TLV OID (length_of_oid (snd x)) /\
            predicate_serialize_x509_keyPurposeIDs_size_oids oids' )

let rec serialize_x509_keyPurposeIDs_size_spec
  (oids: keyPurposeIDs_oids_t)
  // (x: x509_keyPurposeIDs_t oids)
: GTot (nat)
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( length_of_opaque_serialization (serialize_asn1_oid_TLV_of oid) (get_x509_keyPurposeIDs oids) )
  | _  -> ( let x = (get_x509_keyPurposeIDs oids) <: x509_keyPurposeIDs_t oids' `tuple2` get_parser_type (parse_asn1_oid_TLV_of oid) in
            serialize_x509_keyPurposeIDs_size_spec oids' +
            length_of_opaque_serialization (serialize_asn1_oid_TLV_of (snd x)) (snd x) )

let rec lemma_serialize_x509_keyPurposeIDs_size
  (oids: keyPurposeIDs_oids_t)
  // (x: x509_keyPurposeIDs_t oids)
: Lemma (ensures
  length_of_opaque_serialization (serialize_x509_keyPurposeIDs oids) (get_x509_keyPurposeIDs oids) ==
  serialize_x509_keyPurposeIDs_size_spec oids /\
  predicate_serialize_x509_keyPurposeIDs_size_oids oids
)
  (decreases (List.length oids))
= lemma_serialize_x509_keyPurposeIDs_unfold oids;
  let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( lemma_serialize_asn1_oid_TLV_of_size (get_x509_keyPurposeIDs oids) (get_x509_keyPurposeIDs oids) )
  | _  -> ( let x = (get_x509_keyPurposeIDs oids) <: x509_keyPurposeIDs_t oids' `tuple2` get_parser_type (parse_asn1_oid_TLV_of oid) in
            lemma_serialize_asn1_oid_TLV_of_size (snd x) (snd x);
            lemma_serialize_x509_keyPurposeIDs_unfold oids';
            lemma_serialize_x509_keyPurposeIDs_size   oids' )

let valid_x509_ext_keyPurposeIDs_ingredients
  (oids: keyPurposeIDs_oids_t)
  // (x: x509_keyPurposeIDs_t oids)
: Type0
= serialize_x509_keyPurposeIDs_size_spec oids // (get_x509_keyPurposeIDs oids)
  <= asn1_value_length_max_of_type SEQUENCE

let rec length_of_x509_keyPurposeIDs
  (oids: keyPurposeIDs_oids_t
         { valid_x509_ext_keyPurposeIDs_ingredients oids })
  // (x: x509_keyPurposeIDs_t oids
  //     { valid_x509_ext_keyPurposeIDs_ingredients oids x })
: GTot (l: asn1_value_length_of_type SEQUENCE
           { l == serialize_x509_keyPurposeIDs_size_spec oids })
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  lemma_serialize_x509_keyPurposeIDs_size oids;
  match oids' with
  | [] -> ( length_of_asn1_primitive_TLV #OID (get_x509_keyPurposeIDs oids) )
  | _  -> ( let x = (get_x509_keyPurposeIDs oids) <: x509_keyPurposeIDs_t oids' `tuple2` get_parser_type (parse_asn1_oid_TLV_of oid) in
            lemma_serialize_x509_keyPurposeIDs_size oids';
            length_of_x509_keyPurposeIDs oids' +
            length_of_asn1_primitive_TLV #OID (snd x) )

noextract
let rec len_of_x509_keyPurposeIDs
  (oids: keyPurposeIDs_oids_t
         { valid_x509_ext_keyPurposeIDs_ingredients oids })
  // (x: x509_keyPurposeIDs_t oids
  //     { valid_x509_ext_keyPurposeIDs_ingredients oids x })
: Tot (len: asn1_value_int32_of_type SEQUENCE
           { v len == length_of_x509_keyPurposeIDs oids })
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  lemma_serialize_x509_keyPurposeIDs_size oids;
  match oids' with
  | [] -> ( len_of_asn1_primitive_TLV #OID (get_x509_keyPurposeIDs oids) )
  | _  -> ( let x = (get_x509_keyPurposeIDs oids) <: x509_keyPurposeIDs_t oids' `tuple2` get_parser_type (parse_asn1_oid_TLV_of oid) in
            lemma_serialize_x509_keyPurposeIDs_size oids';
            len_of_x509_keyPurposeIDs oids' +
            len_of_asn1_primitive_TLV #OID (snd x) )

(*
 * Payload
 *)

open X509.BasicFields.Extension2

unfold inline_for_extraction
let x509_ext_key_usage_payload_t
  (oids: keyPurposeIDs_oids_t)
= inbound_sequence_value_of
  (**) (serialize_x509_keyPurposeIDs oids)

let parse_x509_ext_key_usage_payload
  (oids: keyPurposeIDs_oids_t)
: parser _ (x509_ext_key_usage_payload_t oids)
= x509_ext_key_usage_payload_t oids
  `coerce_parser`
  parse_asn1_sequence_TLV
  (**) (serialize_x509_keyPurposeIDs oids)

let serialize_x509_ext_key_usage_payload
  (oids: keyPurposeIDs_oids_t)
: serializer (parse_x509_ext_key_usage_payload oids)
= coerce_parser_serializer
    (_)
    (serialize_asn1_sequence_TLV
    (**) (serialize_x509_keyPurposeIDs oids))
    ()

noextract inline_for_extraction
let serialize32_x509_ext_key_usage_payload_backwards
  (oids: keyPurposeIDs_oids_t)
: serializer32_backwards (serialize_x509_ext_key_usage_payload oids)
= coerce_serializer32_backwards
    (_)
    (serialize32_asn1_sequence_TLV_backwards
    (**) (serialize32_x509_keyPurposeIDs_backwards oids))
    ()

let lemma_serialize_x509_ext_key_usage_payload_unfold
  (oids: keyPurposeIDs_oids_t
         { valid_x509_ext_keyPurposeIDs_ingredients oids })
  // (x: x509_ext_key_usage_payload_t oids)
: Lemma (
  lemma_serialize_x509_keyPurposeIDs_size oids;
  predicate_serialize_asn1_sequence_TLV_unfold
  (**) (serialize_x509_keyPurposeIDs oids)
  (**) (get_x509_keyPurposeIDs oids)
)
= lemma_serialize_x509_keyPurposeIDs_size oids;
  lemma_serialize_asn1_sequence_TLV_unfold
  (**) (serialize_x509_keyPurposeIDs oids)
  (**) (get_x509_keyPurposeIDs oids)

let lemma_serialize_x509_ext_key_usage_payload_size
  (oids: keyPurposeIDs_oids_t
         { valid_x509_ext_keyPurposeIDs_ingredients oids })
  // (x: x509_ext_key_usage_payload_t oids)
: Lemma (
  lemma_serialize_x509_keyPurposeIDs_size oids;
  predicate_serialize_asn1_sequence_TLV_size
  (**) (serialize_x509_keyPurposeIDs oids)
  (**) (get_x509_keyPurposeIDs oids)
)
= lemma_serialize_x509_keyPurposeIDs_size oids;
  lemma_serialize_asn1_sequence_TLV_size
  (**) (serialize_x509_keyPurposeIDs oids)
  (**) (get_x509_keyPurposeIDs oids)

let length_of_x509_ext_key_usage_payload_unbounded
  (oids: keyPurposeIDs_oids_t
         { valid_x509_ext_keyPurposeIDs_ingredients oids })
: GTot (asn1_TLV_length_of_type SEQUENCE)
= length_of_TLV
    (SEQUENCE)
    (length_of_x509_keyPurposeIDs oids)

let valid_x509_ext_key_usage_payload_ingredients
  (oids: keyPurposeIDs_oids_t)
= valid_x509_ext_keyPurposeIDs_ingredients oids /\
  length_of_x509_ext_key_usage_payload_unbounded oids
  <= asn1_value_length_max_of_type OCTET_STRING

let length_of_x509_ext_key_usage_payload
  (oids: keyPurposeIDs_oids_t
      { valid_x509_ext_key_usage_payload_ingredients oids })
: GTot (l: asn1_value_length_of_type OCTET_STRING
           { l == length_of_x509_ext_key_usage_payload_unbounded oids })
= length_of_TLV
    (SEQUENCE)
    (length_of_x509_keyPurposeIDs oids)

noextract inline_for_extraction
let len_of_x509_ext_key_usage_payload
  (oids: keyPurposeIDs_oids_t
      { valid_x509_ext_key_usage_payload_ingredients oids })
: Tot (len: asn1_value_int32_of_type OCTET_STRING
            { v len == length_of_x509_ext_key_usage_payload oids })
= len_of_TLV
    (SEQUENCE)
    (len_of_x509_keyPurposeIDs oids)

let lemma_serialize_x509_ext_key_usage_payload_size_exact
  (oids: keyPurposeIDs_oids_t
         { valid_x509_ext_key_usage_payload_ingredients oids })
  // (x: x509_ext_key_usage_payload_t oids)
: Lemma (
  lemma_serialize_x509_keyPurposeIDs_size oids;
  length_of_opaque_serialization (serialize_x509_ext_key_usage_payload oids) (get_x509_keyPurposeIDs oids) ==
  length_of_x509_ext_key_usage_payload oids
)
= lemma_serialize_x509_ext_key_usage_payload_unfold oids;
  lemma_serialize_x509_ext_key_usage_payload_size oids;
    lemma_serialize_x509_keyPurposeIDs_size oids

(*
 * Main
 *)

let x509_ext_key_usage_t
  (oids: keyPurposeIDs_oids_t)
= x509_extension_t
  (**) (OID_EXTENDED_KEY_USAGE)
  (**) (serialize_x509_ext_key_usage_payload oids)

let parse_x509_ext_key_usage
  (oids: keyPurposeIDs_oids_t)
: parser parse_x509_extension_kind (x509_ext_key_usage_t oids)
= x509_ext_key_usage_t oids
  `coerce_parser`
  parse_x509_extension
  (**) (OID_EXTENDED_KEY_USAGE)
  (**) (serialize_x509_ext_key_usage_payload oids)

let serialize_x509_ext_key_usage
  (oids: keyPurposeIDs_oids_t)
: serializer (parse_x509_ext_key_usage oids)
= coerce_parser_serializer
    (parse_x509_ext_key_usage oids)
    (serialize_x509_extension
    (**) (OID_EXTENDED_KEY_USAGE)
    (**) (serialize_x509_ext_key_usage_payload oids))
    ()

noextract inline_for_extraction
let serialize32_x509_ext_key_usage_backwards
  (oids: keyPurposeIDs_oids_t)
: serializer32_backwards (serialize_x509_ext_key_usage oids)
= coerce_serializer32_backwards
    (_)
    (serialize32_x509_extension_backwards
    (**) (OID_EXTENDED_KEY_USAGE)
    (**) (serialize32_x509_ext_key_usage_payload_backwards oids))
    ()

let lemma_serialize_x509_ext_key_usage_unfold
  (oids: keyPurposeIDs_oids_t
         { valid_x509_ext_key_usage_payload_ingredients oids })
  (x: x509_ext_key_usage_t oids)
: Lemma ( lemma_serialize_x509_ext_key_usage_payload_size_exact oids;
          predicate_serialize_x509_extension_unfold
          (**) (OID_EXTENDED_KEY_USAGE)
          (**) (serialize_x509_ext_key_usage_payload oids)
          (**) (x) )
= lemma_serialize_x509_ext_key_usage_payload_size_exact oids;
  lemma_serialize_x509_extension_unfold
  (**) (OID_EXTENDED_KEY_USAGE)
  (**) (serialize_x509_ext_key_usage_payload oids)
  (**) (x)

let lemma_serialize_x509_ext_key_usage_size
  (oids: keyPurposeIDs_oids_t)
  (x: x509_ext_key_usage_t oids)
: Lemma ( predicate_serialize_x509_extension_size
          (**) (OID_EXTENDED_KEY_USAGE)
          (**) (serialize_x509_ext_key_usage_payload oids)
          (**) (x) )
= lemma_serialize_x509_extension_size
  (**) (OID_EXTENDED_KEY_USAGE)
  (**) (serialize_x509_ext_key_usage_payload oids)
  (**) (x)

let valid_x509_ext_key_usage_ingredients
  (oids: keyPurposeIDs_oids_t)
  // (kps: x509_keyPurposeIDs_t oids)
: Type0
= valid_x509_ext_key_usage_payload_ingredients oids /\
 (let _ = lemma_serialize_x509_keyPurposeIDs_size oids;
          lemma_serialize_x509_ext_key_usage_payload_size_exact oids in
  length_of_x509_extension_payload_unbounded
    (OID_EXTENDED_KEY_USAGE)
    (serialize_x509_ext_key_usage_payload oids)
    (get_x509_keyPurposeIDs oids <: x509_ext_key_usage_payload_t oids)
    (length_of_x509_ext_key_usage_payload oids)
  <= asn1_value_length_max_of_type (SEQUENCE))

let length_of_x509_ext_key_usage
  (oids: keyPurposeIDs_oids_t
         { valid_x509_ext_key_usage_ingredients oids })
  // (kps: x509_keyPurposeIDs_t oids
  //       { valid_x509_ext_key_usage_ingredients oids kps })
: GTot (asn1_TLV_length_of_type SEQUENCE)
= lemma_serialize_x509_keyPurposeIDs_size oids;
  lemma_serialize_x509_ext_key_usage_payload_size_exact oids;
  length_of_x509_extension
    (OID_EXTENDED_KEY_USAGE)
    (serialize_x509_ext_key_usage_payload oids)
    ((get_x509_keyPurposeIDs oids) <: x509_ext_key_usage_payload_t oids)
    (length_of_x509_ext_key_usage_payload oids)

let len_of_x509_ext_key_usage
  (oids: keyPurposeIDs_oids_t
         { valid_x509_ext_key_usage_ingredients oids })
  // (kps: x509_keyPurposeIDs_t oids
  //       { valid_x509_ext_key_usage_ingredients oids kps })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_x509_ext_key_usage oids })
= lemma_serialize_x509_keyPurposeIDs_size oids;
  lemma_serialize_x509_ext_key_usage_payload_size_exact oids;
  len_of_x509_extension
    (OID_EXTENDED_KEY_USAGE)
    (serialize_x509_ext_key_usage_payload oids)
    (get_x509_keyPurposeIDs oids <: x509_ext_key_usage_payload_t oids)
    (len_of_x509_ext_key_usage_payload oids)

let lemma_serialize_x509_ext_key_usage_size_exact
  (oids: keyPurposeIDs_oids_t
      { valid_x509_ext_key_usage_ingredients oids })
  (x: x509_ext_key_usage_t oids)
: Lemma (
  length_of_opaque_serialization (serialize_x509_ext_key_usage oids) x ==
  length_of_x509_ext_key_usage oids
)
= lemma_x509_keyPurposeIDs_unique oids;
  lemma_serialize_x509_ext_key_usage_payload_size_exact oids;
  lemma_serialize_x509_keyPurposeIDs_size oids;
  lemma_serialize_x509_extension_size_exact
    (OID_EXTENDED_KEY_USAGE)
    (serialize_x509_ext_key_usage_payload oids)
    (x)
    (length_of_x509_ext_key_usage_payload oids)

(* TODO: Need to figure out how to easily prove `valid_x509_ext_key_usage_ingredients` *)

#push-options "--z3rlimit 128"

noextract inline_for_extraction
let x509_get_ext_extendedKeyUsage
  (oids: keyPurposeIDs_oids_t)
  (criticality: datatype_of_asn1_type BOOLEAN
                { let kpIDs: x509_keyPurposeIDs_t oids = get_x509_keyPurposeIDs oids in
                  valid_x509_ext_key_usage_ingredients oids })
: Tot (x509_ext_key_usage_t oids)
=
  let kpIDs: x509_keyPurposeIDs_t oids = get_x509_keyPurposeIDs oids in
  lemma_serialize_x509_keyPurposeIDs_size oids;

  let ext_payload: x509_ext_key_usage_payload_t oids = get_x509_keyPurposeIDs oids in
  lemma_serialize_x509_ext_key_usage_payload_size_exact oids;

  let ext: x509_ext_key_usage_t oids = x509_get_extension
                                         (OID_EXTENDED_KEY_USAGE)
                                         (serialize_x509_ext_key_usage_payload oids)
                                         (ext_payload)
                                         (len_of_x509_ext_key_usage_payload oids)
                                         (criticality)
                                         in

(* return *) ext

#push-options "--fuel 4"

// #push-options "--fuel 4"

// noextract unfold inline_for_extraction
// let oids: keyPurposeIDs_oids_t
// = [@inline_let] let l = [OID_AT_CN; OID_AT_COUNTRY; OID_AT_ORGANIZATION] in
//   assert_norm (valid_keyPurposeIDs l);
//   l

// let ty = x509_keyPurposeIDs_t oids

// let tm: x509_keyPurposeIDs_t oids = get_x509_keyPurposeIDs oids

// let test () =
//   lemma_serialize_x509_keyPurposeIDs_size oids tm;
//   // assert (
//   //   valid_keyPurposeIDs oids /\
//   //   valid_x509_ext_key_usage_payload_ingredients oids tm /\
//   //   valid_x509_ext_key_usage_ingredients oids tm
//   // );
//   let ext = x509_get_ext_extendedKeyUsage oids true in
// ()

(* Helpers to unroll recursively defined types and lemmas *)

let norm_steps_x509_keyPurposeIDs
  (oids_name: string)
: list P.norm_step
= [delta_only [
(* the parameter *)
  oids_name;
(* the type to extract *)
  `%x509_keyPurposeIDs_t;
  `%get_x509_keyPurposeIDs;
  `%x509_ext_key_usage_payload_t;
  `%x509_ext_key_usage_t;
  `%x509_extension_payload_t;
  `%x509_extension_t;
  // `%serialize_x509_ext_key_usage_payload;
  // `%serialize_x509_keyPurposeIDs;
  `%inbound_sequence_value_of;
  `%inbound_envelop_tag_with_value_of;
  (* the Low* implementation to extract *)
  `%serialize32_x509_keyPurposeIDs_backwards;
  `%serialize32_x509_ext_key_usage_payload_backwards;
  `%serialize32_x509_ext_key_usage_backwards;
  `%serialize_x509_keyPurposeIDs_size_spec;
  `%length_of_x509_keyPurposeIDs;
  `%len_of_x509_keyPurposeIDs;
  `%length_of_x509_ext_key_usage;
  `%len_of_x509_ext_key_usage_payload;
  `%length_of_x509_ext_key_usage_payload;
  `%len_of_x509_ext_key_usage;
  `%length_of_x509_ext_key_usage;
  `%x509_get_ext_extendedKeyUsage;
(* the specs and lemmas *)
  `%serialize_x509_keyPurposeIDs_unfold_spec;
  `%serialize_x509_keyPurposeIDs_size_spec;
  `%predicate_serialize_x509_keyPurposeIDs_size_oids;
  `%lemma_serialize_x509_keyPurposeIDs_unfold;
  `%lemma_serialize_x509_keyPurposeIDs_size;
(* list ops *)
  `%FStar.List.Tot.Base.unsnoc;
  `%FStar.List.Tot.Base.splitAt;
  `%FStar.List.Tot.Base.length;
  `%FStar.List.Tot.Base.hd;
  `%fst;
  `%snd;
  `%Mktuple2?._1;
  `%Mktuple2?._2;
(* coerce helpers *)
  // `%coerce_parser;
  // `%coerce_parser_serializer;
  `%coerce_serializer32_backwards;
  ]; primops; zeta; iota]

// NOTE: Use with: [@@postprocess_with (postprocess_x509_keyPurposeIDs `%oids)]
let postprocess_x509_keyPurposeIDs
  (oids_name: string)
  ()
: T.Tac unit
= T.norm (norm_steps_x509_keyPurposeIDs oids_name);
  T.trefl()

let lemma_serialize_x509_keyPurposeIDs_unfold_norm
  (oids: keyPurposeIDs_oids_t)
  // (x: x509_keyPurposeIDs_t oids)
: Lemma (
  P.norm
    (norm_steps_x509_keyPurposeIDs "oids")
    (serialize_x509_keyPurposeIDs_unfold_spec oids)
  ==
    (serialize_x509_keyPurposeIDs_unfold_spec oids)
)
= P.norm_spec
    (norm_steps_x509_keyPurposeIDs "oids")
    (serialize_x509_keyPurposeIDs_unfold_spec oids)

let lemma_serialize_x509_keyPurposeIDs_size_norm
  (oids: keyPurposeIDs_oids_t)
  // (x: x509_keyPurposeIDs_t oids)
: Lemma (
  P.norm
    (norm_steps_x509_keyPurposeIDs "oids")
    (serialize_x509_keyPurposeIDs_size_spec oids)
  ==
    (serialize_x509_keyPurposeIDs_size_spec oids) /\
  P.norm
    (norm_steps_x509_keyPurposeIDs "oids")
    (predicate_serialize_x509_keyPurposeIDs_size_oids oids)
  ==
    (predicate_serialize_x509_keyPurposeIDs_size_oids oids)
)
= P.norm_spec
    (norm_steps_x509_keyPurposeIDs "oids")
    (serialize_x509_keyPurposeIDs_size_spec oids);
  P.norm_spec
    (norm_steps_x509_keyPurposeIDs "oids")
    (predicate_serialize_x509_keyPurposeIDs_size_oids oids)

// noextract unfold inline_for_extraction
// let oids: l: list (datatype_of_asn1_type OID) { valid_keyPurposeIDs l }
// = [@inline_let] let l = [OID_AT_CN; OID_AT_COUNTRY; OID_AT_ORGANIZATION] in
//   assert_norm (valid_keyPurposeIDs l);
//   l

// // [@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
// let ty = P.norm (norm_steps_x509_keyPurposeIDs (`%oids)) (x509_keyPurposeIDs_t oids)

// let test_success
// = let tm: ty = ((OID_AT_CN, OID_AT_COUNTRY), OID_AT_ORGANIZATION) in
// ()

// (* FIXME: Why this one fails? *)
// [@expect_failure]
// let test_fail
// = let ty = P.norm (norm_steps_x509_keyPurposeIDs (`%oids)) (x509_keyPurposeIDs_t oids) in
//   let tm: ty = ((OID_AT_CN, OID_AT_COUNTRY), OID_AT_ORGANIZATION) in
// ()


(* Tests

noextract unfold inline_for_extraction
let oids: l: list (datatype_of_asn1_type OID) { valid_keyPurposeIDs l }
= [@inline_let] let l = [OID_AT_CN; OID_AT_COUNTRY; OID_AT_ORGANIZATION] in
  assert_norm (valid_keyPurposeIDs l);
  l

[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
let exty = (x509_ext_key_usage_t oids)


[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
let test0 =
  assert_norm( valid_keyPurposeIDs oids );
  let kpIDs: x509_keyPurposeIDs_t oids =
    // P.norm
    //     (norm_steps_x509_keyPurposeIDs (`%oids))
        (get_x509_keyPurposeIDs oids) in
  let _ = lemma_serialize_x509_keyPurposeIDs_size_norm oids kpIDs;
          lemma_serialize_x509_keyPurposeIDs_size oids kpIDs in
  // P.norm
  //   (norm_steps_x509_keyPurposeIDs (`%oids))
    (serialize_x509_keyPurposeIDs_size_spec oids kpIDs)

[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
let test1
= assume (
  length_of_opaque_serialization (serialize_x509_keyPurposeIDs oids) (get_x509_keyPurposeIDs oids) ==
  serialize_x509_keyPurposeIDs_size_spec oids (get_x509_keyPurposeIDs oids) /\
  predicate_serialize_x509_keyPurposeIDs_size_oids oids (get_x509_keyPurposeIDs oids)
  );
  lemma_serialize_x509_keyPurposeIDs_size_norm oids (get_x509_keyPurposeIDs oids);
  assert_norm (
  (serialize_x509_keyPurposeIDs_size_spec oids (get_x509_keyPurposeIDs oids))
  == length_of_asn1_primitive_TLV OID_AT_CN +
     length_of_asn1_primitive_TLV OID_AT_COUNTRY +
     length_of_asn1_primitive_TLV OID_AT_ORGANIZATION
  )

// #push-options "--fuel 3"
let test =
  assert_norm( valid_keyPurposeIDs oids );
  assert (
  // let oids: l: list (datatype_of_asn1_type OID) { valid_keyPurposeIDs l } = oids in
  let kpIDs: x509_keyPurposeIDs_t oids
    = //P.norm
      //  (norm_steps_x509_keyPurposeIDs (`%oids))
        (get_x509_keyPurposeIDs oids) in
  let _ = lemma_serialize_x509_keyPurposeIDs_size_norm oids kpIDs;
          lemma_serialize_x509_keyPurposeIDs_size oids kpIDs in
  // P.norm
  //   (norm_steps_x509_keyPurposeIDs (`%oids))
    (serialize_x509_keyPurposeIDs_size_spec oids kpIDs)
  == length_of_asn1_primitive_TLV OID_AT_CN +
     length_of_asn1_primitive_TLV OID_AT_COUNTRY +
     length_of_asn1_primitive_TLV OID_AT_ORGANIZATION /\
    (serialize_x509_keyPurposeIDs_size_spec oids kpIDs)
  <= asn1_value_length_max_of_type SEQUENCE /\
 // (length_of_x509_ext_key_usage_payload_unbounded oids kpIDs
 //  <= asn1_value_length_max_of_type OCTET_STRING) /\
 // (let _ = lemma_serialize_x509_keyPurposeIDs_size oids kpIDs;
 //          lemma_serialize_x509_ext_key_usage_payload_size_exact oids kpIDs in
 //  length_of_x509_extension_payload_unbounded
 //    (OID_EXTENDED_KEY_USAGE)
 //    (serialize_x509_ext_key_usage_payload oids)
 //    (kpIDs)
 //    (length_of_x509_ext_key_usage_payload oids kpIDs)
 //  <= asn1_value_length_max_of_type (SEQUENCE)) /\
  True
)

// let f ()
// = let extm: exty = (x509_get_ext_extendedKeyUsage oids true) in
//   1

// #push-options "--fuel 4"
// let extm: exty
// =
//   lemma_serialize_x509_keyPurposeIDs_size_norm oids tm;
//   lemma_serialize_x509_keyPurposeIDs_size oids tm;
//   x509_get_ext_extendedKeyUsage oids true
// #pop-options

// let length_of_x509_ext_key_usage
//   (oids: keyPurposeIDs_oids_t)
//   (x: x509_ext_key_usage_payload_t oids
//       { serialize_x509_keyPurposeIDs_size_spec oids x
//         <= asn1_value_length_max_of_type SEQUENCE })
// : GTot (asn1_TLV_int32_of_type SEQUENCE)
// = length_of_TLV

// noextract
// let norm_x509_ext_key_usage
//   (oids_str: string)
//   : Tac unit = norm [delta_only [
//   oids_str;
// (* Types *)
//   `%inbound_sequence_value_of;
//   `%inbound_envelop_tag_with_value_of;
//   `%X509.BasicFields.Extension2.x509_extension_t;
//   `%X509.BasicFields.Extension2.x509_extension_payload_t;
//   `%x509_keyPurposeIDs_t;
//   `%x509_ext_key_usage_payload_t;
//   `%x509_ext_key_usage_t;
// (* Low-Level (rec) Serializers *)
//   `%serialize32_x509_keyPurposeIDs_backwards;
//   // `%serialize32_x509_ext_key_usage_payload_backwards;
//   // `%serialize32_x509_ext_key_usage_backwards;
// (* Misc *)
//   `%FStar.List.Tot.Base.unsnoc;
//   `%FStar.List.Tot.Base.splitAt;
//   `%FStar.List.Tot.Base.length;
//   `%FStar.List.Tot.Base.hd;
// ]; primops; zeta; iota]; trefl ()

(*)
let parse_x509_ext_key_usage_payload
  (oids: keyPurposeIDs_oids_t)
= parse_asn1_sequence_TLV
    (OID_EXTENDED_KEY_USAGE
     `serialize_envelop_OID_with`
     serialize_x509_keyPurposeIDs oids)
 ff
let serialize_x509_keyPurposeIDs_sequence_TLV
  (oids: keyPurposeIDs_oids_t)
: serializer (parse_x509_keyPurposeIDs_sequence_TLV oids)
= serialize_asn1_sequence_TLV
    (OID_EXTENDED_KEY_USAGE_PAYLOAD
     `serialize_envelop_OID_with`
     serialize_x509_keyPurposeIDs oids)

let lemma_serialize_x509_keyPurposeIDs_sequence_TLV_unfold
  (oids: keyPurposeIDs_oids_t)
= lemma_serialize_asn1_sequence_TLV_unfold
    (OID_EXTENDED_KEY_USAGE_PAYLOAD
     `serialize_envelop_OID_with`
     serialize_x509_keyPurposeIDs oids)

let lemma_serialize_x509_keyPurposeIDs_sequence_TLV_size
  (oids: keyPurposeIDs_oids_t)
= lemma_serialize_asn1_sequence_TLV_size
    (OID_EXTENDED_KEY_USAGE_PAYLOAD
     `serialize_envelop_OID_with`
     serialize_x509_keyPurposeIDs oids)

(**)
(* 1 *)
let parse_x509_keyPurposeIDs_1
  (oid: datatype_of_asn1_type OID)
: parser _ _
= parse_asn1_oid_TLV_of oid

let serialize_x509_keyPurposeIDs_1
  (oid: datatype_of_asn1_type OID)
: serializer (parse_x509_keyPurposeIDs_1 oid)
= serialize_asn1_oid_TLV_of oid

let lemma_serialize_x509_keyPurposeIDs_1_unfold
  (oid: datatype_of_asn1_type OID)
= lemma_serialize_asn1_oid_TLV_unfold oid

let lemma_serialize_x509_keyPurposeIDs_1_size
  (oid: datatype_of_asn1_type OID)
= lemma_serialize_asn1_oid_TLV_size oid

let parse_x509_keyPurposeIDs_1_sequence_TLV
  (oid: datatype_of_asn1_type OID)
= parse_asn1_sequence_TLV
    (OID_EXTENDED_KEY_USAGE_PAYLOAD
     `serialize_envelop_OID_with`
     serialize_x509_keyPurposeIDs_1 oid)

let serialize_x509_keyPurposeIDs_1_sequence_TLV
  (oid: datatype_of_asn1_type OID)
: serializer (parse_x509_keyPurposeIDs_1_sequence_TLV oid)
= serialize_asn1_sequence_TLV
    (OID_EXTENDED_KEY_USAGE_PAYLOAD
     `serialize_envelop_OID_with`
     serialize_x509_keyPurposeIDs_1 oid)

let lemma_serialize_x509_keyPurposeIDs_1_sequence_TLV_unfold
  (oid: datatype_of_asn1_type OID)
= lemma_serialize_asn1_sequence_TLV_unfold
    (OID_EXTENDED_KEY_USAGE_PAYLOAD
     `serialize_envelop_OID_with`
     serialize_x509_keyPurposeIDs_1 oid)

let lemma_serialize_x509_keyPurposeIDs_1_sequence_TLV_size
  (oid: datatype_of_asn1_type OID)
= lemma_serialize_asn1_sequence_TLV_size
    (OID_EXTENDED_KEY_USAGE_PAYLOAD
     `serialize_envelop_OID_with`
     serialize_x509_keyPurposeIDs_1 oid)

open ASN1.Low
let x509_keyPurposeIDs_1_inbound
  (oid: datatype_of_asn1_type OID)
= inbound_sequence_value_of (serialize_x509_keyPurposeIDs_1 oid)

let x509_keyPurposeIDs_t_inbound
  (oids: keyPurposeIDs_oids_t)
= inbound_sequence_value_of (serialize_x509_keyPurposeIDs oids)

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

module B32 = FStar.Bytes

module IB = LowStar.ImmutableBuffer
module CB = LowStar.ConstBuffer

module G = FStar.Ghost
open FStar.Integers

// #push-options "--z3rlimit 16"
// let rec length_of_x509_keyPurposeIDs
//   (oids: keyPurposeIDs_oids_t)
//   (x: x509_keyPurposeIDs_t oids)
// : GTot (l: nat {l == Seq.length (serialize (serialize_x509_keyPurposeIDs oids) x)})
//   (decreases (List.length oids))
// = lemma_serialize_x509_keyPurposeIDs_unfold oids x;
//   lemma_serialize_x509_keyPurposeIDs_size   oids x;
//   let oids', oid = List.Tot.Base.unsnoc oids in
//   List.Tot.Properties.lemma_unsnoc_length oids;
//   match oids' with
//   | [] -> ( let x = x <: datatype_of_asn1_type OID in
//             length_of_asn1_primitive_TLV x  )
//   | _  -> ( let x = x <: x509_keyPurposeIDs_t oids' `tuple2` get_parser_type (parse_asn1_oid_TLV_of oid) in
//             length_of_x509_keyPurposeIDs oids' (fst x) +
//             length_of_asn1_primitive_TLV #OID (snd x) )

(* NOTE: Expect all instantiations of it be marked as `inline_for_extraction` evaluated at extract time *)
(* TODO: Check actual extraction behavior. *)
noextract
let rec serialize32_x509_keyPurposeIDs_backwards
  (oids: keyPurposeIDs_oids_t)
: Tot (serializer32_backwards (serialize_x509_keyPurposeIDs oids))
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( serialize32_asn1_oid_TLV_of_backwards oid )
  | _  -> ( serialize32_x509_keyPurposeIDs_backwards oids'
            `serialize32_nondep_then_backwards`
            serialize32_asn1_oid_TLV_of_backwards oid )

noextract
let serialize32_x509_keyPurposeIDs_sequence_TLV_backwards
  (oids: keyPurposeIDs_oids_t!)
: serializer32_backwards (serialize_x509_keyPurposeIDs_sequence_TLV oids)
= serialize32_asn1_sequence_TLV_backwards
  (* s32 *) (OID_EXTENDED_KEY_USAGE_PAYLOAD
             `serialize32_envelop_OID_with_backwards`
             serialize32_x509_keyPurposeIDs_backwards oids)
