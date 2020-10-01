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

(*
 * AR: TODO: this module has some scope for improvements
             it's hard to write an interface to hide defns, since a tactic requires those defns, I think *)

#set-options "--z3rlimit 32 --fuel 2 --ifuel 0"

(*
 * KeyPurposeIDs
 *)

let lemma_x509_keyPurposeIDs_unique oids
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

let rec get_x509_keyPurposeIDs oids
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( oid )
  | _  -> ( (get_x509_keyPurposeIDs oids', oid)
             <: x509_keyPurposeIDs_t oids'
                `tuple2`
                get_parser_type (parse_asn1_oid_TLV_of oid) )

let rec parse_x509_keyPurposeIDs_kind oids
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( get_parser_kind (parse_asn1_oid_TLV_of oid) )
  | _  -> ( parse_x509_keyPurposeIDs_kind oids'
            `and_then_kind`
            get_parser_kind (parse_asn1_oid_TLV_of oid) )

let rec parse_x509_keyPurposeIDs oids
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( parse_asn1_oid_TLV_of oid )
  | _  -> ( parse_x509_keyPurposeIDs oids'
            `nondep_then`
            parse_asn1_oid_TLV_of oid )

let rec serialize_x509_keyPurposeIDs oids
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( serialize_asn1_oid_TLV_of oid )
  | _  -> ( serialize_x509_keyPurposeIDs oids'
            `serialize_nondep_then`
            serialize_asn1_oid_TLV_of oid )

let rec serialize32_x509_keyPurposeIDs_backwards oids
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( serialize32_asn1_oid_TLV_of_backwards oid )
  | _  -> ( serialize32_x509_keyPurposeIDs_backwards oids'
            `serialize32_nondep_then_backwards`
            serialize32_asn1_oid_TLV_of_backwards oid )

let rec lemma_serialize_x509_keyPurposeIDs_unfold oids
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

let rec lemma_serialize_x509_keyPurposeIDs_size oids
= lemma_serialize_x509_keyPurposeIDs_unfold oids;
  let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( lemma_serialize_asn1_oid_TLV_of_size (get_x509_keyPurposeIDs oids) (get_x509_keyPurposeIDs oids) )
  | _  -> ( let x = (get_x509_keyPurposeIDs oids) <: x509_keyPurposeIDs_t oids' `tuple2` get_parser_type (parse_asn1_oid_TLV_of oid) in
            lemma_serialize_asn1_oid_TLV_of_size (snd x) (snd x);
            lemma_serialize_x509_keyPurposeIDs_unfold oids';
            lemma_serialize_x509_keyPurposeIDs_size   oids' )

(*
 * Payload
 *)

open X509.BasicFields.Extension2

let serialize32_x509_ext_key_usage_payload_backwards oids
= coerce_serializer32_backwards
    (_)
    (serialize32_asn1_sequence_TLV_backwards
    (**) (serialize32_x509_keyPurposeIDs_backwards oids))
    ()

let lemma_serialize_x509_ext_key_usage_payload_unfold oids
= lemma_serialize_x509_keyPurposeIDs_size oids;
  lemma_serialize_asn1_sequence_TLV_unfold
  (**) (serialize_x509_keyPurposeIDs oids)
  (**) (get_x509_keyPurposeIDs oids)

let lemma_serialize_x509_ext_key_usage_payload_size oids
= lemma_serialize_x509_keyPurposeIDs_size oids;
  lemma_serialize_asn1_sequence_TLV_size
  (**) (serialize_x509_keyPurposeIDs oids)
  (**) (get_x509_keyPurposeIDs oids)

let lemma_serialize_x509_ext_key_usage_payload_size_exact oids
= lemma_serialize_x509_ext_key_usage_payload_unfold oids;
  lemma_serialize_x509_ext_key_usage_payload_size oids;
    lemma_serialize_x509_keyPurposeIDs_size oids

(*
 * Main
 *)

let serialize32_x509_ext_key_usage_backwards oids
= coerce_serializer32_backwards
    (_)
    (serialize32_x509_extension_backwards
    (**) (OID_EXTENDED_KEY_USAGE)
    (**) (serialize32_x509_ext_key_usage_payload_backwards oids))
    ()

let lemma_serialize_x509_ext_key_usage_unfold oids x
= lemma_serialize_x509_ext_key_usage_payload_size_exact oids;
  lemma_serialize_x509_extension_unfold
  (**) (OID_EXTENDED_KEY_USAGE)
  (**) (serialize_x509_ext_key_usage_payload oids)
  (**) (x)

let lemma_serialize_x509_ext_key_usage_size oids x
= lemma_serialize_x509_extension_size
  (**) (OID_EXTENDED_KEY_USAGE)
  (**) (serialize_x509_ext_key_usage_payload oids)
  (**) (x)

let lemma_serialize_x509_ext_key_usage_size_exact oids x
= lemma_x509_keyPurposeIDs_unique oids;
  lemma_serialize_x509_ext_key_usage_payload_size_exact oids;
  lemma_serialize_x509_keyPurposeIDs_size oids;
  lemma_serialize_x509_extension_size_exact
    (OID_EXTENDED_KEY_USAGE)
    (serialize_x509_ext_key_usage_payload oids)
    (x)
    (length_of_x509_ext_key_usage_payload oids)

(* TODO: Need to figure out how to easily prove `valid_x509_ext_key_usage_ingredients` *)

let lemma_serialize_x509_keyPurposeIDs_unfold_norm oids
= P.norm_spec
    (norm_steps_x509_keyPurposeIDs "oids")
    (serialize_x509_keyPurposeIDs_unfold_spec oids)

let lemma_serialize_x509_keyPurposeIDs_size_norm oids
= P.norm_spec
    (norm_steps_x509_keyPurposeIDs "oids")
    (serialize_x509_keyPurposeIDs_size_spec oids);
  // P.norm_spec
  //   (norm_steps_x509_keyPurposeIDs "oids")
  //   (length_of_x509_keyPurposeIDs oids);
  P.norm_spec
    (norm_steps_x509_keyPurposeIDs "oids")
    (predicate_serialize_x509_keyPurposeIDs_size_oids oids)

let lemma_length_of_x509_keyPurposeIDs_norm oids
=
  P.norm_spec
    (norm_steps_x509_keyPurposeIDs "oids")
    (length_of_x509_keyPurposeIDs oids)

