module RIoT.X509.AliasKeyTBS.Extensions.ExtendedKeyUsage

open ASN1.Spec
open ASN1.Low
open X509
open FStar.Integers

module B32 = FStar.Bytes
module T = FStar.Tactics
module P = FStar.Pervasives

(* 2 fuels for the recursively defined 1-oid extendedKeyUsage *)
#set-options "--z3rlimit 64 --fuel 2 --ifuel 0"

noextract inline_for_extraction
let aliasKeyCrt_extendedKeyUsage_oids
: l: keyPurposeIDs_oids_t
     { valid_x509_ext_key_usage_ingredients l }
= [@inline_let]
  let l = [OID_CLIENT_AUTH] in
  assert_norm (  valid_keyPurposeIDs l  );
  // lemma_serialize_x509_keyPurposeIDs_size_norm l;
  lemma_serialize_x509_keyPurposeIDs_size l;
  l

[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%aliasKeyCrt_extendedKeyUsage_oids))]
let aliasKeyTBS_extensions_extendedKeyUsage_t: Type
= x509_ext_key_usage_t aliasKeyCrt_extendedKeyUsage_oids

let lemma_aliasKeyTBS_extensions_extendedKeyUsage_norm ()
: Lemma (
  aliasKeyTBS_extensions_extendedKeyUsage_t == x509_ext_key_usage_t aliasKeyCrt_extendedKeyUsage_oids
)
=
  // P.norm_spec
  //   (norm_steps_x509_keyPurposeIDs (`%aliasKeyCrt_extendedKeyUsage_oids))
  //   (x509_ext_key_usage_t aliasKeyCrt_extendedKeyUsage_oids)
  assert ( aliasKeyTBS_extensions_extendedKeyUsage_t == x509_ext_key_usage_t aliasKeyCrt_extendedKeyUsage_oids )
  by ( postprocess_x509_keyPurposeIDs (`%aliasKeyCrt_extendedKeyUsage_oids) () )

let parse_aliasKeyTBS_extensions_extendedKeyUsage
: parser X509.BasicFields.Extension2.parse_x509_extension_kind aliasKeyTBS_extensions_extendedKeyUsage_t
= lemma_aliasKeyTBS_extensions_extendedKeyUsage_norm ();
  aliasKeyTBS_extensions_extendedKeyUsage_t
  `coerce_parser`
  parse_x509_ext_key_usage aliasKeyCrt_extendedKeyUsage_oids

let serialize_aliasKeyTBS_extensions_extendedKeyUsage
: serializer parse_aliasKeyTBS_extensions_extendedKeyUsage
= coerce_parser_serializer
    (parse_aliasKeyTBS_extensions_extendedKeyUsage)
    (serialize_x509_ext_key_usage aliasKeyCrt_extendedKeyUsage_oids)
    (lemma_aliasKeyTBS_extensions_extendedKeyUsage_norm ())

[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%aliasKeyCrt_extendedKeyUsage_oids))]
let serialize32_aliasKeyTBS_extensions_extendedKeyUsage_backwards
: serializer32_backwards serialize_aliasKeyTBS_extensions_extendedKeyUsage
= coerce_serializer32_backwards
    (serialize_aliasKeyTBS_extensions_extendedKeyUsage)
    (serialize32_x509_ext_key_usage_backwards aliasKeyCrt_extendedKeyUsage_oids)
    (lemma_aliasKeyTBS_extensions_extendedKeyUsage_norm ())

#push-options "--z3rlimit 256"
let length_of_aliasKeyTBS_extensions_extendedKeyUsage ()
: GTot (l: asn1_TLV_length_of_type SEQUENCE
           { l == 24 })
= length_of_x509_ext_key_usage aliasKeyCrt_extendedKeyUsage_oids
#pop-options

noextract inline_for_extraction unfold
[@@ "opaque_to_smt"; T.postprocess_with (postprocess_x509_keyPurposeIDs (`%aliasKeyCrt_extendedKeyUsage_oids))]
let len_of_aliasKeyTBS_extensions_extendedKeyUsage ()
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_aliasKeyTBS_extensions_extendedKeyUsage () })
// (* FIXME: *) = len_of_x509_ext_key_usage aliasKeyCrt_extendedKeyUsage_oids
= 24ul

let lemma_serialize_aliasKeyTBS_extensions_extendedKeyUsage_size_exact
  (x: aliasKeyTBS_extensions_extendedKeyUsage_t)
: Lemma (
  lemma_aliasKeyTBS_extensions_extendedKeyUsage_norm ();
  length_of_opaque_serialization
    serialize_aliasKeyTBS_extensions_extendedKeyUsage
    x ==
  length_of_aliasKeyTBS_extensions_extendedKeyUsage ()
)
= lemma_aliasKeyTBS_extensions_extendedKeyUsage_norm ();
  lemma_x509_keyPurposeIDs_unique aliasKeyCrt_extendedKeyUsage_oids;
  lemma_serialize_x509_ext_key_usage_size_exact
    (aliasKeyCrt_extendedKeyUsage_oids)
    (x509_ext_key_usage_t aliasKeyCrt_extendedKeyUsage_oids
     `coerce`
     x)

[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%aliasKeyCrt_extendedKeyUsage_oids))]
let x509_get_aliasKeyTBS_extensions_extendedKeyUsage
  (criticality: datatype_of_asn1_type BOOLEAN)
: Tot (aliasKeyTBS_extensions_extendedKeyUsage_t)
= lemma_aliasKeyTBS_extensions_extendedKeyUsage_norm ();
  aliasKeyTBS_extensions_extendedKeyUsage_t
  `coerce`
  x509_get_ext_extendedKeyUsage
    aliasKeyCrt_extendedKeyUsage_oids
    criticality
