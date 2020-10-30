module RIoT.X509.AliasKeyTBS.Extensions.BasicConstraints

open ASN1.Spec
open ASN1.Low
open X509
open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 64 --fuel 0 --ifuel 0"

noextract inline_for_extraction
let aliasKeyTBS_extensions_basicConstraints_isCA: bool = false

let aliasKeyTBS_extensions_basicConstraints_t: Type
= x509_basicConstraints_t aliasKeyTBS_extensions_basicConstraints_isCA

let parse_aliasKeyTBS_extensions_basicConstraints
// : parser parse_x509_extension_kind aliasKeyTBS_extensions_basicConstraints_t
= aliasKeyTBS_extensions_basicConstraints_t
  `coerce_parser`
  parse_x509_basicConstraints aliasKeyTBS_extensions_basicConstraints_isCA

let serialize_aliasKeyTBS_extensions_basicConstraints
: serializer parse_aliasKeyTBS_extensions_basicConstraints
= coerce_parser_serializer
    (parse_aliasKeyTBS_extensions_basicConstraints)
    (serialize_x509_basicConstraints aliasKeyTBS_extensions_basicConstraints_isCA)
    ()

//noextract inline_for_extraction
let serialize32_aliasKeyTBS_extensions_basicConstraints_backwards
: serializer32_backwards serialize_aliasKeyTBS_extensions_basicConstraints
= coerce_serializer32_backwards
    (serialize_aliasKeyTBS_extensions_basicConstraints)
    (serialize32_x509_basicConstraints_backwards aliasKeyTBS_extensions_basicConstraints_isCA)
    ()

let length_of_aliasKeyTBS_extensions_basicConstraints ()
: GTot (asn1_TLV_length_of_type SEQUENCE)
= length_of_x509_basicConstraints aliasKeyTBS_extensions_basicConstraints_isCA

noextract inline_for_extraction unfold
[@@ "opaque_to_smt"]
let len_of_aliasKeyTBS_extensions_basicConstraints ()
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_aliasKeyTBS_extensions_basicConstraints () })
= len_of_x509_basicConstraints aliasKeyTBS_extensions_basicConstraints_isCA

let lemma_serialize_aliasKeyTBS_extensions_basicConstraints_size_exact
  (x: aliasKeyTBS_extensions_basicConstraints_t)
: Lemma (
  length_of_opaque_serialization serialize_aliasKeyTBS_extensions_basicConstraints x
  == length_of_aliasKeyTBS_extensions_basicConstraints ()
)
= lemma_serialize_x509_basicConstraints_size_exact
    (aliasKeyTBS_extensions_basicConstraints_isCA)
    (x)

let x509_get_aliasKeyTBS_extensions_basicConstraints
  (criticality: datatype_of_asn1_type BOOLEAN)
: Tot (aliasKeyTBS_extensions_basicConstraints_t)
= x509_get_basicConstraints_isNotCA
    (aliasKeyTBS_extensions_basicConstraints_isCA)
    (criticality)
