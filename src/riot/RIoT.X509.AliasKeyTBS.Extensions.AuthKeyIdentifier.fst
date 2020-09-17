module RIoT.X509.AliasKeyTBS.Extensions.AuthKeyIdentifier

open ASN1.Spec
open ASN1.Low
open X509
open X509.BasicFields.Extension2
open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 64 --fuel 0 --ifuel 0"

(* extValue payload *)

let aliasKeyTBS_extensions_authKeyID_extValue_payload_t: Type0
= x509_authKeyID_keyIdentifier_t

let parse_aliasKeyTBS_extensions_authKeyID_extValue_payload
: parser _ aliasKeyTBS_extensions_authKeyID_extValue_payload_t
= parse_x509_authKeyID_keyIdentifier

let serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload
: serializer parse_aliasKeyTBS_extensions_authKeyID_extValue_payload
= serialize_x509_authKeyID_keyIdentifier

let serialize32_aliasKeyTBS_extensions_authKeyID_extValue_payload_backwards
: serializer32_backwards serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload
= serialize32_x509_authKeyID_keyIdentifier_backwards

let lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload_unfold
  (x: aliasKeyTBS_extensions_authKeyID_extValue_payload_t)
: Lemma (
  serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload `serialize` x ==
  serialize_x509_authKeyID_keyIdentifier `serialize` x
)
= ()

let length_of_aliasKeyTBS_extensions_authKeyID_extValue_payload
  (keyID: datatype_of_asn1_type OCTET_STRING
          { valid_authKeyID_keyIdentifier_ingredients keyID })
: GTot (nat)
= length_of_x509_authKeyID_keyIdentifier keyID

let valid_aliasKeyTBS_extensions_authKeyID_extValue_payload_ingredients
  (keyID: datatype_of_asn1_type OCTET_STRING)
: Type0
= valid_authKeyID_keyIdentifier_ingredients keyID /\
  length_of_aliasKeyTBS_extensions_authKeyID_extValue_payload keyID
  <= asn1_value_length_max_of_type SEQUENCE

let len_of_aliasKeyTBS_extensions_authKeyID_extValue_payload
  (keyID: datatype_of_asn1_type OCTET_STRING
          { valid_aliasKeyTBS_extensions_authKeyID_extValue_payload_ingredients keyID })
: Tot (len: asn1_value_int32_of_type SEQUENCE
            { v len == length_of_aliasKeyTBS_extensions_authKeyID_extValue_payload keyID })
= len_of_x509_authKeyID_keyIdentifier keyID

let lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload_size
  (x: aliasKeyTBS_extensions_authKeyID_extValue_payload_t
      { valid_aliasKeyTBS_extensions_authKeyID_extValue_payload_ingredients x })
: Lemma (
  length_of_opaque_serialization serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload x ==
  length_of_opaque_serialization serialize_x509_authKeyID_keyIdentifier x /\
  length_of_opaque_serialization serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload x ==
  length_of_aliasKeyTBS_extensions_authKeyID_extValue_payload x
)
= lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload_unfold x;
  lemma_serialize_x509_authKeyID_keyIdentifier_size_exact x

(* extValue *)

let aliasKeyTBS_extensions_authKeyID_extValue_t
= inbound_sequence_value_of
  (**) (serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload)

let parse_aliasKeyTBS_extensions_authKeyID_extValue
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) aliasKeyTBS_extensions_authKeyID_extValue_t
= aliasKeyTBS_extensions_authKeyID_extValue_t
  `coerce_parser`
  parse_asn1_sequence_TLV
  (**) (serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload)

let serialize_aliasKeyTBS_extensions_authKeyID_extValue
: serializer parse_aliasKeyTBS_extensions_authKeyID_extValue
= coerce_parser_serializer
    (parse_aliasKeyTBS_extensions_authKeyID_extValue)
    (serialize_asn1_sequence_TLV
    (**) (serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload))
    ()

let serialize32_aliasKeyTBS_extensions_authKeyID_extValue_backwards
: serializer32_backwards serialize_aliasKeyTBS_extensions_authKeyID_extValue
= coerce_serializer32_backwards
    (serialize_aliasKeyTBS_extensions_authKeyID_extValue)
    (serialize32_asn1_sequence_TLV_backwards
    (**) (serialize32_aliasKeyTBS_extensions_authKeyID_extValue_payload_backwards))
    ()

let lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_unfold
  (x: aliasKeyTBS_extensions_authKeyID_extValue_t)
: Lemma (
  predicate_serialize_asn1_sequence_TLV_unfold
    (serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload)
    (x)
)
= lemma_serialize_asn1_sequence_TLV_unfold
    (serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload)
    (x)

let lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_size
  (x: aliasKeyTBS_extensions_authKeyID_extValue_t)
: Lemma (
  predicate_serialize_asn1_sequence_TLV_size
    (serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload)
    (x)
)
= lemma_serialize_asn1_sequence_TLV_size
    (serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload)
    (x)

let valid_aliasKeyTBS_extensions_authKeyID_extValue_ingredients
  (keyID: datatype_of_asn1_type OCTET_STRING)
= valid_aliasKeyTBS_extensions_authKeyID_extValue_payload_ingredients keyID /\
  length_of_TLV
    (SEQUENCE)
    (length_of_aliasKeyTBS_extensions_authKeyID_extValue_payload keyID)
  <= asn1_value_length_max_of_type OCTET_STRING

let length_of_aliasKeyTBS_extensions_authKeyID_extValue
  (keyID: datatype_of_asn1_type OCTET_STRING
          { valid_aliasKeyTBS_extensions_authKeyID_extValue_ingredients keyID })
: GTot (asn1_value_length_of_type OCTET_STRING)
= length_of_TLV
    (SEQUENCE)
    (length_of_aliasKeyTBS_extensions_authKeyID_extValue_payload keyID)

let len_of_aliasKeyTBS_extensions_authKeyID_extValue
  (keyID: datatype_of_asn1_type OCTET_STRING
          { valid_aliasKeyTBS_extensions_authKeyID_extValue_ingredients keyID })
: Tot (len: asn1_value_int32_of_type OCTET_STRING
            { v len == length_of_aliasKeyTBS_extensions_authKeyID_extValue keyID })
= len_of_TLV
    (SEQUENCE)
    (len_of_aliasKeyTBS_extensions_authKeyID_extValue_payload keyID)

let lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_size_exact
  (x: aliasKeyTBS_extensions_authKeyID_extValue_t
      { valid_aliasKeyTBS_extensions_authKeyID_extValue_ingredients x })
: Lemma (
  length_of_opaque_serialization serialize_aliasKeyTBS_extensions_authKeyID_extValue x ==
  length_of_aliasKeyTBS_extensions_authKeyID_extValue x
)
= lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_size x;
    lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload_size x

let x509_get_aliasKeyTBS_extensions_authKeyID_extValue
  (keyID: datatype_of_asn1_type OCTET_STRING
          { valid_aliasKeyTBS_extensions_authKeyID_extValue_ingredients keyID })
: Tot (aliasKeyTBS_extensions_authKeyID_extValue_t)
= (* Prf *) Classical.forall_intro lemma_serialize_x509_authKeyID_keyIdentifier_size_exact;
  x509_get_authKeyID_keyIdentifier keyID

(* ext *)

let aliasKeyTBS_extensions_authKeyID_t: Type
= x509_extension_t
  (**) (OID_AUTHORITY_KEY_IDENTIFIER)
  (**) (serialize_aliasKeyTBS_extensions_authKeyID_extValue)

let parse_aliasKeyTBS_extensions_authKeyID
// : parser _ aliasKeyTBS_extensions_authKeyID_t
= aliasKeyTBS_extensions_authKeyID_t
  `coerce_parser`
  parse_x509_extension
  (**) (OID_AUTHORITY_KEY_IDENTIFIER)
  (**) (serialize_aliasKeyTBS_extensions_authKeyID_extValue)

let serialize_aliasKeyTBS_extensions_authKeyID
: serializer parse_aliasKeyTBS_extensions_authKeyID
= coerce_parser_serializer
    (parse_aliasKeyTBS_extensions_authKeyID)
    (serialize_x509_extension
    (**) (OID_AUTHORITY_KEY_IDENTIFIER)
    (**) (serialize_aliasKeyTBS_extensions_authKeyID_extValue))
    ()

noextract inline_for_extraction
let serialize32_aliasKeyTBS_extensions_authKeyID_backwards
: serializer32_backwards serialize_aliasKeyTBS_extensions_authKeyID
= coerce_serializer32_backwards
    (serialize_aliasKeyTBS_extensions_authKeyID)
    (serialize32_x509_extension_backwards
    (**) (OID_AUTHORITY_KEY_IDENTIFIER)
    (**) (serialize32_aliasKeyTBS_extensions_authKeyID_extValue_backwards))
    ()

let lemma_serialize_aliasKeyTBS_extensions_authKeyID_unfold
  (x: aliasKeyTBS_extensions_authKeyID_t)
: Lemma (
  predicate_serialize_x509_extension_unfold
    (**) (OID_AUTHORITY_KEY_IDENTIFIER)
    (**) (serialize_aliasKeyTBS_extensions_authKeyID_extValue)
    (**) (x)
)
= lemma_serialize_x509_extension_unfold
    (**) (OID_AUTHORITY_KEY_IDENTIFIER)
    (**) (serialize_aliasKeyTBS_extensions_authKeyID_extValue)
    (**) (x)

let lemma_serialize_aliasKeyTBS_extensions_authKeyID_size
  (x: aliasKeyTBS_extensions_authKeyID_t)
: Lemma (
  predicate_serialize_x509_extension_size
    (**) (OID_AUTHORITY_KEY_IDENTIFIER)
    (**) (serialize_aliasKeyTBS_extensions_authKeyID_extValue)
    (**) (x)
)
= lemma_serialize_x509_extension_size
    (**) (OID_AUTHORITY_KEY_IDENTIFIER)
    (**) (serialize_aliasKeyTBS_extensions_authKeyID_extValue)
    (**) (x)

let valid_aliasKeyTBS_extensions_authKeyID_ingredients
  (keyID: datatype_of_asn1_type OCTET_STRING)
: Type0
= valid_aliasKeyTBS_extensions_authKeyID_extValue_ingredients keyID /\
  (let _ = lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload_size keyID;
           lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_size_exact (x509_get_aliasKeyTBS_extensions_authKeyID_extValue keyID) in
   length_of_x509_extension_payload_unbounded
     (OID_AUTHORITY_KEY_IDENTIFIER)
     (serialize_aliasKeyTBS_extensions_authKeyID_extValue)
     (x509_get_aliasKeyTBS_extensions_authKeyID_extValue keyID)
     (length_of_aliasKeyTBS_extensions_authKeyID_extValue (x509_get_aliasKeyTBS_extensions_authKeyID_extValue keyID))
   <= asn1_value_length_max_of_type (SEQUENCE))

let length_of_aliasKeyTBS_extensions_authKeyID
  (keyID: datatype_of_asn1_type OCTET_STRING
          { valid_aliasKeyTBS_extensions_authKeyID_ingredients keyID })
: GTot (asn1_TLV_length_of_type SEQUENCE)
= lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload_size keyID;
  lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_size_exact (x509_get_aliasKeyTBS_extensions_authKeyID_extValue keyID);
  length_of_x509_extension
    (OID_AUTHORITY_KEY_IDENTIFIER)
    (serialize_aliasKeyTBS_extensions_authKeyID_extValue)
    (x509_get_aliasKeyTBS_extensions_authKeyID_extValue keyID)
    (length_of_aliasKeyTBS_extensions_authKeyID_extValue (x509_get_aliasKeyTBS_extensions_authKeyID_extValue keyID))

let len_of_aliasKeyTBS_extensions_authKeyID
  (keyID: datatype_of_asn1_type OCTET_STRING
          { valid_aliasKeyTBS_extensions_authKeyID_ingredients keyID })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_aliasKeyTBS_extensions_authKeyID keyID })
= lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload_size keyID;
  lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_size_exact (x509_get_aliasKeyTBS_extensions_authKeyID_extValue keyID);
  len_of_x509_extension
    (OID_AUTHORITY_KEY_IDENTIFIER)
    (Ghost.hide serialize_aliasKeyTBS_extensions_authKeyID_extValue)
    (x509_get_aliasKeyTBS_extensions_authKeyID_extValue keyID)
    (len_of_aliasKeyTBS_extensions_authKeyID_extValue (x509_get_aliasKeyTBS_extensions_authKeyID_extValue keyID))

let lemma_serialize_aliasKeyTBS_extensions_authKeyID_size_exact
  (ext: aliasKeyTBS_extensions_authKeyID_t
        { valid_aliasKeyTBS_extensions_authKeyID_ingredients (snd ext) })
: Lemma (
  length_of_opaque_serialization serialize_aliasKeyTBS_extensions_authKeyID ext ==
  length_of_aliasKeyTBS_extensions_authKeyID (snd ext)
)
= lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_size_exact (snd ext);
  lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload_size (snd ext <: aliasKeyTBS_extensions_authKeyID_extValue_t);
  lemma_serialize_x509_extension_size_exact
    (OID_AUTHORITY_KEY_IDENTIFIER)
    (serialize_aliasKeyTBS_extensions_authKeyID_extValue)
    (ext)
    (length_of_aliasKeyTBS_extensions_authKeyID_extValue (snd ext))

let x509_get_aliasKeyTBS_extensions_authKeyID
  (criticality: datatype_of_asn1_type BOOLEAN)
  (keyID: datatype_of_asn1_type OCTET_STRING
          { valid_aliasKeyTBS_extensions_authKeyID_ingredients keyID })
: Tot (aliasKeyTBS_extensions_authKeyID_t)
= let extValue_payload: aliasKeyTBS_extensions_authKeyID_extValue_payload_t = keyID in
  (* Prf *) lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_payload_size extValue_payload;

  let extValue: aliasKeyTBS_extensions_authKeyID_extValue_t = extValue_payload in
  (* Prf *) lemma_serialize_aliasKeyTBS_extensions_authKeyID_extValue_size_exact extValue;

  let ext: aliasKeyTBS_extensions_authKeyID_t = aliasKeyTBS_extensions_authKeyID_t
                                     `coerce`
                                     x509_get_extension
                                       (OID_AUTHORITY_KEY_IDENTIFIER)
                                       (serialize_aliasKeyTBS_extensions_authKeyID_extValue)
                                       (extValue)
                                       (len_of_aliasKeyTBS_extensions_authKeyID_extValue keyID)
                                       (criticality)
                                       in

(* return *) ext
