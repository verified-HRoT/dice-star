module L0.X509.DeviceIDCRI.Attributes

open ASN1.Spec
open ASN1.Low
open X509
open FStar.Integers

module B32 = FStar.Bytes

open LowParse.Spec.SeqBytes.Base
open LowParse.Spec.Bytes

(*
 *   {
 *     ...
 *     attributes    [0] Attributes{{ CRIAttributes }}
 *     ...
 *   }
 *
 *   Attributes { ATTRIBUTE:IOSet } ::= SET OF Attribute{{ IOSet }}
 *
 *    CRIAttributes  ATTRIBUTE  ::= {
 *         ... -- add any locally defined attributes here -- }
 *
 *    Attribute { ATTRIBUTE:IOSet } ::= SEQUENCE {
 *         type   ATTRIBUTE.&id({IOSet}),
 *         values SET SIZE(1..MAX) OF ATTRIBUTE.&Type({IOSet}{@type})
 *    }
 *
 *
 *    RFC 2985 PKCS #9 5.4.2:
 *
 *    extensionRequest ATTRIBUTE ::= {
 *         WITH SYNTAX ExtensionRequest
 *         SINGLE VALUE TRUE
 *         ID pkcs-9-at-extensionRequest
 *    }
 *
 *    ExtensionRequest ::= Extensions
 *
 *    pkcs-9-at-extensionRequest         OBJECT IDENTIFIER ::= {pkcs-9 14}
 *)

(*
 *   SEQUENCE {
 *      SEQUENCE {...}
 *      ...
 *   }
 *)

#set-options "--z3rlimit 128 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

val decl : unit

type deviceIDCRI_attributes_extensionRequest_payload_t = {
  deviceID_attr_ext_key_usage: key_usage_t
}

(* Spec *)
noextract
val parse_deviceIDCRI_attributes_extensionRequest_payload
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) deviceIDCRI_attributes_extensionRequest_payload_t

noextract
val serialize_deviceIDCRI_attributes_extensionRequest_payload
: serializer (parse_deviceIDCRI_attributes_extensionRequest_payload)

val lemma_serialize_deviceIDCRI_attributes_extensionRequest_payload_unfold
  (x: deviceIDCRI_attributes_extensionRequest_payload_t)
: Lemma (
  serialize_deviceIDCRI_attributes_extensionRequest_payload `serialize` x ==
  (serialize_x509_key_usage `serialize` x.deviceID_attr_ext_key_usage)
)

noextract inline_for_extraction unfold
[@@ "opaque_to_smt"]
let len_of_deviceIDCRI_attributes_extensionRequest_payload ()
: Tot (asn1_value_int32_of_type SEQUENCE)
= len_of_x509_key_usage ()

val lemma_serialize_deviceIDCRI_attributes_extensionRequest_payload_size
  (x: deviceIDCRI_attributes_extensionRequest_payload_t)
: Lemma (
  length_of_opaque_serialization serialize_deviceIDCRI_attributes_extensionRequest_payload x ==
  length_of_opaque_serialization serialize_x509_key_usage x.deviceID_attr_ext_key_usage /\
  (* exact size *)
  length_of_opaque_serialization serialize_deviceIDCRI_attributes_extensionRequest_payload x
  == v (len_of_deviceIDCRI_attributes_extensionRequest_payload ())
)

(*
 * [IMPLICIT 0] SET {
 *   SEQUENCE {
 *     oid: OID;
 *     val: SET of {
 *       SEQUENCE of {
 *         value
 *       }
 *     }
 *   }
 * }
 *)

let deviceIDCRI_attributes_t
= (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy
  `asn1_implicit_tagging` SET) `inbound_envelop_tag_with_value_of`
  (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
       (**) (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
       (**) (SET `serialize_asn1_envelop_tag_with_TLV`
            (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                 (**) serialize_deviceIDCRI_attributes_extensionRequest_payload))))

let parse_deviceIDCRI_attributes
: parser (parse_asn1_envelop_tag_with_TLV_kind (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET))
         deviceIDCRI_attributes_t
= deviceIDCRI_attributes_t
  `coerce_parser`
 ((CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy
  `asn1_implicit_tagging` SET) `parse_asn1_envelop_tag_with_TLV`
  (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
       (**) (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
       (**) (SET `serialize_asn1_envelop_tag_with_TLV`
            (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                 (**) serialize_deviceIDCRI_attributes_extensionRequest_payload)))))

let serialize_deviceIDCRI_attributes
: serializer parse_deviceIDCRI_attributes
= coerce_parser_serializer
  (* p *) (parse_deviceIDCRI_attributes)
  (* s *) ((CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy
           `asn1_implicit_tagging` SET) `serialize_asn1_envelop_tag_with_TLV`
           (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                (**) (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
                (**) (SET `serialize_asn1_envelop_tag_with_TLV`
                     (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                          (**) serialize_deviceIDCRI_attributes_extensionRequest_payload)))))
  (*prf*) ()

val lemma_serialize_deviceIDCRI_attributes_unfold
  (x: deviceIDCRI_attributes_t)
: Lemma ( predicate_serialize_asn1_envelop_tag_with_TLV_unfold
            (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy
            `asn1_implicit_tagging` SET)
            (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                (**) (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
                (**) (SET `serialize_asn1_envelop_tag_with_TLV`
                     (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                          (**) serialize_deviceIDCRI_attributes_extensionRequest_payload))))
            (x) )

val lemma_serialize_deviceIDCRI_attributes_size
  (x: deviceIDCRI_attributes_t)
: Lemma ( predicate_serialize_asn1_envelop_tag_with_TLV_size
            (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy
            `asn1_implicit_tagging` SET)
            (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                (**) (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
                (**) (SET `serialize_asn1_envelop_tag_with_TLV`
                     (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                          (**) serialize_deviceIDCRI_attributes_extensionRequest_payload))))
            (x) )

(* length helpers *)
// let length_of_deviceIDCRI_attributes
//   (ku: key_usage_payload_t)
// : GTot (asn1_TLV_length_of_type SEQUENCE)
// = (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET) `length_of_TLV`
//   (**) (SEQUENCE `length_of_TLV`
//        (**) (length_of_asn1_primitive_TLV #OID OID_PKCS9_CSR_EXT_REQ +
//        (**)  SET `length_of_TLV`
//             (**) (SEQUENCE `length_of_TLV`
//                  (**) (v (len_of_deviceIDCRI_attributes_extensionRequest_payload ())))))

noextract inline_for_extraction unfold
[@@ "opaque_to_smt"]
let len_of_deviceIDCRI_attributes ()
: Tot (asn1_TLV_int32_of_type SEQUENCE)
= (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET) `len_of_TLV`
  (**) (SEQUENCE `len_of_TLV`
       (**) (len_of_asn1_primitive_TLV #OID OID_PKCS9_CSR_EXT_REQ +
       (**)  SET `len_of_TLV`
            (**) (SEQUENCE `len_of_TLV`
                 (**) (len_of_deviceIDCRI_attributes_extensionRequest_payload ()))))

// let deviceIDCRI_attributes_extensionRequest_coerce_remove_outermost_tag
//   (x: deviceIDCRI_attributes_t)
// = coerce_envelop
//     (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET)
//     (SEQUENCE)
//     (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
//     (**) (SET `serialize_asn1_envelop_tag_with_TLV`
//          (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
//               (**) serialize_deviceIDCRI_attributes_extensionRequest_payload)))
//     (x)

(* lemma for exact size *)
val lemma_serialize_deviceIDCRI_attributes_size_exact
  (x: deviceIDCRI_attributes_t)
: Lemma (
  let x' = coerce_envelop
             (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET)
             (SEQUENCE)
             (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
             (**) (SET `serialize_asn1_envelop_tag_with_TLV`
                  (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                       (**) serialize_deviceIDCRI_attributes_extensionRequest_payload)))
             (x) in
  length_of_opaque_serialization serialize_deviceIDCRI_attributes x
  == v (len_of_deviceIDCRI_attributes ())
)

(*
 * Low Implementation
 *)

val serialize32_deviceIDCRI_attributes_extensionRequest_payload_backwards
: serializer32_backwards (serialize_deviceIDCRI_attributes_extensionRequest_payload)

val serialize32_deviceIDCRI_attributes_backwards
: serializer32_backwards (serialize_deviceIDCRI_attributes)

///
///
/// helper constructor
///
let x509_get_deviceIDCRI_attributes
  (ku: key_usage_payload_t)
: Tot (deviceIDCRI_attributes_t)
=
  (* construct extensions *)
  let key_usage = x509_get_key_usage ku in
  (* Prf *) lemma_serialize_x509_key_usage_size_exact key_usage;

  (* construct innermost payload *)
  [@inline_let]
  let attrs_payload: deviceIDCRI_attributes_extensionRequest_payload_t = {
    deviceID_attr_ext_key_usage = key_usage
  } in
  (* Prf *) lemma_serialize_deviceIDCRI_attributes_extensionRequest_payload_size attrs_payload;

  (* envelop into the innermost SEQUENCE *)
  [@inline_let]
  let attrs_payload: (SEQUENCE `inbound_envelop_tag_with_value_of`
                     (**) serialize_deviceIDCRI_attributes_extensionRequest_payload) = attrs_payload in
  (* Prf *) lemma_serialize_asn1_envelop_tag_with_TLV_size
              (SEQUENCE)
              (serialize_deviceIDCRI_attributes_extensionRequest_payload)
              (attrs_payload);

  (* envelop into SET *)
  [@inline_let]
  let attrs_payload: (SET `inbound_envelop_tag_with_value_of`
                     (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                          (**) serialize_deviceIDCRI_attributes_extensionRequest_payload))
  = coerce_envelop_back SET SEQUENCE serialize_deviceIDCRI_attributes_extensionRequest_payload attrs_payload in
  (* Prf *) lemma_serialize_asn1_envelop_tag_with_TLV_size
              (SET)
              (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
              (**) serialize_deviceIDCRI_attributes_extensionRequest_payload)
              (attrs_payload);

  (* attach the OID *)
  [@inline_let]
  let attrs: (OID_PKCS9_CSR_EXT_REQ `envelop_OID_with_t`
             (SET `inbound_envelop_tag_with_value_of`
             (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                  (**) serialize_deviceIDCRI_attributes_extensionRequest_payload))) = (
      OID_PKCS9_CSR_EXT_REQ,
      attrs_payload
  ) in
  (* Prf *) lemma_serialize_asn1_oid_TLV_of_size OID_PKCS9_CSR_EXT_REQ OID_PKCS9_CSR_EXT_REQ;
  (* Prf *) lemma_serialize_envelop_OID_with_size
              (OID_PKCS9_CSR_EXT_REQ)
              (SET `serialize_asn1_envelop_tag_with_TLV`
              (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                   (**) serialize_deviceIDCRI_attributes_extensionRequest_payload))
              (attrs);
  (* Prf *) lemma_serialize_asn1_envelop_tag_with_TLV_size
              (SEQUENCE)
              (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
              (SET `serialize_asn1_envelop_tag_with_TLV`
              (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                   (**) serialize_deviceIDCRI_attributes_extensionRequest_payload)))
              (attrs);

(*return*) attrs
