module RIoT.X509.DeviceIDCRI.Attributes

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

#set-options "--query_stats --z3rlimit 32 --fuel 0 --ifuel 0"
type deviceIDCRI_attributes_extensionRequest_payload_t = {
  deviceID_attr_ext_key_usage: key_usage_t
}

let deviceIDCRI_attributes_extensionRequest_payload_t' = (
  key_usage_t
)

(* Conversion of message between record and tuple types *)
let synth_deviceIDCRI_attributes_extensionRequest_payload_t
  (x: deviceIDCRI_attributes_extensionRequest_payload_t')
: GTot (deviceIDCRI_attributes_extensionRequest_payload_t) = {
  deviceID_attr_ext_key_usage = x
}

let synth_deviceIDCRI_attributes_extensionRequest_payload_t'
  (x: deviceIDCRI_attributes_extensionRequest_payload_t)
: Tot (x': deviceIDCRI_attributes_extensionRequest_payload_t'
           { x == synth_deviceIDCRI_attributes_extensionRequest_payload_t x' }) = (
  x.deviceID_attr_ext_key_usage
)

(* Spec *)
let parse_deviceIDCRI_attributes_extensionRequest_payload
: parser _ deviceIDCRI_attributes_extensionRequest_payload_t
= parse_x509_key_usage
  `parse_synth`
  synth_deviceIDCRI_attributes_extensionRequest_payload_t

let serialize_deviceIDCRI_attributes_extensionRequest_payload
: serializer (parse_deviceIDCRI_attributes_extensionRequest_payload)
= serialize_synth
  (* p1 *) (parse_x509_key_usage)
  (* f2 *) (synth_deviceIDCRI_attributes_extensionRequest_payload_t)
  (* s1 *) (serialize_x509_key_usage)
  (* g1 *) (synth_deviceIDCRI_attributes_extensionRequest_payload_t')
  (* prf*) ()

let lemma_serialize_deviceIDCRI_attributes_extensionRequest_payload_unfold
  (x: deviceIDCRI_attributes_extensionRequest_payload_t)
: Lemma (
  serialize_deviceIDCRI_attributes_extensionRequest_payload `serialize` x ==
  (serialize_x509_key_usage `serialize` x.deviceID_attr_ext_key_usage)
)
= serialize_synth_eq
  (* p1 *) (parse_x509_key_usage)
  (* f2 *) (synth_deviceIDCRI_attributes_extensionRequest_payload_t)
  (* s1 *) (serialize_x509_key_usage)
  (* g1 *) (synth_deviceIDCRI_attributes_extensionRequest_payload_t')
  (* prf*) ()
  (* in *) (x)

let length_of_deviceIDCRI_attributes_extensionRequest_payload
  (ku: key_usage_payload_t)
: GTot (nat)
= length_of_x509_key_usage ku

let len_of_deviceIDCRI_attributes_extensionRequest_payload
  (ku: key_usage_payload_t)
: Tot (len: asn1_value_int32_of_type SEQUENCE
            { v len == length_of_deviceIDCRI_attributes_extensionRequest_payload ku })
= len_of_x509_key_usage ku

let lemma_serialize_deviceIDCRI_attributes_extensionRequest_payload_size
  (x: deviceIDCRI_attributes_extensionRequest_payload_t)
: Lemma (
  length_of_opaque_serialization serialize_deviceIDCRI_attributes_extensionRequest_payload x ==
  length_of_opaque_serialization serialize_x509_key_usage x.deviceID_attr_ext_key_usage /\
  (* exact size *)
  length_of_opaque_serialization serialize_deviceIDCRI_attributes_extensionRequest_payload x
  == length_of_deviceIDCRI_attributes_extensionRequest_payload (snd x.deviceID_attr_ext_key_usage)
)
= lemma_serialize_deviceIDCRI_attributes_extensionRequest_payload_unfold x;
    lemma_serialize_x509_key_usage_size_exact x.deviceID_attr_ext_key_usage

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
// : parser (parse_asn1_envelop_tag_with_TLV_kind (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET))
//          deviceIDCRI_attributes_t
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
// : serializer (parse_deviceIDCRI_attributes_extensionRequest)
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

let lemma_serialize_deviceIDCRI_attributes_unfold
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
= lemma_serialize_asn1_envelop_tag_with_TLV_unfold
    (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy
    `asn1_implicit_tagging` SET)
    (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
         (**) (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
         (**) (SET `serialize_asn1_envelop_tag_with_TLV`
              (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                   (**) serialize_deviceIDCRI_attributes_extensionRequest_payload))))
    (x)

let lemma_serialize_deviceIDCRI_attributes_size
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
= lemma_serialize_asn1_envelop_tag_with_TLV_size
    (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy
    `asn1_implicit_tagging` SET)
    (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
         (**) (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
         (**) (SET `serialize_asn1_envelop_tag_with_TLV`
              (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                   (**) serialize_deviceIDCRI_attributes_extensionRequest_payload))))
    (x)

(* length helpers *)
let length_of_deviceIDCRI_attributes
  (ku: key_usage_payload_t)
: GTot (asn1_TLV_length_of_type SEQUENCE)
= (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET) `length_of_TLV`
  (**) (SEQUENCE `length_of_TLV`
       (**) (length_of_asn1_primitive_TLV #OID OID_PKCS9_CSR_EXT_REQ +
       (**)  SET `length_of_TLV`
            (**) (SEQUENCE `length_of_TLV`
                 (**) (length_of_deviceIDCRI_attributes_extensionRequest_payload ku))))

#push-options "--z3rlimit 64"
let len_of_deviceIDCRI_attributes
  (ku: key_usage_payload_t)
: Tot (asn1_TLV_int32_of_type SEQUENCE)
= (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET) `len_of_TLV`
  (**) (SEQUENCE `len_of_TLV`
       (**) (len_of_asn1_primitive_TLV #OID OID_PKCS9_CSR_EXT_REQ +
       (**)  SET `len_of_TLV`
            (**) (SEQUENCE `len_of_TLV`
                 (**) (len_of_deviceIDCRI_attributes_extensionRequest_payload ku))))
#pop-options

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
#push-options "--z3rlimit 64 --fuel 0 --ifuel 4"
let lemma_serialize_deviceIDCRI_attributes_size_exact
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
  == length_of_deviceIDCRI_attributes (snd (snd x').deviceID_attr_ext_key_usage)
)
= (* reveal top level *)
  lemma_serialize_deviceIDCRI_attributes_size x;
  (* reveal the outermost [0] tagged SET *)
  (**) lemma_serialize_asn1_envelop_tag_with_TLV_size
         (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET)
         (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
         (**) (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
         (**) (SET `serialize_asn1_envelop_tag_with_TLV`
              (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                   (**) serialize_deviceIDCRI_attributes_extensionRequest_payload))))
         (x);
         (* reveal the second outermost SEQUENCE *)
         (**) lemma_serialize_asn1_envelop_tag_with_TLV_size
                (SEQUENCE)
                (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
                (SET `serialize_asn1_envelop_tag_with_TLV`
                (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                     (**) serialize_deviceIDCRI_attributes_extensionRequest_payload)))
                (x);
                (* reveal OID_with *)
                (**) lemma_serialize_envelop_OID_with_size
                       (OID_PKCS9_CSR_EXT_REQ)
                       (SET `serialize_asn1_envelop_tag_with_TLV`
                       (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                            (**) serialize_deviceIDCRI_attributes_extensionRequest_payload))
                       (x);
                (* reveal oid *)
                (**) lemma_serialize_asn1_oid_TLV_of_size OID_PKCS9_CSR_EXT_REQ OID_PKCS9_CSR_EXT_REQ;
                let x = coerce_envelop
                          (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET)
                          (SEQUENCE)
                          (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
                          (**) (SET `serialize_asn1_envelop_tag_with_TLV`
                               (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                                    (**) serialize_deviceIDCRI_attributes_extensionRequest_payload)))
                          (x) in
                (* reveal SET *)
                (**) lemma_serialize_asn1_envelop_tag_with_TLV_size
                       (SET)
                       (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                       (**) serialize_deviceIDCRI_attributes_extensionRequest_payload)
                       (snd x);
                       (* reveal the innermost SEQUENCE *)
                       (**) lemma_serialize_asn1_envelop_tag_with_TLV_size
                              (SEQUENCE)
                              (serialize_deviceIDCRI_attributes_extensionRequest_payload)
                              (coerce_envelop SET SEQUENCE serialize_deviceIDCRI_attributes_extensionRequest_payload (snd x));
                              (**) lemma_serialize_deviceIDCRI_attributes_extensionRequest_payload_size (snd x);
()
#pop-options


(*
 * Low Implementation
 *)

let serialize32_deviceIDCRI_attributes_extensionRequest_payload_backwards
: serializer32_backwards (serialize_deviceIDCRI_attributes_extensionRequest_payload)
= serialize32_synth_backwards
  (* s32 *) (serialize32_x509_key_usage_backwards)
  (* f2  *) (synth_deviceIDCRI_attributes_extensionRequest_payload_t)
  (* g1  *) (synth_deviceIDCRI_attributes_extensionRequest_payload_t')
  (* g1' *) (synth_deviceIDCRI_attributes_extensionRequest_payload_t')
  (* prf *) ()

let serialize32_deviceIDCRI_attributes_backwards
// : serializer32_backwards (serialize_deviceIDCRI_attributes_extensionRequest)
= coerce_serializer32_backwards
  (* s2  *) (serialize_deviceIDCRI_attributes)
  (* s32 *) ((CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET) `serialize32_asn1_envelop_tag_with_TLV_backwards`
            (**) (SEQUENCE `serialize32_asn1_envelop_tag_with_TLV_backwards`
                 (**) (OID_PKCS9_CSR_EXT_REQ `serialize32_envelop_OID_with_backwards`
                 (**) (SET `serialize32_asn1_envelop_tag_with_TLV_backwards`
                      (**) (SEQUENCE `serialize32_asn1_envelop_tag_with_TLV_backwards`
                           (**) serialize32_deviceIDCRI_attributes_extensionRequest_payload_backwards)))))
  (* prf *) ()

///
///
/// helper constructor
///
#push-options "--z3rlimit 64 --ifuel 0"
let x509_get_deviceIDCRI_attributes
  (ku: key_usage_payload_t)
: Tot (deviceIDCRI_attributes_t)
=
  (* construct extensions *)
  let key_usage = x509_get_key_usage ku in
  (* Prf *) lemma_serialize_x509_key_usage_size_exact key_usage;

  (* construct innermost payload *)
  let attrs_payload: deviceIDCRI_attributes_extensionRequest_payload_t = {
    deviceID_attr_ext_key_usage = key_usage
  } in
  (* Prf *) lemma_serialize_deviceIDCRI_attributes_extensionRequest_payload_size attrs_payload;

  (* envelop into the innermost SEQUENCE *)
  let attrs_payload: (SEQUENCE `inbound_envelop_tag_with_value_of`
                     (**) serialize_deviceIDCRI_attributes_extensionRequest_payload) = attrs_payload in
  (* Prf *) lemma_serialize_asn1_envelop_tag_with_TLV_size
              (SEQUENCE)
              (serialize_deviceIDCRI_attributes_extensionRequest_payload)
              (attrs_payload);

  (* envelop into SET *)
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
#pop-options
