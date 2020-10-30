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

#set-options "--z3rlimit 128 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

#set-options "--__temp_no_proj RIoT.X509.DeviceIDCRI.Attributes"

let decl = ()

let deviceIDCRI_attributes_extensionRequest_payload_t' = (
  key_usage_t
)

(* Conversion of message between record and tuple types *)
let synth_deviceIDCRI_attributes_extensionRequest_payload_t
  (x: deviceIDCRI_attributes_extensionRequest_payload_t')
: GTot (deviceIDCRI_attributes_extensionRequest_payload_t) = {
  deviceID_attr_ext_key_usage = x
}

inline_for_extraction noextract
let synth_deviceIDCRI_attributes_extensionRequest_payload_t'
  (x: deviceIDCRI_attributes_extensionRequest_payload_t)
: Tot (x': deviceIDCRI_attributes_extensionRequest_payload_t'
           { x == synth_deviceIDCRI_attributes_extensionRequest_payload_t x' }) = (
  x.deviceID_attr_ext_key_usage
)

(* Spec *)
let parse_deviceIDCRI_attributes_extensionRequest_payload
= parse_x509_key_usage
  `parse_synth`
  synth_deviceIDCRI_attributes_extensionRequest_payload_t

let serialize_deviceIDCRI_attributes_extensionRequest_payload
= serialize_synth
  (* p1 *) (parse_x509_key_usage)
  (* f2 *) (synth_deviceIDCRI_attributes_extensionRequest_payload_t)
  (* s1 *) (serialize_x509_key_usage)
  (* g1 *) (synth_deviceIDCRI_attributes_extensionRequest_payload_t')
  (* prf*) ()

let lemma_serialize_deviceIDCRI_attributes_extensionRequest_payload_unfold x
= serialize_synth_eq
  (* p1 *) (parse_x509_key_usage)
  (* f2 *) (synth_deviceIDCRI_attributes_extensionRequest_payload_t)
  (* s1 *) (serialize_x509_key_usage)
  (* g1 *) (synth_deviceIDCRI_attributes_extensionRequest_payload_t')
  (* prf*) ()
  (* in *) (x)

let lemma_serialize_deviceIDCRI_attributes_extensionRequest_payload_size x
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

let lemma_serialize_deviceIDCRI_attributes_unfold x
= lemma_serialize_asn1_envelop_tag_with_TLV_unfold
    (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy
    `asn1_implicit_tagging` SET)
    (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
         (**) (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
         (**) (SET `serialize_asn1_envelop_tag_with_TLV`
              (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                   (**) serialize_deviceIDCRI_attributes_extensionRequest_payload))))
    (x)

let lemma_serialize_deviceIDCRI_attributes_size x
= lemma_serialize_asn1_envelop_tag_with_TLV_size
    (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy
    `asn1_implicit_tagging` SET)
    (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
         (**) (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
         (**) (SET `serialize_asn1_envelop_tag_with_TLV`
              (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                   (**) serialize_deviceIDCRI_attributes_extensionRequest_payload))))
    (x)

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
let lemma_serialize_deviceIDCRI_attributes_size_exact x
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


(*
 * Low Implementation
 *)

let serialize32_deviceIDCRI_attributes_extensionRequest_payload_backwards
= serialize32_synth_backwards
  (* s32 *) (serialize32_x509_key_usage_backwards)
  (* f2  *) (synth_deviceIDCRI_attributes_extensionRequest_payload_t)
  (* g1  *) (synth_deviceIDCRI_attributes_extensionRequest_payload_t')
  (* g1' *) (synth_deviceIDCRI_attributes_extensionRequest_payload_t')
  (* prf *) ()

let serialize32_deviceIDCRI_attributes_backwards
= coerce_serializer32_backwards
  (* s2  *) (serialize_deviceIDCRI_attributes)
  (* s32 *) ((CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET) `serialize32_asn1_envelop_tag_with_TLV_backwards`
            (**) (SEQUENCE `serialize32_asn1_envelop_tag_with_TLV_backwards`
                 (**) (OID_PKCS9_CSR_EXT_REQ `serialize32_envelop_OID_with_backwards`
                 (**) (SET `serialize32_asn1_envelop_tag_with_TLV_backwards`
                      (**) (SEQUENCE `serialize32_asn1_envelop_tag_with_TLV_backwards`
                           (**) serialize32_deviceIDCRI_attributes_extensionRequest_payload_backwards)))))
  (* prf *) ()
