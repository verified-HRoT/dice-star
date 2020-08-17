module RIoT.X509.DeviceIDCRI

open ASN1.Spec
open ASN1.Low
open X509
// open RIoT.X509.Base
// include RIoT.X509.FWID
// include RIoT.X509.CompositeDeviceID
// include RIoT.X509.Extension
open RIoT.X509.DeviceIDCRI.Attributes
open FStar.Integers

module B32 = FStar.Bytes

open LowParse.Spec.SeqBytes.Base
open LowParse.Spec.Bytes

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

(*     (To-Be-Signed) DeviceID Certification Request Info
 *================================================================
 *   CertificationRequestInfo ::= SEQUENCE {
 *        version       INTEGER { v1(0) } (v1,...),
 *        subject       Name,
 *        subjectPKInfo SubjectPublicKeyInfo{{ PKInfoAlgorithms }},
 *        attributes    [0] Attributes{{ CRIAttributes }}
 *   }
 *
 *)

type deviceIDCRI_payload_t (subject_len: asn1_int32) = {
  deviceIDCRI_version: datatype_of_asn1_type INTEGER;
  deviceIDCRI_subject: B32.lbytes32 subject_len; // name
  deviceIDCRI_subjectPKInfo: subjectPublicKeyInfo_t;
  deviceIDCRI_attributes: deviceIDCRI_attributes_t
}

let deviceIDCRI_payload_t' (subject_len: asn1_int32) = (
  datatype_of_asn1_type INTEGER `tuple2`
  B32.lbytes32 subject_len `tuple2`
  subjectPublicKeyInfo_t `tuple2`
  deviceIDCRI_attributes_t
)


(* Conversion *)
let synth_deviceIDCRI_payload_t
  (subject_len: asn1_int32)
  (x': deviceIDCRI_payload_t' subject_len)
: GTot (deviceIDCRI_payload_t subject_len) = {
  deviceIDCRI_version       = fst (fst (fst x'));
  deviceIDCRI_subject       = snd (fst (fst x'));
  deviceIDCRI_subjectPKInfo = snd (fst x');
  deviceIDCRI_attributes    = snd x';
}

let synth_deviceIDCRI_payload_t'
  (subject_len: asn1_int32)
  (x: deviceIDCRI_payload_t subject_len)
: Tot (x': deviceIDCRI_payload_t' subject_len
            { x == synth_deviceIDCRI_payload_t subject_len x' }) = (
  (((x.deviceIDCRI_version),
     x.deviceIDCRI_subject),
     x.deviceIDCRI_subjectPKInfo),
     x.deviceIDCRI_attributes
)


(*
 * Specification
 *)
let parse_deviceIDCRI_payload
  (subject_len: asn1_int32)
: parser _ (deviceIDCRI_payload_t subject_len)
= parse_asn1_TLV_of_type INTEGER
  `nondep_then`
  parse_flbytes32 subject_len
  `nondep_then`
  parse_subjectPublicKeyInfo
  `nondep_then`
  parse_deviceIDCRI_attributes
  `parse_synth`
  synth_deviceIDCRI_payload_t subject_len

let serialize_deviceIDCRI_payload
  (subject_len: asn1_int32)
: serializer (parse_deviceIDCRI_payload subject_len)
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type INTEGER
            `nondep_then`
            parse_flbytes32 subject_len
            `nondep_then`
            parse_subjectPublicKeyInfo
            `nondep_then`
            parse_deviceIDCRI_attributes)
  (* f2 *) (synth_deviceIDCRI_payload_t subject_len)
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_flbytes32 subject_len
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo
            `serialize_nondep_then`
            serialize_deviceIDCRI_attributes)
  (* g1 *) (synth_deviceIDCRI_payload_t' subject_len)
  (* prf*) ()

let lemma_serialize_deviceIDCRI_payload_unfold
  (subject_len: asn1_int32)
  (x: deviceIDCRI_payload_t subject_len)
: Lemma (
  serialize_deviceIDCRI_payload subject_len `serialize` x ==
 (serialize_asn1_TLV_of_type INTEGER `serialize` x.deviceIDCRI_version)
  `Seq.append`
 (serialize_flbytes32 subject_len `serialize` x.deviceIDCRI_subject)
  `Seq.append`
 (serialize_subjectPublicKeyInfo `serialize` x.deviceIDCRI_subjectPKInfo)
  `Seq.append`
 (serialize_deviceIDCRI_attributes `serialize` x.deviceIDCRI_attributes)
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER)
  (* s2 *) (serialize_flbytes32 subject_len)
  (* in *) (fst (fst (synth_deviceIDCRI_payload_t' subject_len x)));
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_flbytes32 subject_len)
  (* s2 *) (serialize_subjectPublicKeyInfo)
  (* in *) (fst (synth_deviceIDCRI_payload_t' subject_len x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_flbytes32 subject_len
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo)
  (* s2 *) (serialize_deviceIDCRI_attributes)
  (* in *) (synth_deviceIDCRI_payload_t' subject_len x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type INTEGER
            `nondep_then`
            parse_flbytes32 subject_len
            `nondep_then`
            parse_subjectPublicKeyInfo
            `nondep_then`
            parse_deviceIDCRI_attributes)
  (* f2 *) (synth_deviceIDCRI_payload_t subject_len)
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_flbytes32 subject_len
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo
            `serialize_nondep_then`
            serialize_deviceIDCRI_attributes)
  (* g1 *) (synth_deviceIDCRI_payload_t' subject_len)
  (* prf*) ()
  (* in *) (x)

#push-options "--z3rlimit 128"
let length_of_deviceIDCRI_payload
  (subject_len: asn1_int32)
  (version: datatype_of_asn1_type INTEGER)
  (ku: key_usage_payload_t)
: GTot (nat)
= length_of_asn1_primitive_TLV #INTEGER version +
  v subject_len +
  length_of_subjectPublicKeyInfo +
  length_of_deviceIDCRI_attributes ku

let len_of_deviceIDCRI_payload
  (subject_len: asn1_int32)
  (version: datatype_of_asn1_type INTEGER)
  (ku: key_usage_payload_t
       { length_of_deviceIDCRI_payload subject_len version ku
         <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_value_int32_of_type SEQUENCE
             { v len == length_of_deviceIDCRI_payload subject_len version ku })
= len_of_asn1_primitive_TLV #INTEGER version +
  subject_len +
  len_of_subjectPublicKeyInfo +
  len_of_deviceIDCRI_attributes ku
#pop-options

#push-options "--z3rlimit 64"
let lemma_serialize_deviceIDCRI_payload_size
  (subject_len: asn1_int32)
  (x: deviceIDCRI_payload_t subject_len)
: Lemma (
  let attrs' = coerce_envelop
                (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET)
                (SEQUENCE)
                (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
                (**) (SET `serialize_asn1_envelop_tag_with_TLV`
                     (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                          (**) serialize_deviceIDCRI_attributes_extensionRequest_payload)))
                (x.deviceIDCRI_attributes) in
  length_of_opaque_serialization (serialize_deviceIDCRI_payload subject_len) x ==
  length_of_opaque_serialization (serialize_asn1_TLV_of_type INTEGER) x.deviceIDCRI_version +
  length_of_opaque_serialization (serialize_flbytes32 subject_len)    x.deviceIDCRI_subject +
  length_of_opaque_serialization (serialize_subjectPublicKeyInfo)     x.deviceIDCRI_subjectPKInfo +
  length_of_opaque_serialization (serialize_deviceIDCRI_attributes) x.deviceIDCRI_attributes /\
  length_of_opaque_serialization (serialize_deviceIDCRI_payload subject_len) x
  == length_of_deviceIDCRI_payload subject_len x.deviceIDCRI_version (snd (snd attrs').deviceID_attr_ext_key_usage)
)
= lemma_serialize_deviceIDCRI_payload_unfold subject_len x;
    lemma_serialize_flbytes32_size subject_len x.deviceIDCRI_subject;
    lemma_serialize_subjectPublicKeyInfo_size_exact x.deviceIDCRI_subjectPKInfo;
    lemma_serialize_deviceIDCRI_attributes_size_exact x.deviceIDCRI_attributes
#pop-options

(*
 *
 *)
let deviceIDCRI_t
  (subject_len: asn1_int32)
= inbound_sequence_value_of (serialize_deviceIDCRI_payload subject_len)

let parse_deviceIDCRI
  (subject_len: asn1_int32)
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (deviceIDCRI_t subject_len)
= (deviceIDCRI_t subject_len)
   `coerce_parser`
  (parse_asn1_sequence_TLV
  (**) (serialize_deviceIDCRI_payload subject_len))

let serialize_deviceIDCRI
  (subject_len: asn1_int32)
= coerce_parser_serializer
  (* p *) (parse_deviceIDCRI subject_len)
  (* s *) (serialize_asn1_sequence_TLV
          (**) (serialize_deviceIDCRI_payload subject_len))
  (*prf*) ()

let lemma_serialize_deviceIDCRI_unfold
  (subject_len: asn1_int32)
  (x: deviceIDCRI_t subject_len)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_deviceIDCRI_payload subject_len) x )
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_deviceIDCRI_payload subject_len) x

let lemma_serialize_deviceIDCRI_size
  (subject_len: asn1_int32)
  (x: deviceIDCRI_t subject_len)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_deviceIDCRI_payload subject_len) x )
= lemma_serialize_asn1_sequence_TLV_size (serialize_deviceIDCRI_payload subject_len) x

unfold
let valid_deviceIDCRI_ingredients
  (subject_len: asn1_int32)
  (version: datatype_of_asn1_type INTEGER)
  (ku: key_usage_payload_t)
: Type0
= length_of_deviceIDCRI_payload subject_len version ku
  <= asn1_value_length_max_of_type SEQUENCE

#push-options "--z3rlimit 128"
let length_of_deviceIDCRI
  (subject_len: asn1_int32)
  (version: datatype_of_asn1_type INTEGER)
  (ku: key_usage_payload_t
       { valid_deviceIDCRI_ingredients subject_len version ku })
: GTot (asn1_TLV_length_of_type SEQUENCE)
= length_of_TLV SEQUENCE (length_of_deviceIDCRI_payload subject_len version ku)

let len_of_deviceIDCRI
  (subject_len: asn1_int32)
  (version: datatype_of_asn1_type INTEGER)
  (ku: key_usage_payload_t
       { valid_deviceIDCRI_ingredients subject_len version ku })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
             { v len == length_of_deviceIDCRI subject_len version ku })
= len_of_TLV SEQUENCE (len_of_deviceIDCRI_payload subject_len version ku)
#pop-options

let lemma_serialize_deviceIDCRI_size_exact
  (subject_len: asn1_int32)
  (x: deviceIDCRI_t subject_len
      { let attrs' = coerce_envelop
                (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET)
                (SEQUENCE)
                (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
                (**) (SET `serialize_asn1_envelop_tag_with_TLV`
                     (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                          (**) serialize_deviceIDCRI_attributes_extensionRequest_payload)))
                (x.deviceIDCRI_attributes) in
        let ku: key_usage_payload_t = snd (snd attrs').deviceID_attr_ext_key_usage in
        valid_deviceIDCRI_ingredients subject_len x.deviceIDCRI_version ku })
: Lemma (
  let _ = lemma_serialize_deviceIDCRI_size subject_len x in
  let attrs' = coerce_envelop
                (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET)
                (SEQUENCE)
                (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
                (**) (SET `serialize_asn1_envelop_tag_with_TLV`
                     (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                          (**) serialize_deviceIDCRI_attributes_extensionRequest_payload)))
                (x.deviceIDCRI_attributes) in
  let ku: key_usage_payload_t = snd (snd attrs').deviceID_attr_ext_key_usage in
  length_of_opaque_serialization (serialize_deviceIDCRI subject_len) x
  == length_of_deviceIDCRI subject_len x.deviceIDCRI_version ku )
= lemma_serialize_deviceIDCRI_size subject_len x;
  (**) lemma_serialize_deviceIDCRI_payload_size subject_len x

(* low *)

let serialize32_deviceIDCRI_payload_backwards
  (subject_len: asn1_int32)
: serializer32_backwards (serialize_deviceIDCRI_payload subject_len)
= serialize32_synth_backwards
  (* s32*) (serialize32_asn1_TLV_backwards_of_type INTEGER
            `serialize32_nondep_then_backwards`
            serialize32_flbytes32_backwards subject_len
            `serialize32_nondep_then_backwards`
            serialize32_subjectPublicKeyInfo_backwards
            `serialize32_nondep_then_backwards`
            serialize32_deviceIDCRI_attributes_backwards)
  (* f2 *) (synth_deviceIDCRI_payload_t subject_len)
  (* g1 *) (synth_deviceIDCRI_payload_t' subject_len)
  (* g1'*) (synth_deviceIDCRI_payload_t' subject_len)
  (* prf*) ()

let serialize32_deviceIDCRI_backwards
  (subject_len: asn1_int32)
: serializer32_backwards (serialize_deviceIDCRI subject_len)
= coerce_serializer32_backwards
    (serialize_deviceIDCRI subject_len)
    (serialize32_asn1_sequence_TLV_backwards
      (serialize32_deviceIDCRI_payload_backwards subject_len))
    ()

let x509_get_deviceIDCRI
  (subject_len: asn1_int32)
  (subject: B32.lbytes32 subject_len)
  (version: datatype_of_asn1_type INTEGER)
  (ku: key_usage_payload_t
       { valid_deviceIDCRI_ingredients subject_len version ku })
  (deviceIDPub: B32.lbytes32 32ul)
: Tot (deviceIDCRI_t subject_len)
=
  let deviceIDCRI_attributes: deviceIDCRI_attributes_t = x509_get_deviceIDCRI_attributes ku in
  (* Prf *) lemma_serialize_deviceIDCRI_attributes_size_exact deviceIDCRI_attributes;

  let deviceID_PKInfo = x509_get_subjectPublicKeyInfo deviceIDPub in
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_size_exact deviceID_PKInfo;

  let deviceIDCRI: deviceIDCRI_payload_t subject_len = {
    deviceIDCRI_version       = version;
    deviceIDCRI_subject       = subject;
    deviceIDCRI_subjectPKInfo = deviceID_PKInfo;
    deviceIDCRI_attributes    = deviceIDCRI_attributes;
  } in
  (* Prf *) lemma_serialize_deviceIDCRI_payload_unfold subject_len deviceIDCRI;
  (* Prf *) lemma_serialize_deviceIDCRI_payload_size   subject_len deviceIDCRI;
  (* Prf *) (**) lemma_serialize_flbytes32_size subject_len deviceIDCRI.deviceIDCRI_subject;

(*return*) deviceIDCRI
