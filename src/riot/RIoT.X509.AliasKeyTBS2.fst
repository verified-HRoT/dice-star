module RIoT.X509.AliasKeyTBS2

open ASN1.Spec
open ASN1.Low
open X509
open RIoT.X509.AliasKeyTBS.Extensions
open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

type aliasKeyTBS_payload_t (header_len: asn1_int32) = {
(*
 *       version         [0]  EXPLICIT Version DEFAULT v1,
 *)
  aliasKeyTBS_version     : x509_version_t;
(*
 *       serialNumber         CertificateSerialNumber,
 *)
  aliasKeyTBS_serialNumber: datatype_of_asn1_type INTEGER;
(*
 *       signature            AlgorithmIdentifier,
 *)
  aliasKeyTBS_signatureAlg: algorithmIdentifier_t;
(* TEMPLATE of
 *       issuer               Name,
 *       validity             Validity,
 *       subject              Name,
 *)
  aliasKeyTBS_template    : B32.lbytes32 header_len;
 (*
  *      subjectPublicKeyInfo SubjectPublicKeyInfo
  *)
  aliasKeyTBS_aliasKey_pub: subjectPublicKeyInfo_t;
 (*
  *      extensions      [3]  EXPLICIT Extensions OPTIONAL
  *)
  aliasKeyTBS_extensions  : x509_extensions_t_inbound
                              serialize_aliasKeyTBS_extensions
}

let aliasKeyTBS_payload_t' (header_len: asn1_int32) = (
  x509_version_t `tuple2`
  datatype_of_asn1_type INTEGER `tuple2`
  algorithmIdentifier_t `tuple2`
  B32.lbytes32 header_len `tuple2`
  subjectPublicKeyInfo_t `tuple2`
  x509_extensions_t_inbound serialize_aliasKeyTBS_extensions
)

let synth_aliasKeyTBS_payload_t
  (header_len: asn1_int32)
  (x': aliasKeyTBS_payload_t' header_len)
: GTot (aliasKeyTBS_payload_t header_len)
= { aliasKeyTBS_version      = fst (fst (fst (fst (fst x'))));
    aliasKeyTBS_serialNumber = snd (fst (fst (fst (fst x'))));
    aliasKeyTBS_signatureAlg = snd (fst (fst (fst x')));
    aliasKeyTBS_template     = snd (fst (fst x'));
    aliasKeyTBS_aliasKey_pub = snd (fst x');
    aliasKeyTBS_extensions   = snd x' }

let synth_aliasKeyTBS_payload_t'
  (header_len: asn1_int32)
  (x: aliasKeyTBS_payload_t header_len)
: Tot (x': aliasKeyTBS_payload_t' header_len { x == synth_aliasKeyTBS_payload_t header_len x' })
= ((((x.aliasKeyTBS_version,
      x.aliasKeyTBS_serialNumber),
      x.aliasKeyTBS_signatureAlg),
      x.aliasKeyTBS_template),
      x.aliasKeyTBS_aliasKey_pub),
      x.aliasKeyTBS_extensions

let parse_aliasKeyTBS_payload
  (header_len: asn1_int32)
: parser _ (aliasKeyTBS_payload_t header_len)
= parse_x509_version
  `nondep_then`
  parse_asn1_TLV_of_type INTEGER
  `nondep_then`
  parse_algorithmIdentifier
  `nondep_then`
  parse_flbytes32 header_len
  `nondep_then`
  parse_subjectPublicKeyInfo
  `nondep_then`
  parse_x509_extensions_TLV serialize_aliasKeyTBS_extensions
  `parse_synth`
  synth_aliasKeyTBS_payload_t header_len

let serialize_aliasKeyTBS_payload
  (header_len: asn1_int32)
: serializer (parse_aliasKeyTBS_payload header_len)
= serialize_synth
  (* p1 *) (parse_x509_version
            `nondep_then`
            parse_asn1_TLV_of_type INTEGER
            `nondep_then`
            parse_algorithmIdentifier
            `nondep_then`
            parse_flbytes32 header_len
            `nondep_then`
            parse_subjectPublicKeyInfo
            `nondep_then`
            parse_x509_extensions_TLV serialize_aliasKeyTBS_extensions)
  (* f2 *) (synth_aliasKeyTBS_payload_t header_len)
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_flbytes32 header_len
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo
            `serialize_nondep_then`
            serialize_x509_extensions_TLV serialize_aliasKeyTBS_extensions)
  (* g1 *) (synth_aliasKeyTBS_payload_t' header_len)
  (* prf*) ()

let lemma_serialize_aliasKeyTBS_payload_unfold
  (header_len: asn1_int32)
  (x: aliasKeyTBS_payload_t header_len)
: Lemma (
  serialize_aliasKeyTBS_payload header_len `serialize` x ==
 (serialize_x509_version `serialize` x.aliasKeyTBS_version)
  `Seq.append`
 (serialize_asn1_TLV_of_type INTEGER `serialize` x.aliasKeyTBS_serialNumber)
  `Seq.append`
 (serialize_algorithmIdentifier `serialize` x.aliasKeyTBS_signatureAlg)
  `Seq.append`
 (serialize_flbytes32 header_len `serialize` x.aliasKeyTBS_template)
  `Seq.append`
 (serialize_subjectPublicKeyInfo `serialize` x.aliasKeyTBS_aliasKey_pub)
  `Seq.append`
 (serialize_x509_extensions_TLV serialize_aliasKeyTBS_extensions `serialize` x.aliasKeyTBS_extensions)
)
=
  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version)
  (* s2 *) (serialize_asn1_TLV_of_type INTEGER)
  (* in *) (fst (fst (fst (fst (synth_aliasKeyTBS_payload_t' header_len x)))));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type INTEGER)
  (* s2 *) (serialize_algorithmIdentifier)
  (* in *) (fst (fst (fst (synth_aliasKeyTBS_payload_t' header_len x))));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_algorithmIdentifier)
  (* s2 *) (serialize_flbytes32 header_len)
  (* in *) (fst (fst (synth_aliasKeyTBS_payload_t' header_len x)));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_flbytes32 header_len)
  (* s2 *) (serialize_subjectPublicKeyInfo)
  (* in *) (fst (synth_aliasKeyTBS_payload_t' header_len x));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_flbytes32 header_len
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo)
  (* s2 *) (serialize_x509_extensions_TLV serialize_aliasKeyTBS_extensions)
  (* in *) (synth_aliasKeyTBS_payload_t' header_len x);

  serialize_synth_eq
  (* p1 *) (parse_x509_version
            `nondep_then`
            parse_asn1_TLV_of_type INTEGER
            `nondep_then`
            parse_algorithmIdentifier
            `nondep_then`
            parse_flbytes32 header_len
            `nondep_then`
            parse_subjectPublicKeyInfo
            `nondep_then`
            parse_x509_extensions_TLV serialize_aliasKeyTBS_extensions)
  (* f2 *) (synth_aliasKeyTBS_payload_t header_len)
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_flbytes32 header_len
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo
            `serialize_nondep_then`
            serialize_x509_extensions_TLV serialize_aliasKeyTBS_extensions)
  (* g1 *) (synth_aliasKeyTBS_payload_t' header_len)
  (* prf*) ()
  (* in *) (x)

#restart-solver
#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let length_of_aliasKeyTBS_payload
  (serialNumber: datatype_of_asn1_type INTEGER)
  (header_len: asn1_int32)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER)
: GTot (nat)
= length_of_x509_version () +
  length_of_asn1_primitive_TLV serialNumber +
  length_of_algorithmIdentifier () +
  v header_len +
  length_of_subjectPublicKeyInfo +
  length_of_x509_extensions (length_of_aliasKeyTBS_extensions ku version)

let len_of_aliasKeyTBS_payload
  (serialNumber: datatype_of_asn1_type INTEGER)
  (header_len: asn1_int32)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER
            { length_of_aliasKeyTBS_payload serialNumber header_len ku version
              <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_aliasKeyTBS_payload serialNumber header_len ku version })
= len_of_x509_version () +
  len_of_asn1_primitive_TLV serialNumber +
  len_of_algorithmIdentifier () +
  header_len +
  len_of_subjectPublicKeyInfo +
  len_of_x509_extensions (len_of_aliasKeyTBS_extensions ku version)

let lemma_serialize_aliasKeyTBS_payload_size
  (header_len: asn1_int32)
  (x: aliasKeyTBS_payload_t header_len)
: Lemma (
  let riot_version = RIoT.X509.Extension.(x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version) in
  let ku = (snd x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_key_usage) in
  (* unfold *)
  length_of_opaque_serialization (serialize_aliasKeyTBS_payload header_len) x ==
  length_of_opaque_serialization (serialize_asn1_TLV_of_type INTEGER)       x.aliasKeyTBS_version      +
  length_of_opaque_serialization (serialize_asn1_TLV_of_type INTEGER)       x.aliasKeyTBS_serialNumber +
  length_of_opaque_serialization (serialize_algorithmIdentifier)            x.aliasKeyTBS_signatureAlg +
  length_of_opaque_serialization (serialize_flbytes32 header_len)           x.aliasKeyTBS_template     +
  length_of_opaque_serialization (serialize_subjectPublicKeyInfo)           x.aliasKeyTBS_aliasKey_pub +
  length_of_opaque_serialization (serialize_x509_extensions_TLV
                                  serialize_aliasKeyTBS_extensions) x.aliasKeyTBS_extensions /\
  (* exact size *)
  length_of_opaque_serialization (serialize_aliasKeyTBS_payload header_len)            x
  == length_of_aliasKeyTBS_payload
       x.aliasKeyTBS_serialNumber
       header_len
       ku
       riot_version
  (* upper bound *)
  // length_of_opaque_serialization (serialize_aliasKeyTBS header_len)            x
  // <= v header_len + 44 + (6 + (6 + 117))
)
=
  lemma_serialize_aliasKeyTBS_payload_unfold header_len x;
    lemma_serialize_x509_version_size_exact x.aliasKeyTBS_version;
    lemma_serialize_asn1_integer_TLV_size x.aliasKeyTBS_serialNumber;
    lemma_serialize_algorithmIdentifier_size_exact x.aliasKeyTBS_signatureAlg;
    (* + v header_len *)
    (* + 44 *)
    lemma_serialize_subjectPublicKeyInfo_size_exact x.aliasKeyTBS_aliasKey_pub;
    (* + (6) *)
    lemma_serialize_x509_extensions_TLV_size serialize_aliasKeyTBS_extensions x.aliasKeyTBS_extensions;
      (* + (6 + 117) / + |riot_veriosn| + 113 *)
      lemma_serialize_aliasKeyTBS_extensions_size_exact x.aliasKeyTBS_extensions
#pop-options

let aliasKeyTBS_t
  (header_len: asn1_int32)
= inbound_sequence_value_of (serialize_aliasKeyTBS_payload header_len)

let parse_aliasKeyTBS
  (header_len: asn1_int32)
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (aliasKeyTBS_t header_len)
=
  aliasKeyTBS_t header_len
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_aliasKeyTBS_payload header_len)

let serialize_aliasKeyTBS
  (header_len: asn1_int32)
: serializer (parse_aliasKeyTBS header_len)
= coerce_parser_serializer
    (parse_aliasKeyTBS header_len)
    (serialize_asn1_sequence_TLV (serialize_aliasKeyTBS_payload header_len))
    ()

let lemma_serialize_aliasKeyTBS_unfold
  (header_len: asn1_int32)
  (x: aliasKeyTBS_t header_len)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_aliasKeyTBS_payload header_len) x )
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_aliasKeyTBS_payload header_len) x

let lemma_serialize_aliasKeyTBS_size
  (header_len: asn1_int32)
  (x: aliasKeyTBS_t header_len)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_aliasKeyTBS_payload header_len) x )
= lemma_serialize_asn1_sequence_TLV_size (serialize_aliasKeyTBS_payload header_len) x

#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let length_of_aliasKeyTBS
  (serialNumber: datatype_of_asn1_type INTEGER)
  (header_len: asn1_int32)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER
            { length_of_aliasKeyTBS_payload serialNumber header_len ku version
              <= asn1_value_length_max_of_type SEQUENCE })
: GTot (asn1_TLV_length_of_type SEQUENCE)
= length_of_TLV SEQUENCE (length_of_aliasKeyTBS_payload serialNumber header_len ku version)

let len_of_aliasKeyTBS
  (serialNumber: datatype_of_asn1_type INTEGER)
  (header_len: asn1_int32)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER
            { length_of_aliasKeyTBS_payload serialNumber header_len ku version
              <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_aliasKeyTBS serialNumber header_len ku version })
= len_of_TLV SEQUENCE (len_of_aliasKeyTBS_payload serialNumber header_len ku version)
#pop-options

#restart-solver
#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let lemma_serialize_aliasKeyTBS_size_exact
  (header_len: asn1_int32)
  (x: aliasKeyTBS_t header_len)
: Lemma (
  let riot_version = RIoT.X509.Extension.(x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version) in
  let ku = (snd x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_key_usage) in
  let _ = lemma_serialize_aliasKeyTBS_payload_size header_len x in
  (* exact size *)
  length_of_opaque_serialization (serialize_aliasKeyTBS header_len) x
  == length_of_aliasKeyTBS
       x.aliasKeyTBS_serialNumber
       header_len
       ku
       riot_version
  (* upper bound *)
  // length_of_opaque_serialization (serialize_aliasKeyTBS header_len) x
  // <= (6 + v header_len + 44 + (6 + (6 + 117)))
)
= lemma_serialize_aliasKeyTBS_size header_len x;
    lemma_serialize_aliasKeyTBS_payload_size header_len x
#pop-options


(* low *)
let serialize32_aliasKeyTBS_payload_backwards
  (header_len: asn1_int32)
: serializer32_backwards (serialize_aliasKeyTBS_payload header_len)
= serialize32_synth_backwards
  (* s1 *) (serialize32_x509_version_backwards
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type INTEGER
            `serialize32_nondep_then_backwards`
            serialize32_algorithmIdentifier_backwards
            `serialize32_nondep_then_backwards`
            serialize32_flbytes32_backwards header_len
            `serialize32_nondep_then_backwards`
            serialize32_subjectPublicKeyInfo_backwards
            `serialize32_nondep_then_backwards`
            serialize32_x509_extensions_TLV_backwards serialize32_aliasKeyTBS_extensions_backwards)
  (* f2 *) (synth_aliasKeyTBS_payload_t  header_len)
  (* g1 *) (synth_aliasKeyTBS_payload_t' header_len)
  (* g1'*) (synth_aliasKeyTBS_payload_t' header_len)
  (* prf*) ()

let serialize32_aliasKeyTBS_backwards
  (header_len: asn1_int32)
: serializer32_backwards (serialize_aliasKeyTBS header_len)
= coerce_serializer32_backwards
  (* s2 *) (serialize_aliasKeyTBS header_len)
  (* s32*) (serialize32_asn1_sequence_TLV_backwards
             (serialize32_aliasKeyTBS_payload_backwards header_len))
  (* prf*) ()


(* helpers *)
#restart-solver
#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let x509_get_AliasKeyTBS
  (crt_version: x509_version_t)
  (serialNumber: datatype_of_asn1_type INTEGER)
  (header_len: asn1_int32)
  (aliasKeyTBS_template: B32.lbytes32 header_len)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER
            { length_of_aliasKeyTBS_payload serialNumber header_len ku version
              <= asn1_value_length_max_of_type SEQUENCE })
  (fwid: B32.lbytes32 32ul)
  (deviceIDPub: B32.lbytes32 32ul)
  (aliasKeyPub: B32.lbytes32 32ul)
: Tot (aliasKeyTBS_t header_len)
=
  let signatureAlg = x509_get_algorithmIdentifier () in
  (* Prf *) lemma_serialize_algorithmIdentifier_size_exact signatureAlg;

  let extensions = x509_get_aliasKeyTBS_extensions
                                 ku
                                 version
                                 fwid
                                 deviceIDPub in
  (* Prf *) lemma_serialize_aliasKeyTBS_extensions_size_exact extensions;

  let aliasKeyPubInfo = x509_get_subjectPublicKeyInfo
                           aliasKeyPub in
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_size_exact aliasKeyPubInfo;

  let aliasKeyTBS: aliasKeyTBS_payload_t header_len = {
    aliasKeyTBS_version        = crt_version;
    aliasKeyTBS_serialNumber   = serialNumber;
    aliasKeyTBS_signatureAlg   = signatureAlg;
    aliasKeyTBS_template       = aliasKeyTBS_template;
    aliasKeyTBS_aliasKey_pub   = aliasKeyPubInfo;
    aliasKeyTBS_extensions     = extensions
  } in
  (* Prf *) lemma_serialize_aliasKeyTBS_payload_unfold header_len aliasKeyTBS;
  (* Prf *) lemma_serialize_aliasKeyTBS_payload_size   header_len aliasKeyTBS;
  (* Prf *) (**) lemma_serialize_x509_version_size_exact crt_version;
  (* Prf *) (**) lemma_serialize_asn1_integer_TLV_size serialNumber;
  (* Prf *) (**) lemma_serialize_flbytes32_size header_len aliasKeyTBS.aliasKeyTBS_template;

(*return*) aliasKeyTBS
