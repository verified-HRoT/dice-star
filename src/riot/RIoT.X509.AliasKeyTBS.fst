module RIoT.X509.AliasKeyTBS

open ASN1.Spec
open ASN1.Low
open X509
include RIoT.X509.Base
include RIoT.X509.FWID
include RIoT.X509.CompositeDeviceID
include RIoT.X509.Extension
open FStar.Integers

module B32 = FStar.Bytes

open LowParse.Spec.SeqBytes.Base
open LowParse.Spec.Bytes

(* Explicit tag [3] of
 *   SEQUENCE of
 *     SEQUENCE of
 *       ...
 *       OCTET STRING of
 *         ...
 *)

// let aliasKeyTBS_extensions_t_inbound
// = CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 3uy
//   `inbound_envelop_tag_with_value_of`
//   (serialize_asn1_sequence_TLV
//      (serialize_asn1_sequence_TLV serialize_riot_extension_sequence_TLV))

type aliasKeyTBS_t (header_len: asn1_int32) = {
  aliasKeyTBS_template: B32.lbytes32 header_len;
  aliasKeyTBS_aliasKey_pub: subjectPublicKeyInfo_t_inbound;
  aliasKeyTBS_riot_extension: riot_extension_t_inbound
}

let aliasKeyTBS_t' (header_len: asn1_int32) = (
  (B32.lbytes32 header_len `tuple2`
   subjectPublicKeyInfo_t_inbound) `tuple2`
   riot_extension_t_inbound
)

let synth_aliasKeyTBS_t
  (header_len: asn1_int32)
  (x': aliasKeyTBS_t' header_len)
: GTot (aliasKeyTBS_t header_len)
= { aliasKeyTBS_template       = fst (fst x');
    aliasKeyTBS_aliasKey_pub   = snd (fst x');
    aliasKeyTBS_riot_extension = snd x' }

let synth_aliasKeyTBS_t'
  (header_len: asn1_int32)
  (x: aliasKeyTBS_t header_len)
: Tot (x': aliasKeyTBS_t' header_len { x == synth_aliasKeyTBS_t header_len x' })
= (x.aliasKeyTBS_template,
   x.aliasKeyTBS_aliasKey_pub),
   x.aliasKeyTBS_riot_extension

let parse_aliasKeyTBS
  (header_len: asn1_int32)
: parser _ (aliasKeyTBS_t header_len)
= parse_flbytes32 header_len
  `nondep_then`
  parse_subjectPublicKeyInfo_sequence_TLV
  `nondep_then`
  parse_riot_extension_sequence_TLV
  `parse_synth`
  synth_aliasKeyTBS_t header_len

let serialize_aliasKeyTBS
  (header_len: asn1_int32)
: serializer (parse_aliasKeyTBS header_len)
= serialize_synth
  (* p1 *) (parse_flbytes32 header_len
            `nondep_then`
            parse_subjectPublicKeyInfo_sequence_TLV
            `nondep_then`
            parse_riot_extension_sequence_TLV)
  (* f2 *) (synth_aliasKeyTBS_t header_len)
  (* s1 *) (serialize_flbytes32 header_len
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo_sequence_TLV
            `serialize_nondep_then`
            serialize_riot_extension_sequence_TLV)
  (* g1 *) (synth_aliasKeyTBS_t' header_len)
  (* prf*) ()

let lemma_serialize_aliasKeyTBS_unfold
  (header_len: asn1_int32)
  (x: aliasKeyTBS_t header_len)
: Lemma (
  serialize_aliasKeyTBS header_len `serialize` x ==
 (serialize_flbytes32 header_len `serialize` x.aliasKeyTBS_template)
  `Seq.append`
 (serialize_subjectPublicKeyInfo_sequence_TLV `serialize` x.aliasKeyTBS_aliasKey_pub)
  `Seq.append`
 (serialize_riot_extension_sequence_TLV `serialize` x.aliasKeyTBS_riot_extension)
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_flbytes32 header_len)
  (* s2 *) (serialize_subjectPublicKeyInfo_sequence_TLV)
  (* in *) (fst (synth_aliasKeyTBS_t' header_len x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_flbytes32 header_len
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo_sequence_TLV)
  (* s2 *) (serialize_riot_extension_sequence_TLV)
  (* in *) (synth_aliasKeyTBS_t' header_len x);
  serialize_synth_eq
  (* p1 *) (parse_flbytes32 header_len
            `nondep_then`
            parse_subjectPublicKeyInfo_sequence_TLV
            `nondep_then`
            parse_riot_extension_sequence_TLV)
  (* f2 *) (synth_aliasKeyTBS_t header_len)
  (* s1 *) (serialize_flbytes32 header_len
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo_sequence_TLV
            `serialize_nondep_then`
            serialize_riot_extension_sequence_TLV)
  (* g1 *) (synth_aliasKeyTBS_t' header_len)
  (* prf*) ()
  (* in *) x

#restart-solver
#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let lemma_serialize_aliasKeyTBS_size
  (header_len: asn1_int32)
  (x: aliasKeyTBS_t header_len)
: Lemma (
  (* unfold *)
  length_of_opaque_serialization (serialize_aliasKeyTBS header_len) x ==
  length_of_opaque_serialization (serialize_flbytes32 header_len) x.aliasKeyTBS_template +
  length_of_opaque_serialization (serialize_subjectPublicKeyInfo_sequence_TLV) x.aliasKeyTBS_aliasKey_pub +
  length_of_opaque_serialization (serialize_riot_extension_sequence_TLV) x.aliasKeyTBS_riot_extension /\
  (* exact size *)
  length_of_opaque_serialization (serialize_aliasKeyTBS header_len) x
  == v header_len + length_of_asn1_primitive_TLV x.aliasKeyTBS_riot_extension.x509_extValue_riot.riot_version + 155 /\
  // == v header_len + 44 /\
  (* upper bound *)
  length_of_opaque_serialization (serialize_aliasKeyTBS header_len) x
  <= v header_len + 161
  // <= v header_len + 44
)
= lemma_serialize_aliasKeyTBS_unfold header_len x;
    lemma_serialize_subjectPublicKeyInfo_sequence_TLV_size_exact x.aliasKeyTBS_aliasKey_pub;
    lemma_serialize_riot_extension_sequence_TLV_size_exact x.aliasKeyTBS_riot_extension
#pop-options

// unfold
let aliasKeyTBS_t_inbound
  (header_len: asn1_int32)
= inbound_sequence_value_of (serialize_aliasKeyTBS header_len)

let parse_aliasKeyTBS_sequence_TLV
  (header_len: asn1_int32)
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (aliasKeyTBS_t_inbound header_len)
=
  aliasKeyTBS_t_inbound header_len
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_aliasKeyTBS header_len)

let serialize_aliasKeyTBS_sequence_TLV
  (header_len: asn1_int32)
: serializer (parse_aliasKeyTBS_sequence_TLV header_len)
= coerce_parser_serializer
    (parse_aliasKeyTBS_sequence_TLV header_len)
    (serialize_asn1_sequence_TLV (serialize_aliasKeyTBS header_len))
    ()

let lemma_serialize_aliasKeyTBS_sequence_TLV_unfold
  (header_len: asn1_int32)
  (x: aliasKeyTBS_t_inbound header_len)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_aliasKeyTBS header_len) x )
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_aliasKeyTBS header_len) x

let lemma_serialize_aliasKeyTBS_sequence_TLV_size
  (header_len: asn1_int32)
  (x: aliasKeyTBS_t_inbound header_len)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_aliasKeyTBS header_len) x )
= lemma_serialize_asn1_sequence_TLV_size (serialize_aliasKeyTBS header_len) x

#restart-solver
#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let lemma_serialize_aliasKeyTBS_sequence_TLV_size_exact
  (header_len: asn1_int32)
  (x: aliasKeyTBS_t_inbound header_len)
: Lemma (
  let length = v header_len + length_of_asn1_primitive_TLV x.aliasKeyTBS_riot_extension.x509_extValue_riot.riot_version + 155 in
  // let length = v header_len + 44 in
  length == length_of_opaque_serialization (serialize_aliasKeyTBS header_len) x /\
  (* exact size *)
  length_of_opaque_serialization (serialize_aliasKeyTBS_sequence_TLV header_len) x
  == v header_len + length_of_asn1_primitive_TLV x.aliasKeyTBS_riot_extension.x509_extValue_riot.riot_version + 156 +
     length_of_asn1_length (u length) /\
  // == v header_len + 45 +
  //    length_of_asn1_length (u length)
  (* upper bound *)
  length_of_opaque_serialization (serialize_aliasKeyTBS_sequence_TLV header_len) x
  <= v header_len + 167
)
= lemma_serialize_aliasKeyTBS_sequence_TLV_size header_len x;
    lemma_serialize_aliasKeyTBS_size header_len x
#pop-options

(* low *)

let serialize32_aliasKeyTBS_backwards
  (header_len: asn1_int32)
: serializer32_backwards (serialize_aliasKeyTBS header_len)
= serialize32_synth_backwards
  (* s1 *) (serialize32_flbytes32_backwards header_len
            `serialize32_nondep_then_backwards`
            serialize32_subjectPublicKeyInfo_sequence_TLV_backwards
            `serialize32_nondep_then_backwards`
            serialize32_riot_extension_sequence_TLV_backwards)
  (* f2 *) (synth_aliasKeyTBS_t  header_len)
  (* g1 *) (synth_aliasKeyTBS_t' header_len)
  (* g1'*) (synth_aliasKeyTBS_t' header_len)
  (* prf*) ()

let serialize32_aliasKeyTBS_sequence_TLV_backwards
  (header_len: asn1_int32)
: serializer32_backwards (serialize_aliasKeyTBS_sequence_TLV header_len)
= coerce_serializer32_backwards
  (* s2 *) (serialize_aliasKeyTBS_sequence_TLV header_len)
  (* s32*) (serialize32_asn1_sequence_TLV_backwards
             (serialize32_aliasKeyTBS_backwards header_len))
  (* prf*) ()


(* helpers *)

#restart-solver
#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
let x509_get_AliasKeyTBS
  (header_len: asn1_int32)
  (aliasKeyTBS_template: B32.lbytes32 header_len)
  (version: datatype_of_asn1_type INTEGER
            { v header_len + length_of_asn1_primitive_TLV version + 155
             <= asn1_value_length_max_of_type SEQUENCE })
  (fwid: B32.lbytes32 32ul)
  (deviceIDPub: B32.lbytes32 32ul)
  (aliasKeyPub: B32.lbytes32 32ul)
: Tot (aliasKeyTBS_t_inbound header_len)
=
  let riot_extension= x509_get_riot_extension
                        version
                        fwid
                        deviceIDPub in
  (* Prf *) lemma_serialize_riot_extension_sequence_TLV_size_exact riot_extension;

  let aliasKeyPubInfo = x509_get_subjectPublicKeyInfo
                           aliasKeyPub in
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_sequence_TLV_size_exact aliasKeyPubInfo;

  let aliasKeyTBS: aliasKeyTBS_t header_len = {
    aliasKeyTBS_template       = aliasKeyTBS_template;
    aliasKeyTBS_aliasKey_pub   = aliasKeyPubInfo;
    aliasKeyTBS_riot_extension = riot_extension
  } in
  (* Prf *) lemma_serialize_aliasKeyTBS_unfold header_len aliasKeyTBS;
  (* Prf *) lemma_serialize_aliasKeyTBS_size   header_len aliasKeyTBS;
  (* Prf *) (**) lemma_serialize_flbytes32_size header_len aliasKeyTBS.aliasKeyTBS_template;

(*return*) aliasKeyTBS

unfold
let length_of_AliasKeyTBS_payload
  (header_len: asn1_int32)
  (version: datatype_of_asn1_type INTEGER
            { v header_len + length_of_asn1_primitive_TLV version + 155
              <= asn1_value_length_max_of_type SEQUENCE })
: GTot (asn1_value_length_of_type SEQUENCE)
= v header_len + length_of_asn1_primitive_TLV version + 155
// = v header_len + 44

unfold
let len_of_AliasKeyTBS_payload
  (header_len: asn1_int32)
  (version: datatype_of_asn1_type INTEGER
            { v header_len + length_of_asn1_primitive_TLV version + 155
              <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_value_int32_of_type SEQUENCE
             { v len == length_of_AliasKeyTBS_payload header_len version })
= header_len + len_of_asn1_primitive_TLV version + 155ul
// = header_len + 44ul

unfold
let length_of_AliasKeyTBS
  (header_len: asn1_int32)
  (version: datatype_of_asn1_type INTEGER
            { v header_len + length_of_asn1_primitive_TLV version + 155
              <= asn1_value_length_max_of_type SEQUENCE })
: GTot (asn1_TLV_length_of_type SEQUENCE)
= 1 +
  length_of_asn1_length (u (length_of_AliasKeyTBS_payload header_len version)) +
  length_of_AliasKeyTBS_payload header_len version

unfold
let len_of_AliasKeyTBS
  (header_len: asn1_int32)
  (version: datatype_of_asn1_type INTEGER
            { v header_len + length_of_asn1_primitive_TLV version + 155
              <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_AliasKeyTBS header_len version })
= 1ul +
  len_of_asn1_length (len_of_AliasKeyTBS_payload header_len version) +
  len_of_AliasKeyTBS_payload header_len version
#pop-options
