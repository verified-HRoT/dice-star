module RIoT.X509.AliasKeyTBS.Extensions

open ASN1.Spec
open ASN1.Low
open X509
open RIoT.X509.Base
open RIoT.X509.FWID
open RIoT.X509.CompositeDeviceID
open RIoT.X509.Extension
open FStar.Integers

module B32 = FStar.Bytes

open LowParse.Spec.SeqBytes.Base
open LowParse.Spec.Bytes

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

(* Extensions of the AliasKey Certificate
 * Includes the RIoT Extension (`CompositeDeviceID`) and others
 * This is the SEQUENCE under the outmost explicit tag
 * Contains SEQUENCEs of individual extensions ({extID, extValue})
 * [3] {               <--- The outmost explicit tag
 *   SEQUENCE {        <--- *HERE*
 *     SEQUENCE {      <--- Individual extension
 *       extID   : OID
 *       extValue: OCTET STRING {..}  <--- Actual extension content enveloped by tag OCTET STRING
 *     };
 *     SEQUENCE {..};
 *     SEQUENCE {..};  <--- Other extensions
 *   }
 * }
 *)

(* Exposed message record type (struct) for manipulation *)
type aliasKeyTBS_extensions_t = {
  (* More extensions could be added here.
   * For example:
   * aliasKeyTBS_extensions_key_usage: key_usage_t;
   *)
  aliasKeyTBS_extensions_key_usage: key_usage_t_inbound;
  aliasKeyTBS_extensions_riot: riot_extension_t_inbound
}

(* The following helpers should be updated accordingly if
 * new extensions are added to the type above
 *)
(* Actual message tuple type for serialization *)
let aliasKeyTBS_extensions_t' = (
  (* More extensions could be added here.
   * For example:
   * key_usage_t &
   *)
  key_usage_t_inbound `tuple2`
  riot_extension_t_inbound
)

(* Conversion of message between record and tuple types *)
let synth_aliasKeyTBS_extensions_t
  (x': aliasKeyTBS_extensions_t')
: GTot (aliasKeyTBS_extensions_t) = {
  (* More extensions could be added here.
   * For example:
   * aliasKeyTBS_extensions_key_usage = fst x;
   *)
   aliasKeyTBS_extensions_key_usage = fst x';
   aliasKeyTBS_extensions_riot      = snd x'
}

let synth_aliasKeyTBS_extensions_t'
  (x: aliasKeyTBS_extensions_t)
: Tot  (x': aliasKeyTBS_extensions_t'
           {x == synth_aliasKeyTBS_extensions_t x'}) = (
  (* More extensions could be added here.
   * For example:
   * x.aliasKeyTBS_extensions_key_usage,
   *)
   x.aliasKeyTBS_extensions_key_usage,
   x.aliasKeyTBS_extensions_riot
)

(* Parser Specification for VALUE *)
let parse_aliasKeyTBS_extensions
: parser _ (aliasKeyTBS_extensions_t)
= parse_x509_key_usage
  `nondep_then`
  parse_riot_extension_sequence_TLV
  `parse_synth`
  synth_aliasKeyTBS_extensions_t

(* Serializer Specification for VALUE *)
let serialize_aliasKeyTBS_extensions
: serializer (parse_aliasKeyTBS_extensions)
= serialize_synth
  (* p1 *) (parse_x509_key_usage
            `nondep_then`
            parse_riot_extension_sequence_TLV)
  (* f2 *) (synth_aliasKeyTBS_extensions_t)
  (* s1 *) (serialize_x509_key_usage
            `serialize_nondep_then`
            serialize_riot_extension_sequence_TLV)
  (* g1 *) (synth_aliasKeyTBS_extensions_t')
  (* prf*) ()

(* Lemmas for serialization *)
let lemma_serialize_aliasKeyTBS_extensions_unfold
  (x: aliasKeyTBS_extensions_t)
: Lemma (
  serialize_aliasKeyTBS_extensions `serialize` x ==
  (serialize_x509_key_usage `serialize` x.aliasKeyTBS_extensions_key_usage)
  `Seq.append`
  (serialize_riot_extension_sequence_TLV `serialize` x.aliasKeyTBS_extensions_riot)
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_x509_key_usage)
  (* s2 *) (serialize_riot_extension_sequence_TLV)
  (* in *) (synth_aliasKeyTBS_extensions_t' x);
  serialize_synth_eq
  (* p1 *) (parse_x509_key_usage
            `nondep_then`
            parse_riot_extension_sequence_TLV)
  (* f2 *) (synth_aliasKeyTBS_extensions_t)
  (* s1 *) (serialize_x509_key_usage
            `serialize_nondep_then`
            serialize_riot_extension_sequence_TLV)
  (* g1 *) (synth_aliasKeyTBS_extensions_t')
  (* prf*) ()
  (* in *) (x)

let length_of_aliasKeyTBS_extensions_payload
    (ku: key_usage_t)
    (version: datatype_of_asn1_type INTEGER)
= length_of_riot_extension version +
  length_of_x509_key_usage ku

let len_of_aliasKeyTBS_extensions_payload
    (ku: key_usage_t)
    (version: datatype_of_asn1_type INTEGER
              { length_of_aliasKeyTBS_extensions_payload ku version
                <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_aliasKeyTBS_extensions_payload ku version })
= len_of_riot_extension version +
  len_of_x509_key_usage ku

#push-options "--query_stats --z3rlimit 64 --fuel 0 --ifuel 0"
let lemma_serialize_aliasKeyTBS_extensions_size
  (x: aliasKeyTBS_extensions_t)
: Lemma (
  (* unfold *)
  length_of_opaque_serialization (serialize_aliasKeyTBS_extensions)      x ==
  length_of_opaque_serialization (serialize_riot_extension_sequence_TLV) x.aliasKeyTBS_extensions_riot +
  length_of_opaque_serialization (serialize_x509_key_usage)              x.aliasKeyTBS_extensions_key_usage /\
  (* exact size of the VALUE of SEQUENCE
   * For now its just the size of the RIoT Extension
   *)
  length_of_opaque_serialization (serialize_aliasKeyTBS_extensions)      x
  == length_of_aliasKeyTBS_extensions_payload
       (snd x.aliasKeyTBS_extensions_key_usage)
       (x.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version)
  (* upper bound *)
  // length_of_opaque_serialization (serialize_aliasKeyTBS_extensions)      x
  // <= 117
)
= lemma_serialize_aliasKeyTBS_extensions_unfold x;
    lemma_serialize_riot_extension_sequence_TLV_size_exact x.aliasKeyTBS_extensions_riot;
    lemma_serialize_x509_key_usage_size_exact x.aliasKeyTBS_extensions_key_usage
#pop-options

(*
 * SEQUENCE serializer
 *)
(* aliasKeyTBS_extensions: inbound sub type for SEQUENCE TLV*)
// unfold
let aliasKeyTBS_extensions_t_inbound
= inbound_sequence_value_of (serialize_aliasKeyTBS_extensions)

(* aliasKeyTBS_extensions: parser for TLV *)
let parse_aliasKeyTBS_extensions_sequence_TLV
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (aliasKeyTBS_extensions_t_inbound)
= aliasKeyTBS_extensions_t_inbound
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_aliasKeyTBS_extensions)

(* aliasKeyTBS_extensions: serializer for TLV *)
let serialize_aliasKeyTBS_extensions_sequence_TLV
: serializer (parse_aliasKeyTBS_extensions_sequence_TLV)
= coerce_parser_serializer
  (* t *) (parse_aliasKeyTBS_extensions_sequence_TLV)
  (* s *) (serialize_asn1_sequence_TLV (serialize_aliasKeyTBS_extensions))
  (*prf*) ()

(* aliasKeyTBS_extensions: lemmas for TLV *)
let lemma_serialize_aliasKeyTBS_extensions_sequence_TLV_unfold
  (x: aliasKeyTBS_extensions_t_inbound)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold serialize_aliasKeyTBS_extensions x )
= lemma_serialize_asn1_sequence_TLV_unfold serialize_aliasKeyTBS_extensions x

let lemma_serialize_aliasKeyTBS_extensions_sequence_TLV_size
  (x: aliasKeyTBS_extensions_t_inbound)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size serialize_aliasKeyTBS_extensions x )
= lemma_serialize_asn1_sequence_TLV_size serialize_aliasKeyTBS_extensions x

let length_of_aliasKeyTBS_extensions
    (ku: key_usage_t)
    (version: datatype_of_asn1_type INTEGER)
: GTot (asn1_TLV_length_of_type SEQUENCE)
= length_of_TLV SEQUENCE
    (length_of_riot_extension version +
     length_of_x509_key_usage ku)

#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let len_of_aliasKeyTBS_extensions
    (ku: key_usage_t)
    (version: datatype_of_asn1_type INTEGER
              { length_of_aliasKeyTBS_extensions ku version
                <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_aliasKeyTBS_extensions ku version })
= len_of_TLV SEQUENCE
    (len_of_riot_extension version +
     len_of_x509_key_usage ku)
#pop-options

#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let lemma_serialize_aliasKeyTBS_extensions_sequence_TLV_size_exact
  (x: aliasKeyTBS_extensions_t_inbound)
: Lemma (
  (* exact size of the VALUE of SEQUENCE
   * For now its just the size of the RIoT Extension
   *)
  length_of_opaque_serialization (serialize_aliasKeyTBS_extensions_sequence_TLV) x
  == length_of_aliasKeyTBS_extensions
       (snd x.aliasKeyTBS_extensions_key_usage)
       (x.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version)
  (* upper bound *)
  // length_of_opaque_serialization (serialize_aliasKeyTBS_extensions_sequence_TLV)      x
  // <= 6 +
  //      117
)
= lemma_serialize_aliasKeyTBS_extensions_sequence_TLV_size x;
  lemma_serialize_aliasKeyTBS_extensions_size x
#pop-options

(*
 * Low Level Serializer
 *)
(* aliasKeyTBS_extensions: low level serializer for VALUE *)
let serialize32_aliasKeyTBS_extensions_backwards
: serializer32_backwards (serialize_aliasKeyTBS_extensions)
= serialize32_synth_backwards
  (* s32 *) (serialize32_x509_key_usage_backwards
             `serialize32_nondep_then_backwards`
             serialize32_riot_extension_sequence_TLV_backwards)
  (* f2  *) synth_aliasKeyTBS_extensions_t
  (* g1  *) synth_aliasKeyTBS_extensions_t'
  (* g1' *) synth_aliasKeyTBS_extensions_t'
  (* prf *) ()

(* aliasKeyTBS_extensions: low level serializer for SEQUENCE TLV *)
let serialize32_aliasKeyTBS_extensions_sequence_TLV_backwards
: serializer32_backwards (serialize_aliasKeyTBS_extensions_sequence_TLV)
= coerce_serializer32_backwards
  (* s2  *) (serialize_aliasKeyTBS_extensions_sequence_TLV)
  (* s32 *) (serialize32_asn1_sequence_TLV_backwards
             (* ls *) (serialize32_aliasKeyTBS_extensions_backwards))
  (* prf *) ()

#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let x509_get_aliasKeyTBS_extensions
  (ku: key_usage_t)
  (version: datatype_of_asn1_type INTEGER
            { length_of_aliasKeyTBS_extensions ku version
              <= asn1_value_length_max_of_type SEQUENCE })
  (fwid: B32.lbytes32 32ul)
  (deviceIDPub: B32.lbytes32 32ul)
: Tot (aliasKeyTBS_extensions_t_inbound)
=
  let riot_extension= x509_get_riot_extension
                        version
                        fwid
                        deviceIDPub in
  (* Prf *) lemma_serialize_riot_extension_sequence_TLV_size_exact riot_extension;

  let key_usage = x509_get_key_usage ku in
  (* Prf *) lemma_serialize_x509_key_usage_size_exact key_usage;

  let aliasKeyTBS_extensions: aliasKeyTBS_extensions_t = {
    aliasKeyTBS_extensions_riot = riot_extension;
    aliasKeyTBS_extensions_key_usage = key_usage
  } in
  (* Prf *) lemma_serialize_aliasKeyTBS_extensions_unfold aliasKeyTBS_extensions;
  (* Prf *) lemma_serialize_aliasKeyTBS_extensions_size   aliasKeyTBS_extensions;
  (* Prf *) assert ( length_of_opaque_serialization serialize_aliasKeyTBS_extensions aliasKeyTBS_extensions
                     <= asn1_value_length_max_of_type SEQUENCE );

(*return*) aliasKeyTBS_extensions
#pop-options
