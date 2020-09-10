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

module T = FStar.Tactics
module P = FStar.Pervasives

(* 4 fuels for the recursively defined 3-oid extendedKeyUsage *)
#set-options "--z3rlimit 64 --fuel 4 --ifuel 0"

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

noextract inline_for_extraction
let aliasKeyCrt_extendedKeyUsage_oids
: l: keyPurposeIDs_oids_t
     { valid_x509_ext_key_usage_ingredients l }
= [@inline_let]
  let l = [OID_AT_CN; OID_AT_COUNTRY; OID_AT_ORGANIZATION] in
  assert_norm (  valid_keyPurposeIDs l  );
  // lemma_serialize_x509_keyPurposeIDs_size_norm l;
  lemma_serialize_x509_keyPurposeIDs_size l;
  l

(* FIXME: Seems postprocess does not work on type indices.
   Potential fixes: 1. separately define a suite of parser/serializer for the normalized type;
                    2. get rid of the record type and just use the internal tuple type. *)
// [@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%aliasKeyCrt_extendedKeyUsage_oids))]
type aliasKeyTBS_extensions_payload_t = {
  (* More extensions could be added here.
   * For example:
   * aliasKeyTBS_extensions_key_usage: key_usage_t;
   *)
  aliasKeyTBS_extensions_key_usage: key_usage_t;
  aliasKeyTBS_extensions_extendedKeyUsage: x509_ext_key_usage_t aliasKeyCrt_extendedKeyUsage_oids;
  // aliasKeyTBS_extensions_extendedKeyUsage: aliasKeyTBS_extensions_extendedKeyUsage_t;
  aliasKeyTBS_extensions_riot: riot_extension_t
}

(* The following helpers should be updated accordingly if
 * new extensions are added to the type above
 *)
(* Actual message tuple type for serialization *)
// [@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%aliasKeyCrt_extendedKeyUsage_oids))]
let aliasKeyTBS_extensions_payload_t' = (
  (* More extensions could be added here.
   * For example:
   * key_usage_t &
   *)
  key_usage_t `tuple2`
  x509_ext_key_usage_t aliasKeyCrt_extendedKeyUsage_oids `tuple2`
  // aliasKeyTBS_extensions_extendedKeyUsage_t `tuple2`
  riot_extension_t
)

(* Conversion of message between record and tuple types *)
let synth_aliasKeyTBS_extensions_payload_t
  (x': aliasKeyTBS_extensions_payload_t')
: GTot (aliasKeyTBS_extensions_payload_t) = {
  (* More extensions could be added here.
   * For example:
   * aliasKeyTBS_extensions_key_usage = fst x;
   *)
   aliasKeyTBS_extensions_key_usage = fst (fst x');
   aliasKeyTBS_extensions_extendedKeyUsage = snd (fst x');
   aliasKeyTBS_extensions_riot      = snd x'
}

let synth_aliasKeyTBS_extensions_payload_t'
  (x: aliasKeyTBS_extensions_payload_t)
: Tot  (x': aliasKeyTBS_extensions_payload_t'
           {x == synth_aliasKeyTBS_extensions_payload_t x'}) = (
  (* More extensions could be added here.
   * For example:
   * x.aliasKeyTBS_extensions_key_usage,
   *)
  (x.aliasKeyTBS_extensions_key_usage,
   x.aliasKeyTBS_extensions_extendedKeyUsage),
   x.aliasKeyTBS_extensions_riot
)

(* Parser Specification for VALUE *)
let parse_aliasKeyTBS_extensions_payload
: parser _ (aliasKeyTBS_extensions_payload_t)
= parse_x509_key_usage
  `nondep_then`
  parse_x509_ext_key_usage aliasKeyCrt_extendedKeyUsage_oids
  `nondep_then`
  parse_riot_extension
  `parse_synth`
  synth_aliasKeyTBS_extensions_payload_t

(* Serializer Specification for VALUE *)
let serialize_aliasKeyTBS_extensions_payload
: serializer (parse_aliasKeyTBS_extensions_payload)
= serialize_synth
  (* p1 *) (parse_x509_key_usage
            `nondep_then`
            parse_x509_ext_key_usage aliasKeyCrt_extendedKeyUsage_oids
            `nondep_then`
            parse_riot_extension)
  (* f2 *) (synth_aliasKeyTBS_extensions_payload_t)
  (* s1 *) (serialize_x509_key_usage
            `serialize_nondep_then`
            serialize_x509_ext_key_usage aliasKeyCrt_extendedKeyUsage_oids
            `serialize_nondep_then`
            serialize_riot_extension)
  (* g1 *) (synth_aliasKeyTBS_extensions_payload_t')
  (* prf*) ()

(* Lemmas for serialization *)
let lemma_serialize_aliasKeyTBS_extensions_payload_unfold
  (x: aliasKeyTBS_extensions_payload_t)
: Lemma (
  serialize_aliasKeyTBS_extensions_payload `serialize` x ==
  (serialize_x509_key_usage `serialize` x.aliasKeyTBS_extensions_key_usage)
  `Seq.append`
  (serialize_x509_ext_key_usage aliasKeyCrt_extendedKeyUsage_oids
                            `serialize` x.aliasKeyTBS_extensions_extendedKeyUsage)
  `Seq.append`
  (serialize_riot_extension `serialize` x.aliasKeyTBS_extensions_riot)
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_x509_key_usage)
  (* s2 *) (serialize_x509_ext_key_usage aliasKeyCrt_extendedKeyUsage_oids)
  (* in *) (fst (synth_aliasKeyTBS_extensions_payload_t' x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_key_usage
            `serialize_nondep_then`
            serialize_x509_ext_key_usage aliasKeyCrt_extendedKeyUsage_oids)
  (* s2 *) (serialize_riot_extension)
  (* in *) (synth_aliasKeyTBS_extensions_payload_t' x);
  serialize_synth_eq
  (* p1 *) (parse_x509_key_usage
            `nondep_then`
            parse_x509_ext_key_usage aliasKeyCrt_extendedKeyUsage_oids
            `nondep_then`
            parse_riot_extension)
  (* f2 *) (synth_aliasKeyTBS_extensions_payload_t)
  (* s1 *) (serialize_x509_key_usage
            `serialize_nondep_then`
            serialize_x509_ext_key_usage aliasKeyCrt_extendedKeyUsage_oids
            `serialize_nondep_then`
            serialize_riot_extension)
  (* g1 *) (synth_aliasKeyTBS_extensions_payload_t')
  (* prf*) ()
  (* in *) (x)

noextract
let length_of_aliasKeyTBS_extensions_payload
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER)
: GTot (nat)
= length_of_riot_extension version +
  length_of_x509_ext_key_usage (aliasKeyCrt_extendedKeyUsage_oids) +
  length_of_x509_key_usage ku

[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%aliasKeyCrt_extendedKeyUsage_oids))]
let len_of_aliasKeyTBS_extensions_payload
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER
            { length_of_aliasKeyTBS_extensions_payload ku version
              <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_aliasKeyTBS_extensions_payload ku version })
= (* Why do we need to proof this? Is this related to the refinement on `len_of_x509_extension`'s `x_len` param? *)
  lemma_serialize_x509_ext_key_usage_payload_size_exact (aliasKeyCrt_extendedKeyUsage_oids);
  len_of_riot_extension version +
  len_of_x509_ext_key_usage (aliasKeyCrt_extendedKeyUsage_oids) +
  len_of_x509_key_usage ku

#restart-solver
#push-options "--z3rlimit 128"
let lemma_serialize_aliasKeyTBS_extensions_payload_size
  (x: aliasKeyTBS_extensions_payload_t)
: Lemma (
  (* unfold *)
  length_of_opaque_serialization (serialize_aliasKeyTBS_extensions_payload)      x ==
  length_of_opaque_serialization (serialize_x509_key_usage)              x.aliasKeyTBS_extensions_key_usage +
  length_of_opaque_serialization (serialize_x509_ext_key_usage aliasKeyCrt_extendedKeyUsage_oids)
                                                                         x.aliasKeyTBS_extensions_extendedKeyUsage +
  length_of_opaque_serialization (serialize_riot_extension)              x.aliasKeyTBS_extensions_riot /\
  (* exact size *)
  length_of_opaque_serialization (serialize_aliasKeyTBS_extensions_payload)      x
  == length_of_aliasKeyTBS_extensions_payload
       (snd x.aliasKeyTBS_extensions_key_usage)
       (x.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version) /\
  True
)
= lemma_serialize_aliasKeyTBS_extensions_payload_unfold x;
    lemma_serialize_x509_key_usage_size_exact x.aliasKeyTBS_extensions_key_usage;
    lemma_x509_keyPurposeIDs_unique aliasKeyCrt_extendedKeyUsage_oids;
    lemma_serialize_x509_ext_key_usage_size_exact aliasKeyCrt_extendedKeyUsage_oids
                                              x.aliasKeyTBS_extensions_extendedKeyUsage;
    lemma_serialize_riot_extension_size_exact x.aliasKeyTBS_extensions_riot;
()
#pop-options

(*
 * SEQUENCE serializer
 *)
(* aliasKeyTBS_extensions: inbound sub type for SEQUENCE TLV*)
let aliasKeyTBS_extensions_t
= inbound_sequence_value_of (serialize_aliasKeyTBS_extensions_payload)

(* aliasKeyTBS_extensions: parser for TLV *)
let parse_aliasKeyTBS_extensions
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (aliasKeyTBS_extensions_t)
= aliasKeyTBS_extensions_t
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_aliasKeyTBS_extensions_payload)

(* aliasKeyTBS_extensions: serializer for TLV *)
let serialize_aliasKeyTBS_extensions
: serializer (parse_aliasKeyTBS_extensions)
= coerce_parser_serializer
  (* t *) (parse_aliasKeyTBS_extensions)
  (* s *) (serialize_asn1_sequence_TLV (serialize_aliasKeyTBS_extensions_payload))
  (*prf*) ()

(* aliasKeyTBS_extensions: lemmas for TLV *)
let lemma_serialize_aliasKeyTBS_extensions_unfold
  (x: aliasKeyTBS_extensions_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold serialize_aliasKeyTBS_extensions_payload x )
= lemma_serialize_asn1_sequence_TLV_unfold serialize_aliasKeyTBS_extensions_payload x

let lemma_serialize_aliasKeyTBS_extensions_size
  (x: aliasKeyTBS_extensions_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size serialize_aliasKeyTBS_extensions_payload x )
= lemma_serialize_asn1_sequence_TLV_size serialize_aliasKeyTBS_extensions_payload x

let valid_aliasKeyTBS_ingredients
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER)
: Type0
= length_of_aliasKeyTBS_extensions_payload ku version
  <= asn1_value_length_max_of_type SEQUENCE

#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let length_of_aliasKeyTBS_extensions
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER
            { valid_aliasKeyTBS_ingredients ku version })
: GTot (asn1_TLV_length_of_type SEQUENCE)
= length_of_TLV SEQUENCE
    (length_of_aliasKeyTBS_extensions_payload ku version)

let len_of_aliasKeyTBS_extensions
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER
            { valid_aliasKeyTBS_ingredients ku version })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_aliasKeyTBS_extensions ku version })
= len_of_TLV SEQUENCE
    (len_of_aliasKeyTBS_extensions_payload ku version)
#pop-options

let lemma_serialize_aliasKeyTBS_extensions_size_exact
  (x: aliasKeyTBS_extensions_t
      { valid_aliasKeyTBS_ingredients
          (snd x.aliasKeyTBS_extensions_key_usage)
          (x.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version) })
: Lemma (
  (* exact size *)
  length_of_opaque_serialization (serialize_aliasKeyTBS_extensions) x
  == length_of_aliasKeyTBS_extensions
       (snd x.aliasKeyTBS_extensions_key_usage)
       (x.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version)
)
= lemma_serialize_aliasKeyTBS_extensions_size x;
  lemma_serialize_aliasKeyTBS_extensions_payload_size x;
()


(*
 * Low Level Serializer
 *)
(* aliasKeyTBS_extensions: low level serializer for VALUE *)
[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%aliasKeyCrt_extendedKeyUsage_oids))]
let serialize32_aliasKeyTBS_extensions_payload_backwards
: serializer32_backwards (serialize_aliasKeyTBS_extensions_payload)
= serialize32_synth_backwards
  (* s32 *) (serialize32_x509_key_usage_backwards
             `serialize32_nondep_then_backwards`
             serialize32_x509_ext_key_usage_backwards aliasKeyCrt_extendedKeyUsage_oids
             `serialize32_nondep_then_backwards`
             serialize32_riot_extension_backwards)
  (* f2  *) synth_aliasKeyTBS_extensions_payload_t
  (* g1  *) synth_aliasKeyTBS_extensions_payload_t'
  (* g1' *) synth_aliasKeyTBS_extensions_payload_t'
  (* prf *) ()

(* aliasKeyTBS_extensions: low level serializer for SEQUENCE TLV *)
let serialize32_aliasKeyTBS_extensions_backwards
: serializer32_backwards (serialize_aliasKeyTBS_extensions)
= coerce_serializer32_backwards
  (* s2  *) (serialize_aliasKeyTBS_extensions)
  (* s32 *) (serialize32_asn1_sequence_TLV_backwards
             (* ls *) (serialize32_aliasKeyTBS_extensions_payload_backwards))
  (* prf *) ()

#restart-solver
#push-options "--z3rlimit 256 --fuel 4 --ifuel 0"
[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%aliasKeyCrt_extendedKeyUsage_oids))]
let x509_get_aliasKeyTBS_extensions
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER
            { length_of_aliasKeyTBS_extensions ku version
              <= asn1_value_length_max_of_type SEQUENCE })
  (fwid: B32.lbytes32 32ul)
  (deviceIDPub: B32.lbytes32 32ul)
: Tot (aliasKeyTBS_extensions_t)
=
  let key_usage = x509_get_key_usage ku in
  (* Prf *) lemma_serialize_x509_key_usage_size_exact key_usage;

  let extendedKeyUsage = x509_get_ext_extendedKeyUsage
                           aliasKeyCrt_extendedKeyUsage_oids
                           (*TODO: FIXME: Maybe move criticality to params *) true in
  (* Prf *) lemma_serialize_x509_ext_key_usage_size_exact aliasKeyCrt_extendedKeyUsage_oids extendedKeyUsage;

  let riot_extension= x509_get_riot_extension
                        version
                        fwid
                        deviceIDPub in
  (* Prf *) lemma_serialize_riot_extension_size_exact riot_extension;

  let aliasKeyTBS_extensions: aliasKeyTBS_extensions_payload_t = {
    aliasKeyTBS_extensions_key_usage = key_usage;
    aliasKeyTBS_extensions_extendedKeyUsage = extendedKeyUsage;
    aliasKeyTBS_extensions_riot = riot_extension
  } in
  (* Prf *) lemma_serialize_aliasKeyTBS_extensions_payload_unfold aliasKeyTBS_extensions;
  (* Prf *) lemma_serialize_aliasKeyTBS_extensions_payload_size   aliasKeyTBS_extensions;
  (* Prf *) assert ( length_of_opaque_serialization serialize_aliasKeyTBS_extensions_payload aliasKeyTBS_extensions
                     <= asn1_value_length_max_of_type SEQUENCE );

(*return*) aliasKeyTBS_extensions
#pop-options
