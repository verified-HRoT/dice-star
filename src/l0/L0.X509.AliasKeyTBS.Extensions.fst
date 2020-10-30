module RIoT.X509.AliasKeyTBS.Extensions

open ASN1.Spec
open ASN1.Low
open X509
open RIoT.X509.Base
open RIoT.X509.FWID
open RIoT.X509.CompositeDeviceID
open RIoT.X509.Extension
open RIoT.X509.AliasKeyTBS.Extensions.BasicConstraints
open RIoT.X509.AliasKeyTBS.Extensions.AuthKeyIdentifier
open RIoT.X509.AliasKeyTBS.Extensions.ExtendedKeyUsage
open FStar.Integers

module B32 = FStar.Bytes

module T = FStar.Tactics
module P = FStar.Pervasives

#set-options "--z3rlimit 128 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

#set-options "--__temp_no_proj RIoT.X509.AliasKeyTBS.Extensions"

let decl = ()


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
  aliasKeyTBS_extensions_extendedKeyUsage_t `tuple2`
  aliasKeyTBS_extensions_basicConstraints_t `tuple2`
  aliasKeyTBS_extensions_authKeyID_t `tuple2`
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
   aliasKeyTBS_extensions_key_usage        = fst (fst (fst (fst x')));
   aliasKeyTBS_extensions_extendedKeyUsage = snd (fst (fst (fst x')));
   aliasKeyTBS_extensions_basicConstraints = snd (fst (fst x'));
   aliasKeyTBS_extensions_authKeyID        = snd (fst x');
   aliasKeyTBS_extensions_riot             = snd x';
}

inline_for_extraction noextract
let synth_aliasKeyTBS_extensions_payload_t'
  (x: aliasKeyTBS_extensions_payload_t)
: Tot  (x': aliasKeyTBS_extensions_payload_t'
           {x == synth_aliasKeyTBS_extensions_payload_t x'}) = (
  (* More extensions could be added here.
   * For example:
   * x.aliasKeyTBS_extensions_key_usage,
   *)
  (((x.aliasKeyTBS_extensions_key_usage,
     x.aliasKeyTBS_extensions_extendedKeyUsage),
     x.aliasKeyTBS_extensions_basicConstraints),
     x.aliasKeyTBS_extensions_authKeyID),
     x.aliasKeyTBS_extensions_riot
)

(* Parser Specification for VALUE *)
let parse_aliasKeyTBS_extensions_payload
= parse_x509_key_usage
  `nondep_then`
  parse_aliasKeyTBS_extensions_extendedKeyUsage
  `nondep_then`
  parse_aliasKeyTBS_extensions_basicConstraints
  `nondep_then`
  parse_aliasKeyTBS_extensions_authKeyID
  `nondep_then`
  parse_riot_extension
  `parse_synth`
  synth_aliasKeyTBS_extensions_payload_t

(* Serializer Specification for VALUE *)
let serialize_aliasKeyTBS_extensions_payload
= serialize_synth
  (* p1 *) (parse_x509_key_usage
            `nondep_then`
            parse_aliasKeyTBS_extensions_extendedKeyUsage
            `nondep_then`
            parse_aliasKeyTBS_extensions_basicConstraints
            `nondep_then`
            parse_aliasKeyTBS_extensions_authKeyID
            `nondep_then`
            parse_riot_extension)
  (* f2 *) (synth_aliasKeyTBS_extensions_payload_t)
  (* s1 *) (serialize_x509_key_usage
            `serialize_nondep_then`
            serialize_aliasKeyTBS_extensions_extendedKeyUsage
            `serialize_nondep_then`
            serialize_aliasKeyTBS_extensions_basicConstraints
            `serialize_nondep_then`
            serialize_aliasKeyTBS_extensions_authKeyID
            `serialize_nondep_then`
            serialize_riot_extension)
  (* g1 *) (synth_aliasKeyTBS_extensions_payload_t')
  (* prf*) ()

(* Lemmas for serialization *)
let lemma_serialize_aliasKeyTBS_extensions_payload_unfold x
=
  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_key_usage)
  (* s2 *) (serialize_aliasKeyTBS_extensions_extendedKeyUsage)
  (* in *) (fst (fst (fst (synth_aliasKeyTBS_extensions_payload_t' x))));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_key_usage
            `serialize_nondep_then`
            serialize_aliasKeyTBS_extensions_extendedKeyUsage)
  (* s2 *) (serialize_aliasKeyTBS_extensions_basicConstraints)
  (* in *) (fst (fst (synth_aliasKeyTBS_extensions_payload_t' x)));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_key_usage
            `serialize_nondep_then`
            serialize_aliasKeyTBS_extensions_extendedKeyUsage
            `serialize_nondep_then`
            serialize_aliasKeyTBS_extensions_basicConstraints)
  (* s2 *) (serialize_aliasKeyTBS_extensions_authKeyID)
  (* in *) (fst (synth_aliasKeyTBS_extensions_payload_t' x));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_key_usage
            `serialize_nondep_then`
            serialize_aliasKeyTBS_extensions_extendedKeyUsage
            `serialize_nondep_then`
            serialize_aliasKeyTBS_extensions_basicConstraints
            `serialize_nondep_then`
            serialize_aliasKeyTBS_extensions_authKeyID)
  (* s2 *) (serialize_riot_extension)
  (* in *) (synth_aliasKeyTBS_extensions_payload_t' x);

  serialize_synth_eq
  (* p1 *) (parse_x509_key_usage
            `nondep_then`
            parse_aliasKeyTBS_extensions_extendedKeyUsage
            `nondep_then`
            parse_aliasKeyTBS_extensions_basicConstraints
            `nondep_then`
            parse_aliasKeyTBS_extensions_authKeyID
            `nondep_then`
            parse_riot_extension)
  (* f2 *) (synth_aliasKeyTBS_extensions_payload_t)
  (* s1 *) (serialize_x509_key_usage
            `serialize_nondep_then`
            serialize_aliasKeyTBS_extensions_extendedKeyUsage
            `serialize_nondep_then`
            serialize_aliasKeyTBS_extensions_basicConstraints
            `serialize_nondep_then`
            serialize_aliasKeyTBS_extensions_authKeyID
            `serialize_nondep_then`
            serialize_riot_extension)
  (* g1 *) (synth_aliasKeyTBS_extensions_payload_t')
  (* prf*) ()
  (* in *) (x)

let lemma_serialize_aliasKeyTBS_extensions_payload_size x
= lemma_serialize_aliasKeyTBS_extensions_payload_unfold x;
    lemma_serialize_x509_key_usage_size_exact x.aliasKeyTBS_extensions_key_usage;
    lemma_x509_keyPurposeIDs_unique aliasKeyCrt_extendedKeyUsage_oids;
    lemma_serialize_aliasKeyTBS_extensions_extendedKeyUsage_size_exact
                                              x.aliasKeyTBS_extensions_extendedKeyUsage;
    lemma_serialize_aliasKeyTBS_extensions_basicConstraints_size_exact
                                              x.aliasKeyTBS_extensions_basicConstraints;
    lemma_serialize_aliasKeyTBS_extensions_authKeyID_size_exact
                                              x.aliasKeyTBS_extensions_authKeyID;
    lemma_serialize_riot_extension_size_exact x.aliasKeyTBS_extensions_riot;
  lemma_length_of_aliasKeyTBS_extensions_payload_size_max x.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version


(*
 * SEQUENCE serializer
 *)
(* aliasKeyTBS_extensions: lemmas for TLV *)
let lemma_serialize_aliasKeyTBS_extensions_unfold x
= lemma_serialize_asn1_sequence_TLV_unfold serialize_aliasKeyTBS_extensions_payload x

let lemma_serialize_aliasKeyTBS_extensions_size x
= lemma_serialize_asn1_sequence_TLV_size serialize_aliasKeyTBS_extensions_payload x

// #push-options "--z3rlimit 256 --fuel 0"
// let lemma_aliasKeyTBS_extensions_ingredients_valid
//   (ku: key_usage_payload_t)
//   (keyID: datatype_of_asn1_type OCTET_STRING)
//   (version: datatype_of_asn1_type INTEGER)
// : Lemma (
//   valid_aliasKeyTBS_extensions_ingredients
//     (ku)
//     (version)
// )
// =
//   // P.norm_spec
//   //   (norm_steps_x509_keyPurposeIDs (`%aliasKeyCrt_extendedKeyUsage_oids))
//   //   (length_of_x509_keyPurposeIDs aliasKeyCrt_extendedKeyUsage_oids);
// ()
// #pop-options

let lemma_serialize_aliasKeyTBS_extensions_size_exact x
= //Classical.forall_intro lemma_aliasKeyTBS_extensions_ingredients_valid;
  lemma_serialize_aliasKeyTBS_extensions_size x;
  lemma_serialize_aliasKeyTBS_extensions_payload_size x;
()


(*
 * Low Level Serializer
 *)
(* aliasKeyTBS_extensions: low level serializer for VALUE *)
// [@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%aliasKeyCrt_extendedKeyUsage_oids))]
let serialize32_aliasKeyTBS_extensions_payload_backwards
= serialize32_synth_backwards
  (* s32 *) (serialize32_x509_key_usage_backwards
             `serialize32_nondep_then_backwards`
             serialize32_aliasKeyTBS_extensions_extendedKeyUsage_backwards
             `serialize32_nondep_then_backwards`
             serialize32_aliasKeyTBS_extensions_basicConstraints_backwards
             `serialize32_nondep_then_backwards`
             serialize32_aliasKeyTBS_extensions_authKeyID_backwards
             `serialize32_nondep_then_backwards`
             serialize32_riot_extension_backwards)
  (* f2  *) synth_aliasKeyTBS_extensions_payload_t
  (* g1  *) synth_aliasKeyTBS_extensions_payload_t'
  (* g1' *) synth_aliasKeyTBS_extensions_payload_t'
  (* prf *) ()

(* aliasKeyTBS_extensions: low level serializer for SEQUENCE TLV *)
let serialize32_aliasKeyTBS_extensions_backwards
= coerce_serializer32_backwards
  (* s2  *) (serialize_aliasKeyTBS_extensions)
  (* s32 *) (serialize32_asn1_sequence_TLV_backwards
             (* ls *) (serialize32_aliasKeyTBS_extensions_payload_backwards))
  (* prf *) ()
