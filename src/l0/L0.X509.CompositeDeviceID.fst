module L0.X509.CompositeDeviceID

open LowParse.Low.Base
open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

open X509.Base
open X509.BasicFields.SubjectPublicKeyInfo
open X509.Crypto
open L0.X509.Base
open L0.X509.FWID

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

#set-options "--__temp_no_proj L0.X509.CompositeDeviceID"

let decl = ()

(* CompositeDeviceID *)

let compositeDeviceID_payload_t'
= ((datatype_of_asn1_type INTEGER &
    subjectPublicKeyInfo_t) &
    fwid_t)

(* Serialier spec *)
let synth_compositeDeviceID_payload_t
  (x': compositeDeviceID_payload_t')
: GTot (compositeDeviceID_payload_t)
= { l0_version  = fst (fst x');
    l0_deviceID = snd (fst x');
    l0_fwid     = snd x' }

inline_for_extraction noextract
let synth_compositeDeviceID_payload_t'
  (x: compositeDeviceID_payload_t)
: Tot (x': compositeDeviceID_payload_t' { x == synth_compositeDeviceID_payload_t x' })
= ((x.l0_version, x.l0_deviceID), x.l0_fwid)

let parse_compositeDeviceID_payload
= parse_asn1_TLV_of_type INTEGER
  `nondep_then`
  parse_subjectPublicKeyInfo
  `nondep_then`
  parse_fwid
  `parse_synth`
  synth_compositeDeviceID_payload_t

let serialize_compositeDeviceID_payload
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type INTEGER
            `nondep_then`
            parse_subjectPublicKeyInfo
            `nondep_then`
            parse_fwid)
  (* f2 *) (synth_compositeDeviceID_payload_t)
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo
            `serialize_nondep_then`
            serialize_fwid)
  (* g1 *) (synth_compositeDeviceID_payload_t')
  (* prf*) ()

let lemma_serialize_compositeDeviceID_payload_unfold x
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER)
  (* s2 *) (serialize_subjectPublicKeyInfo)
  (* in *) (fst (synth_compositeDeviceID_payload_t' x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo)
  (* s2 *) (serialize_fwid)
  (* in *) (synth_compositeDeviceID_payload_t' x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type INTEGER
            `nondep_then`
            parse_subjectPublicKeyInfo
            `nondep_then`
            parse_fwid)
  (* f2 *) (synth_compositeDeviceID_payload_t)
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo
            `serialize_nondep_then`
            serialize_fwid)
  (* g1 *) (synth_compositeDeviceID_payload_t')
  (* prf*) ()
  (* in *) x

let lemma_serialize_compositeDeviceID_payload_size x
= lemma_serialize_compositeDeviceID_payload_unfold x;
    lemma_serialize_subjectPublicKeyInfo_size_exact x.l0_deviceID;
    lemma_serialize_fwid_size_exact x.l0_fwid

(* inbound sub type*)

let lemma_serialize_compositeDeviceID_unfold x
= lemma_serialize_asn1_sequence_TLV_unfold serialize_compositeDeviceID_payload x

let lemma_serialize_compositeDeviceID_size x
= lemma_serialize_asn1_sequence_TLV_size serialize_compositeDeviceID_payload x

open FStar.Integers
let lemma_serialize_compositeDeviceID_size_exact x
= lemma_serialize_compositeDeviceID_unfold x;
  lemma_serialize_compositeDeviceID_size   x;
    lemma_serialize_compositeDeviceID_payload_size x

let serialize32_compositeDeviceID_payload_backwards
= serialize32_synth_backwards
  (* ls *) (serialize32_asn1_TLV_backwards_of_type INTEGER
            `serialize32_nondep_then_backwards`
            serialize32_subjectPublicKeyInfo_backwards
            `serialize32_nondep_then_backwards`
            serialize32_fwid_backwards)
  (* f2 *) (synth_compositeDeviceID_payload_t)
  (* g1 *) (synth_compositeDeviceID_payload_t')
  (* g1'*) (synth_compositeDeviceID_payload_t')
  (* prf*) ()

let serialize32_compositeDeviceID_backwards
= coerce_serializer32_backwards
  (* s2  *) (serialize_compositeDeviceID)
  (* s32 *) (serialize32_asn1_sequence_TLV_backwards
             (* ls *) (serialize32_compositeDeviceID_payload_backwards))
  (* prf *) ()
