module RIoT.X509.CompositeDeviceID

open LowParse.Low.Base
open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

open X509.Base
open X509.BasicFields.SubjectPublicKeyInfo
open X509.Crypto
open RIoT.X509.Base
open RIoT.X509.FWID

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

(* CompositeDeviceID *)
type compositeDeviceID_payload_t
= { riot_version : datatype_of_asn1_type INTEGER;
    riot_deviceID: subjectPublicKeyInfo_t;
    riot_fwid    : fwid_t }

let compositeDeviceID_payload_t'
= ((datatype_of_asn1_type INTEGER &
    subjectPublicKeyInfo_t) &
    fwid_t)

(* Serialier spec *)
let synth_compositeDeviceID_payload_t
  (x': compositeDeviceID_payload_t')
: GTot (compositeDeviceID_payload_t)
= { riot_version  = fst (fst x');
    riot_deviceID = snd (fst x');
    riot_fwid     = snd x' }

let synth_compositeDeviceID_payload_t'
  (x: compositeDeviceID_payload_t)
: Tot (x': compositeDeviceID_payload_t' { x == synth_compositeDeviceID_payload_t x' })
= ((x.riot_version, x.riot_deviceID), x.riot_fwid)

let parse_compositeDeviceID_payload
: parser _ (compositeDeviceID_payload_t)
= parse_asn1_TLV_of_type INTEGER
  `nondep_then`
  parse_subjectPublicKeyInfo
  `nondep_then`
  parse_fwid
  `parse_synth`
  synth_compositeDeviceID_payload_t

let serialize_compositeDeviceID_payload
: serializer (parse_compositeDeviceID_payload)
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

let lemma_serialize_compositeDeviceID_payload_unfold
  (x: compositeDeviceID_payload_t)
: Lemma (
  serialize (serialize_compositeDeviceID_payload) x ==
  serialize (serialize_asn1_TLV_of_type INTEGER) x.riot_version
  `Seq.append`
  serialize (serialize_subjectPublicKeyInfo) x.riot_deviceID
  `Seq.append`
  serialize serialize_fwid x.riot_fwid
)
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

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"
let lemma_serialize_compositeDeviceID_payload_size
  (x: compositeDeviceID_payload_t)
: Lemma (
  length_of_opaque_serialization (serialize_compositeDeviceID_payload) x ==
  length_of_asn1_primitive_TLV x.riot_version +
  length_of_opaque_serialization (serialize_subjectPublicKeyInfo) x.riot_deviceID +
  length_of_opaque_serialization serialize_fwid x.riot_fwid /\
  length_of_opaque_serialization serialize_compositeDeviceID_payload x ==
  length_of_asn1_primitive_TLV x.riot_version + 91 /\
  length_of_opaque_serialization serialize_compositeDeviceID_payload x <= 97
)
= lemma_serialize_compositeDeviceID_payload_unfold x;
    lemma_serialize_subjectPublicKeyInfo_size_exact x.riot_deviceID;
    lemma_serialize_fwid_size_exact x.riot_fwid

(* inbound sub type*)
// unfold
let compositeDeviceID_t
= inbound_sequence_value_of (serialize_compositeDeviceID_payload)

(* TLV serializer *)
let parse_compositeDeviceID
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (compositeDeviceID_t)
= compositeDeviceID_t
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_compositeDeviceID_payload)

let serialize_compositeDeviceID
: serializer (parse_compositeDeviceID)
= coerce_parser_serializer
  (* t *) (parse_compositeDeviceID)
  (* s *) (serialize_asn1_sequence_TLV (serialize_compositeDeviceID_payload))
  (*prf*) ()

(* manually unfolding `lemma_serialize_asn1_sequence_TLV_size` to avoid stuck here.  *)
let lemma_serialize_compositeDeviceID_unfold
  (x: compositeDeviceID_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold serialize_compositeDeviceID_payload x )
= lemma_serialize_asn1_sequence_TLV_unfold serialize_compositeDeviceID_payload x

let lemma_serialize_compositeDeviceID_size
  (x: compositeDeviceID_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size serialize_compositeDeviceID_payload x )
= lemma_serialize_asn1_sequence_TLV_size serialize_compositeDeviceID_payload x

open FStar.Integers
#push-options "--z3rlimit 64"
let lemma_serialize_compositeDeviceID_size_exact
  (x: compositeDeviceID_t)
: Lemma (
  length_of_opaque_serialization serialize_compositeDeviceID x ==
  length_of_asn1_primitive_TLV x.riot_version + 93 /\
  length_of_opaque_serialization serialize_compositeDeviceID_payload x <= 99
)
= lemma_serialize_compositeDeviceID_unfold x;
  lemma_serialize_compositeDeviceID_size   x;
    lemma_serialize_compositeDeviceID_payload_size x
#pop-options

let serialize32_compositeDeviceID_payload_backwards
: serializer32_backwards (serialize_compositeDeviceID_payload)
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
: serializer32_backwards (serialize_compositeDeviceID)
= coerce_serializer32_backwards
  (* s2  *) (serialize_compositeDeviceID)
  (* s32 *) (serialize32_asn1_sequence_TLV_backwards
             (* ls *) (serialize32_compositeDeviceID_payload_backwards))
  (* prf *) ()

(* helpers *)
module B32 = FStar.Bytes

#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
let x509_get_compositeDeviceID
  (version: datatype_of_asn1_type INTEGER)
  (deviceKeyPub: B32.lbytes32 32ul)
  (fwid: B32.lbytes32 32ul)
: Tot (compositeDeviceID_t)
= let deviceIDPublicKeyInfo: subjectPublicKeyInfo_t = x509_get_subjectPublicKeyInfo deviceKeyPub in
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_size_exact deviceIDPublicKeyInfo;

  let fwid: fwid_payload_t = x509_get_fwid fwid in
  (* Prf *) lemma_serialize_fwid_size_exact fwid;

  let compositeDeviceID: compositeDeviceID_payload_t = {
    riot_version  = version;
    riot_deviceID = deviceIDPublicKeyInfo;
    riot_fwid     = fwid
  } in
  (* Prf *) lemma_serialize_compositeDeviceID_payload_size compositeDeviceID;
  (* Prf *) (**) lemma_serialize_asn1_integer_TLV_size compositeDeviceID.riot_version;

(* return *) compositeDeviceID
#pop-options
