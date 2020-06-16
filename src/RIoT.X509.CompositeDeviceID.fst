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

(* CompositeDeviceID *)
type compositeDeviceID_t
= { riot_version : datatype_of_asn1_type INTEGER;
    riot_deviceID: subjectPublicKeyInfo_t_inbound;
    riot_fwid    : fwid_t_inbound }

let compositeDeviceID_t'
= ((datatype_of_asn1_type INTEGER &
    subjectPublicKeyInfo_t_inbound) &
    fwid_t_inbound)

(* Serialier spec *)
let synth_compositeDeviceID_t
  (x': compositeDeviceID_t')
: GTot (compositeDeviceID_t)
= { riot_version  = fst (fst x');
    riot_deviceID = snd (fst x');
    riot_fwid     = snd x' }

let synth_compositeDeviceID_t'
  (x: compositeDeviceID_t)
: Tot (x': compositeDeviceID_t' { x == synth_compositeDeviceID_t x' })
= ((x.riot_version, x.riot_deviceID), x.riot_fwid)

let parse_compositeDeviceID
: parser _ (compositeDeviceID_t)
= parse_asn1_TLV_of_type INTEGER
  `nondep_then`
  parse_subjectPublicKeyInfo_sequence_TLV
  `nondep_then`
  parse_fwid_sequence_TLV
  `parse_synth`
  synth_compositeDeviceID_t

let serialize_compositeDeviceID
: serializer (parse_compositeDeviceID)
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type INTEGER
            `nondep_then`
            parse_subjectPublicKeyInfo_sequence_TLV
            `nondep_then`
            parse_fwid_sequence_TLV)
  (* f2 *) (synth_compositeDeviceID_t)
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo_sequence_TLV
            `serialize_nondep_then`
            serialize_fwid_sequence_TLV)
  (* g1 *) (synth_compositeDeviceID_t')
  (* prf*) ()

let lemma_serialize_compositeDeviceID_unfold
  (x: compositeDeviceID_t)
: Lemma (
  serialize (serialize_compositeDeviceID) x ==
  serialize (serialize_asn1_TLV_of_type INTEGER) x.riot_version
  `Seq.append`
  serialize (serialize_subjectPublicKeyInfo_sequence_TLV) x.riot_deviceID
  `Seq.append`
  serialize serialize_fwid_sequence_TLV x.riot_fwid
  // (* unfold subjectPublicKeyInfo *)
  // serialize (serialize_subjectPublicKeyInfo) x.riot_deviceID ==
  // serialize (serialize_algorithmIdentifier_sequence_TLV) x.riot_deviceID.subjectPubKey_alg
  // `Seq.append`
  // serialize (serialize_asn1_TLV_of_type BIT_STRING) x.riot_deviceID.subjectPubKey /\
  // (* unfold FWID *)
  // serialize serialize_fwid x.riot_fwid ==
  // serialize (serialize_asn1_TLV_of_type OID) x.riot_fwid.fwid_hashAlg
  // `Seq.append`
  // serialize (serialize_asn1_TLV_of_type OCTET_STRING) x.riot_fwid.fwid_value
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER)
  (* s2 *) (serialize_subjectPublicKeyInfo_sequence_TLV)
  (* in *) (fst (synth_compositeDeviceID_t' x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo_sequence_TLV)
  (* s2 *) (serialize_fwid_sequence_TLV)
  (* in *) (synth_compositeDeviceID_t' x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type INTEGER
            `nondep_then`
            parse_subjectPublicKeyInfo_sequence_TLV
            `nondep_then`
            parse_fwid_sequence_TLV)
  (* f2 *) (synth_compositeDeviceID_t)
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo_sequence_TLV
            `serialize_nondep_then`
            serialize_fwid_sequence_TLV)
  (* g1 *) (synth_compositeDeviceID_t')
  (* prf*) ()
  (* in *) x
    // lemma_serialize_subjectPublicKeyInfo_sequence_TLV_unfold   x.riot_deviceID;
    // lemma_serialize_subjectPublicKeyInfo_unfold                x.riot_deviceID;
    //   lemma_serialize_algorithmIdentifier_sequence_TLV_unfold x.riot_deviceID.subjectPubKey_alg;
    //   lemma_serialize_algorithmIdentifier_sequence_TLV_size   x.riot_deviceID.subjectPubKey_alg;
    // lemma_serialize_fwid_sequence_TLV_unfold x.riot_fwid;
    // lemma_serialize_fwid_unfold              x.riot_fwid

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"
let lemma_serialize_compositeDeviceID_size
  (x: compositeDeviceID_t)
: Lemma (
  length_of_opaque_serialization (serialize_compositeDeviceID) x ==
  length_of_asn1_primitive_TLV x.riot_version +
  length_of_opaque_serialization (serialize_subjectPublicKeyInfo_sequence_TLV) x.riot_deviceID +
  length_of_opaque_serialization serialize_fwid_sequence_TLV x.riot_fwid /\
  length_of_opaque_serialization serialize_compositeDeviceID x ==
  length_of_asn1_primitive_TLV x.riot_version + 91 /\
  length_of_opaque_serialization serialize_compositeDeviceID x <= 97
)
= lemma_serialize_compositeDeviceID_unfold x;
    lemma_serialize_subjectPublicKeyInfo_sequence_TLV_size_exact x.riot_deviceID;
    lemma_serialize_fwid_sequence_TLV_size_exact x.riot_fwid

(* inbound sub type*)
let compositeDeviceID_t_inbound
= inbound_sequence_value_of (serialize_compositeDeviceID)

(* TLV serializer *)
let parse_compositeDeviceID_sequence_TLV
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (compositeDeviceID_t_inbound)
= compositeDeviceID_t_inbound
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_compositeDeviceID)

let serialize_compositeDeviceID_sequence_TLV
: serializer (parse_compositeDeviceID_sequence_TLV)
= coerce_parser_serializer
  (* t *) (parse_compositeDeviceID_sequence_TLV)
  (* s *) (serialize_asn1_sequence_TLV (serialize_compositeDeviceID))
  (*prf*) ()

(* manually unfolding `lemma_serialize_asn1_sequence_TLV_size` to avoid stuck here.  *)
let lemma_serialize_compositeDeviceID_sequence_TLV_unfold
  (x: compositeDeviceID_t_inbound)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold serialize_compositeDeviceID x )
= lemma_serialize_asn1_sequence_TLV_unfold serialize_compositeDeviceID x

let lemma_serialize_compositeDeviceID_sequence_TLV_size
  (x: compositeDeviceID_t_inbound)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size serialize_compositeDeviceID x )
= lemma_serialize_asn1_sequence_TLV_size serialize_compositeDeviceID x

open FStar.Integers
#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
let lemma_serialize_compositeDeviceID_sequence_TLV_size_exact
  (x: compositeDeviceID_t_inbound)
: Lemma (
  length_of_opaque_serialization serialize_compositeDeviceID_sequence_TLV x ==
  length_of_asn1_primitive_TLV x.riot_version + 93 /\
  length_of_opaque_serialization serialize_compositeDeviceID_sequence_TLV x <= 99
)
= lemma_serialize_compositeDeviceID_sequence_TLV_unfold x;
  lemma_serialize_compositeDeviceID_sequence_TLV_size   x;
    lemma_serialize_compositeDeviceID_size x;
    assert (length_of_opaque_serialization serialize_compositeDeviceID_sequence_TLV x ==
            1 +
            length_of_asn1_length (u (length_of_opaque_serialization serialize_compositeDeviceID x)) +
            length_of_opaque_serialization serialize_compositeDeviceID x)
#pop-options

let serialize32_compositeDeviceID_backwards
: serializer32_backwards (serialize_compositeDeviceID)
= serialize32_synth_backwards
  (* ls *) (serialize32_asn1_TLV_backwards_of_type INTEGER
            `serialize32_nondep_then_backwards`
            serialize32_subjectPublicKeyInfo_sequence_TLV_backwards
            `serialize32_nondep_then_backwards`
            serialize32_fwid_sequence_TLV_backwards)
  (* f2 *) (synth_compositeDeviceID_t)
  (* g1 *) (synth_compositeDeviceID_t')
  (* g1'*) (synth_compositeDeviceID_t')
  (* prf*) ()

let serialize32_compositeDeviceID_sequence_TLV_backwards
: serializer32_backwards (serialize_compositeDeviceID_sequence_TLV)
= coerce_serializer32_backwards
  (* s2  *) (serialize_compositeDeviceID_sequence_TLV)
  (* s32 *) (serialize32_asn1_sequence_TLV_backwards
             (* ls *) (serialize32_compositeDeviceID_backwards))
  (* prf *) ()

(* helpers *)
module B32 = FStar.Bytes

#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
let x509_get_compositeDeviceID
  (version: datatype_of_asn1_type INTEGER)
  (deviceKeyPub: B32.lbytes32 32ul)
  (fwid: B32.lbytes32 32ul)
: Tot (compositeDeviceID_t_inbound)
= let deviceIDPublicKeyInfo: subjectPublicKeyInfo_t_inbound = x509_get_subjectPublicKeyInfo deviceKeyPub in
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_sequence_TLV_size_exact deviceIDPublicKeyInfo;

  let fwid: fwid_t_inbound = x509_get_fwid fwid in
  (* Prf *) lemma_serialize_fwid_sequence_TLV_size_exact fwid;

  let compositeDeviceID: compositeDeviceID_t = {
    riot_version  = version;
    riot_deviceID = deviceIDPublicKeyInfo;
    riot_fwid     = fwid
  } in
  (* Prf *) lemma_serialize_compositeDeviceID_size compositeDeviceID;
  (* Prf *) (**) lemma_serialize_asn1_integer_TLV_size compositeDeviceID.riot_version;

(* return *) compositeDeviceID
#pop-options
