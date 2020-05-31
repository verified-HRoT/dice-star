module X509.RIoT.Ext

open LowParse.Low.Base
// open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

open X509.Crypto

(* FWID
  ======
*)
noeq
type fwid_t = {
  fwid_hashAlg: datatype_of_asn1_type OID; (* OID *)
  fwid_value  : datatype_of_asn1_type OCTET_STRING
}
let fwid_t' = (datatype_of_asn1_type OID & datatype_of_asn1_type OCTET_STRING)

(* Serialier spec *)
let synth_fwid_t
  (x': fwid_t')
: GTot (fwid_t)
= { fwid_hashAlg = fst x';
    fwid_value   = snd x' }

let synth_fwid_t'
  (x: fwid_t)
: Tot (x': fwid_t' { x == synth_fwid_t x' } )
= (x.fwid_hashAlg, x.fwid_value)

let parse_fwid_sequence
: parser _ fwid_t
= parse_asn1_TLV_of_type OID
  `nondep_then`
  parse_asn1_TLV_of_type OCTET_STRING
  `parse_synth`
  synth_fwid_t

let serialize_fwid_sequence
: serializer parse_fwid_sequence
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type OID
            `nondep_then`
            parse_asn1_TLV_of_type OCTET_STRING)
  (* f2 *) (synth_fwid_t)
  (* s1 *) (serialize_asn1_TLV_of_type OID
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type OCTET_STRING)
  (* g1 *) (synth_fwid_t')
  (* prf*) ()

let lemma_serialize_fwid_sequence_unfold
  (x: fwid_t)
: Lemma (
  serialize serialize_fwid_sequence x ==
  serialize serialize_asn1_oid_TLV x.fwid_hashAlg
  `Seq.append`
  serialize serialize_asn1_octet_string_TLV x.fwid_value
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type OID)
  (* s2 *) (serialize_asn1_TLV_of_type OCTET_STRING)
  (* in *) (synth_fwid_t' x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type OID
            `nondep_then`
            parse_asn1_TLV_of_type OCTET_STRING)
  (* f2 *) (synth_fwid_t)
  (* s1 *) (serialize_asn1_TLV_of_type OID
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type OCTET_STRING)
  (* g1 *) (synth_fwid_t')
  (* prf*) ()
  (* in *) x

#push-options "--query_stats --z3rlimit 16"
let lemma_serialize_fwid_sequence_size
  (x: fwid_t)
: Lemma (
  Seq.length (serialize serialize_fwid_sequence x) ==
  length_of_asn1_primitive_TLV x.fwid_hashAlg +
  length_of_asn1_primitive_TLV x.fwid_value
)
= lemma_serialize_fwid_sequence_unfold x;
  lemma_serialize_asn1_oid_TLV_size x.fwid_hashAlg;
  lemma_serialize_asn1_octet_string_TLV_size x.fwid_value
#pop-options

(* inbound sub type*)
let fwid_t_inbound
= inbound_sequence_value_of serialize_fwid_sequence

(* TLV serializer *)
let parse_fwid_sequence_TLV
: parser _ fwid_t_inbound
= parse_asn1_sequence_TLV serialize_fwid_sequence

let serialize_fwid_sequence_TLV
: serializer parse_fwid_sequence_TLV
= serialize_asn1_sequence_TLV serialize_fwid_sequence

let lemma_serialize_fwid_sequence_TLV_unfold
= lemma_serialize_asn1_sequence_TLV_unfold serialize_fwid_sequence

let lemma_serialize_fwid_sequence_TLV_size
= lemma_serialize_asn1_sequence_TLV_size serialize_fwid_sequence

let serialize32_fwid_sequence
: serializer32_backwards serialize_fwid_sequence
= serialize32_synth_backwards
  (* ls *) (serialize32_asn1_TLV_backwards_of_type OID
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type OCTET_STRING)
  (* f2 *) (synth_fwid_t)
  (* g1 *) (synth_fwid_t')
  (* g1'*) (synth_fwid_t')
  (* prf*) ()

let serialize32_fwid_TLV_sequence_backwards
: serializer32_backwards serialize_fwid_sequence_TLV
= serialize32_asn1_sequence_TLV_backwards
  (* ls *) (serialize32_fwid_sequence)

(* CompositeDeviceID *)
noeq
type compositeDeviceID_t = {
  device_version: datatype_of_asn1_type INTEGER;
  deviceID: subjectPublicKeyInfo_ECDSA_P256_t_inbound;
  fwid: fwid_t_inbound
}

let compositeDeviceID_t'
= ((datatype_of_asn1_type INTEGER &
    subjectPublicKeyInfo_ECDSA_P256_t_inbound) &
    fwid_t_inbound)

(* Serialier spec *)
let synth_compositeDeviceID_t
  (x': compositeDeviceID_t')
: GTot (compositeDeviceID_t)
= { device_version  = fst (fst x');
    deviceID = snd (fst x');
    fwid     = snd x' }

let synth_compositeDeviceID_t'
  (x: compositeDeviceID_t)
: Tot (x': compositeDeviceID_t' { x == synth_compositeDeviceID_t x' })
= ((x.device_version, x.deviceID), x.fwid)

let parse_compositeDeviceID_sequence
: parser _ compositeDeviceID_t
= parse_asn1_TLV_of_type INTEGER
  `nondep_then`
  parse_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256
  `nondep_then`
  parse_fwid_sequence_TLV
  `parse_synth`
  synth_compositeDeviceID_t

let serialize_compositeDeviceID_sequence
: serializer parse_compositeDeviceID_sequence
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type INTEGER
            `nondep_then`
            parse_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256
            `nondep_then`
            parse_fwid_sequence_TLV)
  (* f2 *) (synth_compositeDeviceID_t)
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256
            `serialize_nondep_then`
            serialize_fwid_sequence_TLV)
  (* g1 *) (synth_compositeDeviceID_t')
  (* prf*) ()

let lemma_serialize_compositeDeviceID_sequence_unfold
  (x: compositeDeviceID_t)
: Lemma (
  serialize serialize_compositeDeviceID_sequence x ==
  serialize (serialize_asn1_TLV_of_type INTEGER) x.device_version
  `Seq.append`
  serialize serialize_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256 x.deviceID
  `Seq.append`
  serialize serialize_fwid_sequence_TLV x.fwid
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER)
  (* s2 *) (serialize_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256)
  (* in *) (fst (synth_compositeDeviceID_t' x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256)
  (* s2 *) (serialize_fwid_sequence_TLV)
  (* in *) (synth_compositeDeviceID_t' x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type INTEGER
            `nondep_then`
            parse_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256
            `nondep_then`
            parse_fwid_sequence_TLV)
  (* f2 *) (synth_compositeDeviceID_t)
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256
            `serialize_nondep_then`
            serialize_fwid_sequence_TLV)
  (* g1 *) (synth_compositeDeviceID_t')
  (* prf*) ()
  (* in *) x

let lemma_serialize_compositeDeviceID_sequence_size
  (x: compositeDeviceID_t)
: Lemma (
  Seq.length (serialize serialize_compositeDeviceID_sequence x) ==
  length_of_asn1_primitive_TLV x.device_version +
  Seq.length (serialize serialize_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256 x.deviceID) +
  Seq.length (serialize serialize_fwid_sequence_TLV x.fwid))
= lemma_serialize_compositeDeviceID_sequence_unfold x;
  lemma_serialize_asn1_integer_TLV_size x.device_version;
  lemma_serialize_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256_size x.deviceID;
  lemma_serialize_fwid_sequence_TLV_size x.fwid

(* inbound sub type*)
let compositeDeviceID_t_inbound
= inbound_sequence_value_of serialize_compositeDeviceID_sequence

(* TLV serializer *)
let parse_compositeDeviceID_sequence_TLV
: parser _ compositeDeviceID_t_inbound
= parse_asn1_sequence_TLV serialize_compositeDeviceID_sequence

let serialize_compositeDeviceID_sequence_TLV
: serializer parse_compositeDeviceID_sequence_TLV
= serialize_asn1_sequence_TLV serialize_compositeDeviceID_sequence

let lemma_serialize_compositeDeviceID_sequence_TLV_unfold
= lemma_serialize_asn1_sequence_TLV_unfold serialize_compositeDeviceID_sequence

let lemma_serialize_compositeDeviceID_sequence_TLV_size
= lemma_serialize_asn1_sequence_TLV_size serialize_compositeDeviceID_sequence

let serialize32_compositeDeviceID_sequence
: serializer32_backwards serialize_compositeDeviceID_sequence
= serialize32_synth_backwards
  (* ls *) (serialize32_asn1_TLV_backwards_of_type INTEGER
            `serialize32_nondep_then_backwards`
            serialize32_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256_backwards
            `serialize32_nondep_then_backwards`
            serialize32_fwid_TLV_sequence_backwards)
  (* f2 *) (synth_compositeDeviceID_t)
  (* g1 *) (synth_compositeDeviceID_t')
  (* g1'*) (synth_compositeDeviceID_t')
  (* prf*) ()

let serialize32_compositeDeviceID_TLV_sequence_backwards
: serializer32_backwards serialize_compositeDeviceID_sequence_TLV
= serialize32_asn1_sequence_TLV_backwards
  (* ls *) (serialize32_compositeDeviceID_sequence)

(* RIoT Extension*)
noeq
type riot_extension_t = {
  riot_oid: oid:datatype_of_asn1_type OID{ oid == OID_RIOT };
  riot_compositeDeviceID: compositeDeviceID_t_inbound
}

/// tuple repr
let filter_riot_extension_t'
  (x': tuple2 (datatype_of_asn1_type OID) compositeDeviceID_t_inbound)
: GTot bool
= fst x' = OID_RIOT

let riot_extension_t'
= parse_filter_refine filter_riot_extension_t'

(* Serialier spec *)
let synth_riot_extension_t
  (x': riot_extension_t')
: GTot (riot_extension_t)
= { riot_oid = fst x';
    riot_compositeDeviceID = snd x' }

let synth_riot_extension_t'
  (x: riot_extension_t)
: Tot (x': riot_extension_t' { x == synth_riot_extension_t x' })
= (x.riot_oid, x.riot_compositeDeviceID)

let parse_riot_extension_sequence
: parser _ riot_extension_t
= parse_asn1_TLV_of_type OID
  `nondep_then`
  parse_compositeDeviceID_sequence_TLV
  `parse_filter`
  filter_riot_extension_t'
  `parse_synth`
  synth_riot_extension_t

let serialize_riot_extension_sequence
: serializer parse_riot_extension_sequence
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type OID
            `nondep_then`
            parse_compositeDeviceID_sequence_TLV
            `parse_filter`
            filter_riot_extension_t')
  (* f2 *) (synth_riot_extension_t)
  (* s1 *) (serialize_asn1_TLV_of_type OID
            `serialize_nondep_then`
            serialize_compositeDeviceID_sequence_TLV
            `serialize_filter`
            filter_riot_extension_t')
  (* g1 *) (synth_riot_extension_t')
  (* prf*) ()

let lemma_serialize_riot_extension_sequence_unfold
  (x: riot_extension_t)
: Lemma (
  serialize serialize_riot_extension_sequence x ==
  serialize (serialize_asn1_TLV_of_type OID) x.riot_oid
  `Seq.append`
  serialize serialize_compositeDeviceID_sequence_TLV x.riot_compositeDeviceID
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type OID)
  (* s2 *) (serialize_compositeDeviceID_sequence_TLV)
  (* in *) (synth_riot_extension_t' x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type OID
            `nondep_then`
            parse_compositeDeviceID_sequence_TLV
            `parse_filter`
            filter_riot_extension_t')
  (* f2 *) (synth_riot_extension_t)
  (* s1 *) (serialize_asn1_TLV_of_type OID
            `serialize_nondep_then`
            serialize_compositeDeviceID_sequence_TLV
            `serialize_filter`
            filter_riot_extension_t')
  (* g1 *) (synth_riot_extension_t')
  (* prf*) ()
  (* in *) x

let lemma_serialize_riot_extension_sequence_size
  (x: riot_extension_t)
: Lemma (
  Seq.length (serialize serialize_riot_extension_sequence x) ==
  length_of_asn1_primitive_TLV x.riot_oid +
  Seq.length (serialize serialize_compositeDeviceID_sequence_TLV x.riot_compositeDeviceID))
= lemma_serialize_riot_extension_sequence_unfold x;
  lemma_serialize_asn1_oid_TLV_size x.riot_oid;
  lemma_serialize_compositeDeviceID_sequence_TLV_size x.riot_compositeDeviceID

(* inbound sub type*)
let riot_extension_t_inbound
= inbound_sequence_value_of serialize_riot_extension_sequence

(* TLV serializer *)
let parse_riot_extension_sequence_TLV
: parser _ riot_extension_t_inbound
= parse_asn1_sequence_TLV serialize_riot_extension_sequence

let serialize_riot_extension_sequence_TLV
: serializer parse_riot_extension_sequence_TLV
= serialize_asn1_sequence_TLV serialize_riot_extension_sequence

let lemma_serialize_riot_extension_sequence_TLV_unfold
= lemma_serialize_asn1_sequence_TLV_unfold serialize_riot_extension_sequence

let lemma_serialize_riot_extension_sequence_TLV_size
= lemma_serialize_asn1_sequence_TLV_size serialize_riot_extension_sequence

let serialize32_riot_extension_sequence
: serializer32_backwards serialize_riot_extension_sequence
= serialize32_synth_backwards
  (* ls *) (serialize32_asn1_TLV_backwards_of_type OID
            `serialize32_nondep_then_backwards`
            serialize32_compositeDeviceID_TLV_sequence_backwards
            `serialize32_filter_backwards`
            filter_riot_extension_t')
  (* f2 *) (synth_riot_extension_t)
  (* g1 *) (synth_riot_extension_t')
  (* g1'*) (synth_riot_extension_t')
  (* prf*) ()

let serialize32_riot_extension_TLV_sequence_backwards
: serializer32_backwards serialize_riot_extension_sequence_TLV
= serialize32_asn1_sequence_TLV_backwards
  (* ls *) (serialize32_riot_extension_sequence)
