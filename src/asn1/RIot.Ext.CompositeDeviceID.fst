module RIoT.Ext.CompositeDeviceID

open LowParse.Low.Base
open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

open RIoT.Ext


//////////////////////////////////////////////////////////
noeq
type compositeDeviceID_t = {
  version: datatype_of_asn1_type INTEGER;
  deviceID: subjectPublicKeyInfo_t_inbound;
  fwid2: fwid_t_inbound
}

let compositeDeviceID_t' = ((datatype_of_asn1_type INTEGER * subjectPublicKeyInfo_t_inbound) * fwid_t_inbound)

(* Serialier spec *)
let synth_compositeDeviceID_t
  (x': compositeDeviceID_t')
: GTot (compositeDeviceID_t)
= { version  = fst (fst x');
    deviceID = snd (fst x');
    fwid2     = snd x' }

let synth_compositeDeviceID_t'
  (x: compositeDeviceID_t)
: Tot (x': compositeDeviceID_t' { x == synth_compositeDeviceID_t x' })
= let a: (datatype_of_asn1_type INTEGER * subjectPublicKeyInfo_t_inbound) = (x.version, x.deviceID) in
  (a, x.fwid2)

let parse_compositeDeviceID_value
: parser _ compositeDeviceID_t
= parse_asn1_TLV_of_type INTEGER
  `nondep_then`
  parse_subjectPublicKeyInfo_sequence_TLV
  `nondep_then`
  parse_fwid_sequence_TLV
  `parse_synth`
  synth_compositeDeviceID_t

let serialize_compositeDeviceID_value
: serializer parse_compositeDeviceID_value
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

let serialize_compositeDeviceID_value_unfold
  (x: compositeDeviceID_t)
: Lemma (
  serialize serialize_compositeDeviceID_value x ==
  serialize (serialize_asn1_TLV_of_type INTEGER) x.version
  `Seq.append`
  serialize serialize_subjectPublicKeyInfo_sequence_TLV x.deviceID
  `Seq.append`
  serialize serialize_fwid_sequence_TLV x.fwid2
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
open FStar.Integers

let serialize_compositeDeviceID_value_size
  (x: compositeDeviceID_t)
: Lemma (
  Seq.length (serialize serialize_compositeDeviceID_value x) ==
  length_of_asn1_primitive_TLV x.version +
  v (len_of_subjectPublicKeyInfo_TLV_inbound x.deviceID) +
  v (len_of_fwid_TLV_inbound x.fwid2))
= serialize_compositeDeviceID_value_unfold x;
  lemma_serialize_asn1_integer_TLV_size x.version;
  serialize_subjectPublicKeyInfo_sequence_TLV_size x.deviceID;
  serialize_fwid_sequence_TLV_size x.fwid2

(* inbound sub type*)
let compositeDeviceID_t_inbound
= inbound_sequence_value_of serialize_compositeDeviceID_value

(* TLV serializer *)
let parse_compositeDeviceID_sequence_TLV
: parser _ compositeDeviceID_t_inbound
= parse_asn1_sequence_TLV serialize_compositeDeviceID_value

let serialize_compositeDeviceID_sequence_TLV
: serializer parse_compositeDeviceID_sequence_TLV
= serialize_asn1_sequence_TLV serialize_compositeDeviceID_value

let serialize_compositeDeviceID_sequence_TLV_unfold
= lemma_serialize_asn1_sequence_TLV_unfold serialize_compositeDeviceID_value

let serialize_compositeDeviceID_sequence_TLV_size
= lemma_serialize_asn1_sequence_TLV_size serialize_compositeDeviceID_value

let serialize32_compositeDeviceID_value
: serializer32_backwards serialize_compositeDeviceID_value
= serialize32_synth_backwards
  (* ls *) (serialize32_asn1_TLV_backwards_of_type INTEGER
            `serialize32_nondep_then_backwards`
            serialize32_subjectPublicKeyInfo_sequence_TLV_backwards
            `serialize32_nondep_then_backwards`
            serialize32_fwid_TLV_sequence_backwards)
  (* f2 *) (synth_compositeDeviceID_t)
  (* g1 *) (synth_compositeDeviceID_t')
  (* g1'*) (synth_compositeDeviceID_t')
  (* prf*) ()

#push-options "--query_stats --z3rlimit 64"
let len_of_compositeDeviceID_value_inbound
  (x: compositeDeviceID_t_inbound)
: Tot (inbound_sequence_value_len_of serialize_compositeDeviceID_value x)
= serialize_compositeDeviceID_value_unfold x;
  serialize_compositeDeviceID_value_size x;
  len_of_asn1_primitive_TLV x.version +
  len_of_subjectPublicKeyInfo_TLV_inbound x.deviceID +
  len_of_fwid_TLV_inbound x.fwid2
#pop-options

let len_of_compositeDeviceID_TLV_inbound
  (x: compositeDeviceID_t_inbound)
// : Tot (inbound_sequence_value_len_of serialize_compositeDeviceID_sequence_TLV x)
= len_of_sequence_TLV
  (* s *) serialize_compositeDeviceID_value
  (*len*) len_of_compositeDeviceID_value_inbound
  (*val*) x

let serialize32_compositeDeviceID_sequence
: serializer32_backwards serialize_compositeDeviceID_sequence_TLV
= serialize32_asn1_sequence_TLV_backwards
  (* ls *) (serialize32_compositeDeviceID_value)
  (*flen*) (len_of_compositeDeviceID_value_inbound)
