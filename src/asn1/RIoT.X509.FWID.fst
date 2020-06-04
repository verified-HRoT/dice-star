module RIoT.X509.FWID

open LowParse.Low.Base
// open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

open X509.Crypto
open X509.BasicFields
open X509.ExtFields

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

let parse_fwid
: parser _ fwid_t
= parse_asn1_TLV_of_type OID
  `nondep_then`
  parse_asn1_TLV_of_type OCTET_STRING
  `parse_synth`
  synth_fwid_t

let serialize_fwid
: serializer parse_fwid
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

let lemma_serialize_fwid_unfold
  (x: fwid_t)
: Lemma (
  serialize serialize_fwid x ==
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

let lemma_serialize_fwid_size
  (x: fwid_t)
: Lemma (
  Seq.length (serialize serialize_fwid x) ==
  length_of_asn1_primitive_TLV x.fwid_hashAlg +
  length_of_asn1_primitive_TLV x.fwid_value
)
= lemma_serialize_fwid_unfold x

(* inbound sub type*)
let fwid_t_inbound
= inbound_sequence_value_of serialize_fwid

(* TLV serializer *)
let parse_fwid_sequence_TLV
: parser _ fwid_t_inbound
= parse_asn1_sequence_TLV serialize_fwid

let serialize_fwid_sequence_TLV
: serializer parse_fwid_sequence_TLV
= serialize_asn1_sequence_TLV serialize_fwid

let lemma_serialize_fwid_sequence_TLV_unfold
= lemma_serialize_asn1_sequence_TLV_unfold serialize_fwid

let lemma_serialize_fwid_sequence_TLV_size
= lemma_serialize_asn1_sequence_TLV_size serialize_fwid

(* Low *)
let serialize32_fwid_backwards
: serializer32_backwards serialize_fwid
= serialize32_synth_backwards
  (* ls *) (serialize32_asn1_TLV_backwards_of_type OID
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type OCTET_STRING)
  (* f2 *) (synth_fwid_t)
  (* g1 *) (synth_fwid_t')
  (* g1'*) (synth_fwid_t')
  (* prf*) ()

let serialize32_fwid_sequence_TLV_backwards
: serializer32_backwards serialize_fwid_sequence_TLV
= serialize32_asn1_sequence_TLV_backwards
  (* ls *) (serialize32_fwid_backwards)
