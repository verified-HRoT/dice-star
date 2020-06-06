module RIoT.X509.FWID

open LowParse.Low.Base
// open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

// open X509.Crypto
// open X509.BasicFields
// open X509.ExtFields

open FStar.Integers

(* FWID
  ======
*)
type fwid_t = {
  fwid_hashAlg: x:datatype_of_asn1_type OID {x == OID_DIGEST_SHA256}; (* OID *)
  fwid_value  : x:datatype_of_asn1_type OCTET_STRING {v (dfst x) == 32}
}

let filter_fwid
  (x': datatype_of_asn1_type OID `tuple2` datatype_of_asn1_type OCTET_STRING)
: GTot bool
= fst x' = OID_DIGEST_SHA256 &&
  v (dfst (snd x')) = 32

let fwid_t' = parse_filter_refine filter_fwid

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
  `parse_filter`
  filter_fwid
  `parse_synth`
  synth_fwid_t

let serialize_fwid
: serializer parse_fwid
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type OID
            `nondep_then`
            parse_asn1_TLV_of_type OCTET_STRING
            `parse_filter`
            filter_fwid)
  (* f2 *) (synth_fwid_t)
  (* s1 *) (serialize_asn1_TLV_of_type OID
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type OCTET_STRING
            `serialize_filter`
            filter_fwid)
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
            parse_asn1_TLV_of_type OCTET_STRING
            `parse_filter`
            filter_fwid)
  (* f2 *) (synth_fwid_t)
  (* s1 *) (serialize_asn1_TLV_of_type OID
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type OCTET_STRING
            `serialize_filter`
            filter_fwid)
  (* g1 *) (synth_fwid_t')
  (* prf*) ()
  (* in *) x

#push-options "--z3rlimit 32"
let lemma_serialize_fwid_size
  (x: fwid_t)
: Lemma (
  Seq.length (serialize serialize_fwid x) ==
  length_of_asn1_primitive_TLV x.fwid_hashAlg +
  length_of_asn1_primitive_TLV x.fwid_value /\
  Seq.length (serialize serialize_fwid x) == 45
)
= lemma_serialize_fwid_unfold x;
  assert_norm (length_of_asn1_primitive_TLV x.fwid_hashAlg == 11);
  assert_norm (length_of_asn1_primitive_TLV x.fwid_value == 34)
#pop-options

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
  (x: fwid_t_inbound)
: Lemma ( prop_serialize_asn1_sequence_TLV_unfold serialize_fwid x )
= lemma_serialize_asn1_sequence_TLV_unfold serialize_fwid x

let lemma_serialize_fwid_sequence_TLV_size
  (x: fwid_t_inbound)
: Lemma ( prop_serialize_asn1_sequence_TLV_size serialize_fwid x )
= lemma_serialize_asn1_sequence_TLV_size serialize_fwid x

/// 1 + 1 + 45
#restart-solver
#push-options "--z3rlimit 32 --fuel 4 --ifuel 4"
let lemma_serialize_fwid_sequence_TLV_size_exact
  (x: fwid_t_inbound)
: Lemma (
  length_of_opaque_serialization serialize_fwid_sequence_TLV x == 47
)
=
  lemma_serialize_fwid_sequence_TLV_unfold x;
  lemma_serialize_fwid_sequence_TLV_size x;
  lemma_serialize_fwid_size x
#pop-options

(* Low *)
let serialize32_fwid_backwards
: serializer32_backwards serialize_fwid
= serialize32_synth_backwards
  (* ls *) (serialize32_asn1_TLV_backwards_of_type OID
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type OCTET_STRING
            `serialize32_filter_backwards`
            filter_fwid)
  (* f2 *) (synth_fwid_t)
  (* g1 *) (synth_fwid_t')
  (* g1'*) (synth_fwid_t')
  (* prf*) ()

let serialize32_fwid_sequence_TLV_backwards
: serializer32_backwards serialize_fwid_sequence_TLV
= serialize32_asn1_sequence_TLV_backwards
  (* ls *) (serialize32_fwid_backwards)
