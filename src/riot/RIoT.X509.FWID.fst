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
type fwid_payload_t = {
  fwid_hashAlg: x:datatype_of_asn1_type OID {x == OID_DIGEST_SHA256}; (* OID *)
  fwid_value  : x:datatype_of_asn1_type OCTET_STRING {v (dfst x) == 32}
}

let filter_fwid_payload
  (x': datatype_of_asn1_type OID `tuple2` datatype_of_asn1_type OCTET_STRING)
: GTot bool
= fst x' = OID_DIGEST_SHA256 &&
  v (dfst (snd x')) = 32

let fwid_payload_t' = parse_filter_refine filter_fwid_payload

(* Serialier spec *)
let synth_fwid_payload_t
  (x': fwid_payload_t')
: GTot (fwid_payload_t)
= { fwid_hashAlg = fst x';
    fwid_value   = snd x' }

let synth_fwid_payload_t'
  (x: fwid_payload_t)
: Tot (x': fwid_payload_t' { x == synth_fwid_payload_t x' } )
= (x.fwid_hashAlg, x.fwid_value)

let parse_fwid_payload
: parser _ fwid_payload_t
= parse_asn1_TLV_of_type OID
  `nondep_then`
  parse_asn1_TLV_of_type OCTET_STRING
  `parse_filter`
  filter_fwid_payload
  `parse_synth`
  synth_fwid_payload_t

let serialize_fwid_payload
: serializer parse_fwid_payload
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type OID
            `nondep_then`
            parse_asn1_TLV_of_type OCTET_STRING
            `parse_filter`
            filter_fwid_payload)
  (* f2 *) (synth_fwid_payload_t)
  (* s1 *) (serialize_asn1_TLV_of_type OID
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type OCTET_STRING
            `serialize_filter`
            filter_fwid_payload)
  (* g1 *) (synth_fwid_payload_t')
  (* prf*) ()

let lemma_serialize_fwid_payload_unfold
  (x: fwid_payload_t)
: Lemma (
  serialize serialize_fwid_payload x ==
  serialize serialize_asn1_oid_TLV x.fwid_hashAlg
  `Seq.append`
  serialize serialize_asn1_octet_string_TLV x.fwid_value
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type OID)
  (* s2 *) (serialize_asn1_TLV_of_type OCTET_STRING)
  (* in *) (synth_fwid_payload_t' x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type OID
            `nondep_then`
            parse_asn1_TLV_of_type OCTET_STRING
            `parse_filter`
            filter_fwid_payload)
  (* f2 *) (synth_fwid_payload_t)
  (* s1 *) (serialize_asn1_TLV_of_type OID
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type OCTET_STRING
            `serialize_filter`
            filter_fwid_payload)
  (* g1 *) (synth_fwid_payload_t')
  (* prf*) ()
  (* in *) x

#push-options "--z3rlimit 32"
let lemma_serialize_fwid_payload_size
  (x: fwid_payload_t)
: Lemma (
  Seq.length (serialize serialize_fwid_payload x) ==
  length_of_asn1_primitive_TLV x.fwid_hashAlg +
  length_of_asn1_primitive_TLV x.fwid_value /\
  Seq.length (serialize serialize_fwid_payload x) == 45
)
= lemma_serialize_fwid_payload_unfold x;
  assert_norm (length_of_asn1_primitive_TLV x.fwid_hashAlg == 11);
  assert_norm (length_of_asn1_primitive_TLV x.fwid_value == 34)
#pop-options

(* inbound sub type*)
let fwid_t
= inbound_sequence_value_of serialize_fwid_payload

(* TLV serializer *)
let parse_fwid
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) fwid_t
= fwid_t
  `coerce_parser`
  parse_asn1_sequence_TLV serialize_fwid_payload

let serialize_fwid
: serializer parse_fwid
= coerce_parser_serializer
  (* p *) (parse_fwid)
  (* s *) (serialize_asn1_sequence_TLV serialize_fwid_payload)
  (*prf*) ()

let lemma_serialize_fwid_unfold
  (x: fwid_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold serialize_fwid_payload x )
= lemma_serialize_asn1_sequence_TLV_unfold serialize_fwid_payload x

let lemma_serialize_fwid_size
  (x: fwid_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size serialize_fwid_payload x )
= lemma_serialize_asn1_sequence_TLV_size serialize_fwid_payload x

/// 1 + 1 + 45
#restart-solver
#push-options "--z3rlimit 32 --fuel 4 --ifuel 4"
let lemma_serialize_fwid_size_exact
  (x: fwid_t)
: Lemma (
  length_of_opaque_serialization serialize_fwid x == 47
)
=
  lemma_serialize_fwid_unfold x;
  lemma_serialize_fwid_size x;
  lemma_serialize_fwid_payload_size x
#pop-options

(* Low *)
let serialize32_fwid_payload_backwards
: serializer32_backwards serialize_fwid_payload
= serialize32_synth_backwards
  (* ls *) (serialize32_asn1_TLV_backwards_of_type OID
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type OCTET_STRING
            `serialize32_filter_backwards`
            filter_fwid_payload)
  (* f2 *) (synth_fwid_payload_t)
  (* g1 *) (synth_fwid_payload_t')
  (* g1'*) (synth_fwid_payload_t')
  (* prf*) ()

let serialize32_fwid_backwards
: serializer32_backwards serialize_fwid
= coerce_serializer32_backwards
  (* s  *) (serialize_fwid)
  (* s32*) (serialize32_asn1_sequence_TLV_backwards
           (* ls *) (serialize32_fwid_payload_backwards))
  (* prf*) ()

module B32 = FStar.Bytes

(* helpers *)
#push-options "--z3rlimit 8 --fuel 0 --ifuel 0"
let x509_get_fwid
  (fwid: B32.lbytes32 32ul)
: Tot (fwid_t)
=
  let fwid: fwid_payload_t = {
    fwid_hashAlg = OID_DIGEST_SHA256;
    fwid_value   = (|32ul, fwid|)
  } in
  (* Prf *) lemma_serialize_fwid_payload_size fwid;
  (* Prf *) (**) lemma_serialize_asn1_oid_TLV_size fwid.fwid_hashAlg;
  (* Prf *) (**) lemma_serialize_asn1_octet_string_TLV_size fwid.fwid_value;

(* return *) fwid
#pop-options
