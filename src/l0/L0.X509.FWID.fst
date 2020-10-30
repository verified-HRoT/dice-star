module L0.X509.FWID

open LowParse.Low.Base
// open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

// open X509.Crypto
// open X509.BasicFields
// open X509.ExtFields

open FStar.Integers

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

#set-options "--__temp_no_proj RIoT.X509.FWID"

let decl = ()

(* FWID
  ======
*)

let filter_fwid_payload_string
  (s: datatype_of_asn1_type OCTET_STRING)
: GTot bool
= //fst x' = OID_DIGEST_SHA256 &&
  v (s.ASN1.Base.len) = 32

let fwid_payload_t'
= (OID_DIGEST_SHA256) `envelop_OID_with_t`
  (parse_filter_refine filter_fwid_payload_string)

(* Serialier spec *)
let synth_fwid_payload_t
  (x': fwid_payload_t')
: GTot (fwid_payload_t)
= { fwid_hashAlg = fst x';
    fwid_value   = snd x' }

inline_for_extraction noextract
let synth_fwid_payload_t'
  (x: fwid_payload_t)
: Tot (x': fwid_payload_t' { x == synth_fwid_payload_t x' } )
= (x.fwid_hashAlg, x.fwid_value)

let parse_fwid_payload
=
  ((OID_DIGEST_SHA256) `parse_envelop_OID_with`
   (serialize_asn1_TLV_of_type OCTET_STRING
   `serialize_filter`
   filter_fwid_payload_string))
  `parse_synth`
  synth_fwid_payload_t

let serialize_fwid_payload
= serialize_synth
  (* p1 *) ((OID_DIGEST_SHA256) `parse_envelop_OID_with`
            (serialize_asn1_TLV_of_type OCTET_STRING
             `serialize_filter`
             filter_fwid_payload_string))
  (* f2 *) (synth_fwid_payload_t)
  (* s1 *) ((OID_DIGEST_SHA256) `serialize_envelop_OID_with`
            (serialize_asn1_TLV_of_type OCTET_STRING
             `serialize_filter`
             filter_fwid_payload_string))
  (* g1 *) (synth_fwid_payload_t')
  (* prf*) ()

let lemma_serialize_fwid_payload_unfold x
=
  lemma_serialize_envelop_OID_with_unfold
    (OID_DIGEST_SHA256)
    (serialize_asn1_TLV_of_type OCTET_STRING
     `serialize_filter`
     filter_fwid_payload_string)
    (synth_fwid_payload_t' x);
  serialize_synth_eq
  (* p1 *) ((OID_DIGEST_SHA256) `parse_envelop_OID_with`
            (serialize_asn1_TLV_of_type OCTET_STRING
             `serialize_filter`
             filter_fwid_payload_string))
  (* f2 *) (synth_fwid_payload_t)
  (* s1 *) ((OID_DIGEST_SHA256) `serialize_envelop_OID_with`
            (serialize_asn1_TLV_of_type OCTET_STRING
             `serialize_filter`
             filter_fwid_payload_string))
  (* g1 *) (synth_fwid_payload_t')
  (* prf*) ()
  (* in *) x

let lemma_serialize_fwid_payload_size x
= lemma_serialize_fwid_payload_unfold x;
  assert_norm (length_of_asn1_primitive_TLV x.fwid_hashAlg == 11);
  assert_norm (length_of_asn1_primitive_TLV x.fwid_value == 34)

let lemma_serialize_fwid_unfold x
= lemma_serialize_asn1_sequence_TLV_unfold serialize_fwid_payload x

let lemma_serialize_fwid_size x
= lemma_serialize_asn1_sequence_TLV_size serialize_fwid_payload x

let lemma_serialize_fwid_size_exact x
=
  lemma_serialize_fwid_unfold x;
  lemma_serialize_fwid_size x;
  lemma_serialize_fwid_payload_size x

(* Low *)
let serialize32_fwid_payload_backwards
= serialize32_synth_backwards
  // (* ls *) (serialize32_asn1_TLV_backwards_of_type OID
  //           `serialize32_nondep_then_backwards`
  //           serialize32_asn1_TLV_backwards_of_type OCTET_STRING
  //           `serialize32_filter_backwards`
  //           filter_fwid_payload)
  (* ls *) (serialize32_envelop_OID_with_backwards
              (OID_DIGEST_SHA256)
              (serialize32_asn1_TLV_backwards_of_type OCTET_STRING
               `serialize32_filter_backwards`
               filter_fwid_payload_string))
  (* f2 *) (synth_fwid_payload_t)
  (* g1 *) (synth_fwid_payload_t')
  (* g1'*) (synth_fwid_payload_t')
  (* prf*) ()

let serialize32_fwid_backwards
= coerce_serializer32_backwards
  (* s  *) (serialize_fwid)
  (* s32*) (serialize32_asn1_sequence_TLV_backwards
           (* ls *) (serialize32_fwid_payload_backwards))
  (* prf*) ()
