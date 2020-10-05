module X509.BasicFields.Extensions

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec
open ASN1.Low

open X509.Base
open FStar.Integers

module B32 = FStar.Bytes

let x509_extensions_outmost_explicit_tag: asn1_tag_t
= CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 3uy

inline_for_extraction
let x509_extensions_t_inbound
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= inbound_envelop_tag_with_value_of
  (* tag *) x509_extensions_outmost_explicit_tag
  (*  s  *) s

let parse_x509_extensions_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: parser (parse_asn1_envelop_tag_with_TLV_kind x509_extensions_outmost_explicit_tag) (x509_extensions_t_inbound s)
= x509_extensions_t_inbound s
  `coerce_parser`
  parse_asn1_envelop_tag_with_TLV
  (* tag *) x509_extensions_outmost_explicit_tag
  (*  s  *) s

let serialize_x509_extensions_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: serializer (parse_x509_extensions_TLV s)
= coerce_parser_serializer
  (* p *) (parse_x509_extensions_TLV s)
  (* s *) (serialize_asn1_envelop_tag_with_TLV
           (* tag *) x509_extensions_outmost_explicit_tag
           (*  s  *) s)
  (*prf*) ()

val lemma_serialize_x509_extensions_TLV_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: x509_extensions_t_inbound s)
: Lemma ( predicate_serialize_asn1_envelop_tag_with_TLV_unfold x509_extensions_outmost_explicit_tag s x )

val lemma_serialize_x509_extensions_TLV_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: x509_extensions_t_inbound s)
: Lemma ( predicate_serialize_asn1_envelop_tag_with_TLV_size x509_extensions_outmost_explicit_tag s x )

unfold
[@@ "opaque_to_smt"]
let length_of_x509_extensions
  (l: asn1_value_length_of_type x509_extensions_outmost_explicit_tag)
: GTot (asn1_TLV_length_of_type x509_extensions_outmost_explicit_tag)
= length_of_TLV x509_extensions_outmost_explicit_tag l

noextract inline_for_extraction unfold
[@@ "opaque_to_smt"]
let len_of_x509_extensions
  (len_payload: asn1_value_int32_of_type x509_extensions_outmost_explicit_tag)
: Tot (len: asn1_TLV_int32_of_type x509_extensions_outmost_explicit_tag
            { v len == length_of_x509_extensions (v len_payload) })
= len_of_TLV x509_extensions_outmost_explicit_tag len_payload

inline_for_extraction
val serialize32_x509_extensions_TLV_backwards
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32_backwards s)
: serializer32_backwards (serialize_x509_extensions_TLV s)
