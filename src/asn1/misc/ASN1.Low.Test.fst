module ASN1.Low.Test
open ASN1.Base
(*)
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Value.BOOLEAN
open ASN1.Spec.Value.NULL
open ASN1.Spec.Value.OCTET_STRING
// open ASN1.Spec.TLV

open ASN1.Low.Base
open ASN1.Low.Tag
open ASN1.Low.Length
open ASN1.Low.Value.BOOLEAN
open ASN1.Low.Value.NULL
open ASN1.Low.Value.OCTET_STRING
// open ASN1.Low.TLV

open LowParse.Low.Base
open LowParse.Low.Combinators
open LowParse.Bytes
open LowParse.Low.DER

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

module I = FStar.Integers

type ext = {
  b: datatype_of_asn1_type BOOLEAN;
  n: datatype_of_asn1_type NULL;
  s: datatype_of_asn1_type OCTET_STRING
}

let ext' = ((datatype_of_asn1_type BOOLEAN * datatype_of_asn1_type NULL) * datatype_of_asn1_type OCTET_STRING)

let synth_ext
  (x': ext')
: Tot (ext)
= let (b, n), s = x' in
  {b = b; n = n; s = s}

let synth_ext_inverse
  (x: ext)
: Tot (x': ext'{x == synth_ext x'})
= ((x.b, x.n), x.s)

let p
: parser _ ext
=((parse_asn1_boolean_TLV
  `nondep_then`
  parse_asn1_null_TLV)
  `nondep_then`
  parse_asn1_octet_string_TLV)
  `parse_synth`
  synth_ext

let s
: serializer p
= serialize_synth
  (* p1 *) ((parse_asn1_boolean_TLV
             `nondep_then`
             parse_asn1_null_TLV)
             `nondep_then`
             parse_asn1_octet_string_TLV)
  (* f2 *) (synth_ext)
  (* s1 *) ((serialize_asn1_boolean_TLV
             `serialize_nondep_then`
             serialize_asn1_null_TLV)
             `serialize_nondep_then`
             serialize_asn1_octet_string_TLV)
  (* g1 *) (synth_ext_inverse)
  (* prf*) ()


let synth_ext_inverse_impl
  (x: ext)
: Tot (x': ext'{x' == synth_ext_inverse x})
= ((x.b, x.n), x.s)

let s32
: serializer32_backwards s
= serialize32_synth_backwards
  (* ls1*) (((serialize32_asn1_boolean_TLV_backwards ()
              `serialize32_nondep_then_backwards`
              serialize32_asn1_null_TLV_backwards ())
              `serialize32_nondep_then_backwards`
              serialize32_asn1_octet_string_TLV_backwards ()))
  (* f2 *) (synth_ext)
  (* g1 *) (synth_ext_inverse)
  (* lg1*) (synth_ext_inverse_impl)
  (* prf*) ()


/// Old example
///
type ext_inner = {
  b1: asn1_value;
  n1: asn1_value;
}

type extension = {
  s1: asn1_value;
  sq: ext_inner;
  s2: asn1_value;
}

let extension' = (((asn1_value * asn1_value) * asn1_value) * asn1_value)

let synth_extension
  (e': extension')
: GTot extension
= let ((s1, b1), n1), s2 = e' in
  {s1 = s1; sq = {b1 = b1; n1 = n1}; s2 = s2}

let synth_extension_inverse
  (e: extension)
: GTot extension'
= (((e.s1, e.sq.b1), e.sq.n1), e.s2)

let p
: parser _ extension
=((parse_TLV
  `nondep_then`
  parse_TLV)
  `nondep_then`
  parse_TLV)
  `nondep_then`
  parse_TLV
  `parse_synth`
  synth_extension

let s
: serializer p
= serialize_synth
  (* p1 *) (((parse_TLV
              `nondep_then`
              parse_TLV)
              `nondep_then`
              parse_TLV)
              `nondep_then`
              parse_TLV)
  (* f2 *) (synth_extension)
  (* s1 *) (((serialize_TLV
              `serialize_nondep_then`
              serialize_TLV)
              `serialize_nondep_then`
              serialize_TLV)
              `serialize_nondep_then`
              serialize_TLV)
  (* g1 *) (synth_extension_inverse)
  (* prf*) ()

let synth_extension_inverse_impl
  (e: extension)
: Tot (e': extension'{e' == synth_extension_inverse e})
= (((e.s1, e.sq.b1), e.sq.n1), e.s2)

let s32
: serializer32_backwards s
= serialize32_synth_backwards
  (* ls1*) (((serialize32_asn1_TLV_backwards ()
              `serialize32_nondep_then_backwards`
              serialize32_asn1_TLV_backwards ())
              `serialize32_nondep_then_backwards`
              serialize32_asn1_TLV_backwards ())
              `serialize32_nondep_then_backwards`
              serialize32_asn1_TLV_backwards ())
  (* f2 *) (synth_extension)
  (* g1 *) (synth_extension_inverse)
  (* lg1*) (synth_extension_inverse_impl)
  (* prf*) ()

let t = {
  s1 = OCTET_STRING_VALUE 2ul (Seq.seq_of_list [1uy; 2uy]);
  sq = {
    b1 = BOOLEAN_VALUE true;
    n1 = NULL_VALUE ()
  };
  s2 = OCTET_STRING_VALUE 1ul (Seq.seq_of_list [1uy])
}

open I

let s32_test
  (size: size_t{v size > Seq.length (serialize s t)})
  (b: B.buffer byte_t{B.length b == v size})
: HST.Stack unit
  (requires fun h -> B.live h b)
  (ensures fun h _ h' ->
    let sx = serialize s t in
    let s' = B.as_seq h' b in
    B.modifies (B.loc_buffer_from_to b (size - u (Seq.length sx)) size) h h' /\
    Seq.slice s' (v size - Seq.length sx) (v size) == sx)
= HST.push_frame ();
  let _ = s32 t b size in
  HST.pop_frame ()
