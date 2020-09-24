module ASN1.Low.Value.StringCombinator

open ASN1.Base
open ASN1.Spec.Value.StringCombinator
open ASN1.Low.Base
open LowParse.Low.Bytes

open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Low.Tag
open ASN1.Low.Length

open FStar.Integers

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

module B32 = FStar.Bytes

noextract inline_for_extraction
val serialize32_asn1_string_backwards
  (t: asn1_type { t == IA5_STRING \/ t == PRINTABLE_STRING \/ t == OCTET_STRING })
  (len_of_string: datatype_of_asn1_type t -> asn1_value_int32_of_type t)
  (filter_string: (len: asn1_value_int32_of_type t)
                  -> (s32: B32.lbytes32 len)
                  -> GTot (bool))
  (synth_string: (len: asn1_value_int32_of_type t)
                 -> (s32: parse_filter_refine (filter_string len))
                 -> GTot (x: datatype_of_asn1_type t
                            { len_of_string x== len }))
  (synth_string_inverse: (len: asn1_value_int32_of_type t)
                         -> (x: datatype_of_asn1_type t { len_of_string x== len })
                         -> (s32: parse_filter_refine (filter_string len)
                                 { x == synth_string len s32 }))
  (prf: unit { forall len. synth_injective (synth_string len) })
  (len: asn1_value_int32_of_type t)
: Tot (serializer32_backwards (serialize_asn1_string t len_of_string filter_string synth_string synth_string_inverse prf len))

noextract inline_for_extraction
val serialize32_asn1_string_TLV_backwards
  (t: asn1_type { t == IA5_STRING \/ t == PRINTABLE_STRING \/ t == OCTET_STRING })
  (len_of_string: datatype_of_asn1_type t -> asn1_value_int32_of_type t)
  (filter_string: (len: asn1_value_int32_of_type t)
                  -> (s32: B32.lbytes32 len)
                  -> GTot (bool))
  (synth_string: (len: asn1_value_int32_of_type t)
                       -> (s32: parse_filter_refine (filter_string len))
                       -> GTot (x: datatype_of_asn1_type t
                                  { len_of_string x== len }))
  (synth_string_inverse: (len: asn1_value_int32_of_type t)
                         -> (x: datatype_of_asn1_type t { len_of_string x== len })
                         -> (s32: parse_filter_refine (filter_string len)
                                 { x == synth_string len s32 }))
  (prf: unit { forall len. synth_injective (synth_string len) })
: serializer32_backwards (serialize_asn1_string_TLV t len_of_string filter_string synth_string synth_string_inverse prf)

noextract inline_for_extraction
val serialize32_asn1_string_TLV_with_character_bound_backwards
  (t: asn1_type { t == IA5_STRING \/ t == PRINTABLE_STRING \/ t == OCTET_STRING })
  (len_of_string: datatype_of_asn1_type t -> asn1_value_int32_of_type t)
  (filter_string: (len: asn1_value_int32_of_type t)
                  -> (s32: B32.lbytes32 len)
                  -> GTot (bool))
  (synth_string: (len: asn1_value_int32_of_type t)
                       -> (s32: parse_filter_refine (filter_string len))
                       -> GTot (x: datatype_of_asn1_type t
                                  { len_of_string x== len }))
  (synth_string_inverse: (len: asn1_value_int32_of_type t)
                         -> (x: datatype_of_asn1_type t { len_of_string x== len })
                         -> (s32: parse_filter_refine (filter_string len)
                                 { x == synth_string len s32 }))
  (prf: unit { forall len. synth_injective (synth_string len) })
  (count_character: (x: datatype_of_asn1_type t) -> Tot (asn1_int32))
  (lb: asn1_value_int32_of_type t)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: serializer32_backwards (serialize_asn1_string_TLV_with_character_bound t len_of_string filter_string synth_string synth_string_inverse prf count_character lb ub)
