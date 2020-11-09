module ASN1.Spec.Value.StringCombinator

open ASN1.Spec.Base
open LowParse.Spec.Bytes

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers

module B32 = FStar.Bytes

noextract
val parse_asn1_string
  (t: asn1_type { t == IA5_STRING \/ t == PRINTABLE_STRING \/ t == OCTET_STRING })
  (len_of_string: datatype_of_asn1_type t -> asn1_value_int32_of_type t)
  (filter_string: (len: asn1_value_int32_of_type t)
                  -> (s32: B32.lbytes32 len)
                  -> GTot (bool))
  (synth_string: (len: asn1_value_int32_of_type t)
                 -> (s32: parse_filter_refine (filter_string len))
                 -> GTot (x: datatype_of_asn1_type t
                                  { len_of_string x== len }))
  (prf: unit { forall len. synth_injective (synth_string len) })
  (len: asn1_value_int32_of_type t)
: parser (parse_filter_kind (total_constant_size_parser_kind (v len)))
    (x: datatype_of_asn1_type t {len_of_string x == len})

noextract
val serialize_asn1_string
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
: serializer (parse_asn1_string t len_of_string filter_string synth_string prf len)

unfold
let predicate_serialize_asn1_string_unfold
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
  (x: datatype_of_asn1_type t { len_of_string x== len })
: Type0
= serialize (serialize_asn1_string t len_of_string filter_string synth_string synth_string_inverse prf len) x
  == serialize (serialize_flbytes (v len)) (synth_string_inverse len x)

val lemma_serialize_asn1_string_unfold
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
  (x: datatype_of_asn1_type t { len_of_string x== len })
: Lemma (
  predicate_serialize_asn1_string_unfold t len_of_string filter_string synth_string synth_string_inverse prf len x
)

unfold
let predicate_serialize_asn1_string_size
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
  (x: datatype_of_asn1_type t { len_of_string x== len })
: Type0
= let length = length_of_opaque_serialization (serialize_asn1_string t len_of_string filter_string synth_string synth_string_inverse prf len) x in
  length == v len /\
  len == len_of_string x /\
  asn1_value_length_inbound_of_type t length

val lemma_serialize_asn1_string_size
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
  (x: datatype_of_asn1_type t { len_of_string x== len })
: Lemma (
  predicate_serialize_asn1_string_size t len_of_string filter_string synth_string synth_string_inverse prf len x
)

noextract inline_for_extraction
val parser_tag_of_asn1_string
  (t: asn1_type { t == IA5_STRING \/ t == PRINTABLE_STRING \/ t == OCTET_STRING })
  (len_of_string: datatype_of_asn1_type t -> asn1_value_int32_of_type t)
  (x: datatype_of_asn1_type t)
: Tot (the_asn1_tag t `tuple2` asn1_value_int32_of_type t)

val synth_asn1_string_V
  (t: asn1_type { t == IA5_STRING \/ t == PRINTABLE_STRING \/ t == OCTET_STRING })
  (len_of_string: datatype_of_asn1_type t -> asn1_value_int32_of_type t)
  (tag: the_asn1_tag t `tuple2` asn1_value_int32_of_type t)
  (value: datatype_of_asn1_type t { v (len_of_string value) == v (snd tag) })
: GTot (refine_with_tag (parser_tag_of_asn1_string t len_of_string) tag)

noextract inline_for_extraction
val synth_asn1_string_V_inverse
  (t: asn1_type { t == IA5_STRING \/ t == PRINTABLE_STRING \/ t == OCTET_STRING })
  (len_of_string: datatype_of_asn1_type t -> asn1_value_int32_of_type t)
  (tag: the_asn1_tag t `tuple2` asn1_value_int32_of_type t)
  (value': refine_with_tag (parser_tag_of_asn1_string t len_of_string) tag)
: Tot (value: datatype_of_asn1_type t
               { v (len_of_string value) == v (snd tag) /\
                 value' == synth_asn1_string_V t len_of_string tag value })

val parse_asn1_string_V
  (t: asn1_type { t == IA5_STRING \/ t == PRINTABLE_STRING \/ t == OCTET_STRING })
  (len_of_string: datatype_of_asn1_type t -> asn1_value_int32_of_type t)
  (filter_string: (len: asn1_value_int32_of_type t)
                  -> (s32: B32.lbytes32 len)
                  -> GTot (bool))
  (synth_string: (len: asn1_value_int32_of_type t)
                       -> (s32: parse_filter_refine (filter_string len))
                       -> GTot (x: datatype_of_asn1_type t
                                  { len_of_string x== len }))
  (prf: unit { forall len. synth_injective (synth_string len) })
  (tag: the_asn1_tag t `tuple2` asn1_value_int32_of_type t)
: parser (weak_kind_of_type t) (refine_with_tag (parser_tag_of_asn1_string t len_of_string) tag)

val serialize_asn1_string_V
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
  (tag: the_asn1_tag t `tuple2` asn1_value_int32_of_type t)
: serializer (parse_asn1_string_V t len_of_string filter_string synth_string prf tag)

inline_for_extraction noextract
let parse_asn1_string_TLV_kind
  (t: asn1_type { t == IA5_STRING \/ t == PRINTABLE_STRING \/ t == OCTET_STRING })
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type t
  `and_then_kind`
  weak_kind_of_type t

val parse_asn1_string_TLV
  (t: asn1_type { t == IA5_STRING \/ t == PRINTABLE_STRING \/ t == OCTET_STRING })
  (len_of_string: datatype_of_asn1_type t -> asn1_value_int32_of_type t)
  (filter_string: (len: asn1_value_int32_of_type t)
                  -> (s32: B32.lbytes32 len)
                  -> GTot (bool))
  (synth_string: (len: asn1_value_int32_of_type t)
                       -> (s32: parse_filter_refine (filter_string len))
                       -> GTot (x: datatype_of_asn1_type t
                                  { len_of_string x== len }))
  (prf: unit { forall len. synth_injective (synth_string len) })
: parser (parse_asn1_string_TLV_kind t) (datatype_of_asn1_type t)

val serialize_asn1_string_TLV
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
: serializer (parse_asn1_string_TLV t len_of_string filter_string synth_string prf)

#push-options "--z3rlimit 32"
unfold
let predicate_serialize_asn1_string_TLV_unfold
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
  (x: datatype_of_asn1_type t)
: Type0
= serialize (serialize_asn1_string_TLV t len_of_string filter_string synth_string synth_string_inverse prf) x ==
  serialize (serialize_asn1_tag_of_type t) t
  `Seq.append`
  serialize (serialize_asn1_length_of_type t) (len_of_string x)
  `Seq.append`
  serialize (serialize_asn1_string t len_of_string filter_string synth_string synth_string_inverse prf (len_of_string x)) x

val lemma_serialize_asn1_string_TLV_unfold
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
  (x: datatype_of_asn1_type t)
: Lemma (
  predicate_serialize_asn1_string_TLV_unfold t len_of_string filter_string synth_string synth_string_inverse prf x
)

unfold
let predicate_serialize_asn1_string_TLV_size
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
  (x: datatype_of_asn1_type t)
: Type0
= let length: nat = length_of_opaque_serialization (serialize_asn1_string_TLV t len_of_string filter_string synth_string synth_string_inverse prf) x in
  length == 1 + length_of_asn1_length (len_of_string x) + v (len_of_string x) /\
  asn1_TLV_length_inbound_of_type t length

val  lemma_serialize_asn1_string_TLV_size
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
  (x: datatype_of_asn1_type t)
: Lemma (
  predicate_serialize_asn1_string_TLV_size t len_of_string filter_string synth_string synth_string_inverse prf x
)
#pop-options

(* Refined Version *)
let filter_asn1_string_with_character_bound
  (t: asn1_type { t == IA5_STRING \/ t == PRINTABLE_STRING \/ t == OCTET_STRING })
  (count_character: (x: datatype_of_asn1_type t) -> Tot (asn1_int32))
  (lb: asn1_value_int32_of_type t)
  (ub: asn1_value_int32_of_type t { lb <= ub })
  (x: datatype_of_asn1_type t)
: Tot (bool)
= lb <= count_character x && count_character x <= ub

noextract inline_for_extraction unfold
let asn1_string_with_character_bound_t
  (t: asn1_type { t == IA5_STRING \/ t == PRINTABLE_STRING \/ t == OCTET_STRING })
  (count_character: (x: datatype_of_asn1_type t) -> Tot (asn1_int32))
  (lb: asn1_value_int32_of_type t)
  (ub: asn1_value_int32_of_type t { lb <= ub })
= parse_filter_refine (filter_asn1_string_with_character_bound t count_character lb ub)

let parse_asn1_string_TLV_with_character_bound
  (t: asn1_type { t == IA5_STRING \/ t == PRINTABLE_STRING \/ t == OCTET_STRING })
  (len_of_string: datatype_of_asn1_type t -> asn1_value_int32_of_type t)
  (filter_string: (len: asn1_value_int32_of_type t)
                  -> (s32: B32.lbytes32 len)
                  -> GTot (bool))
  (synth_string: (len: asn1_value_int32_of_type t)
                       -> (s32: parse_filter_refine (filter_string len))
                       -> GTot (x: datatype_of_asn1_type t
                                  { len_of_string x== len }))
  (prf: unit { forall len. synth_injective (synth_string len) })
  (count_character: (x: datatype_of_asn1_type t) -> Tot (asn1_int32))
  (lb: asn1_value_int32_of_type t)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: parser (parse_asn1_string_TLV_kind t) (asn1_string_with_character_bound_t t count_character lb ub)
= parse_asn1_string_TLV t len_of_string filter_string synth_string prf
  `parse_filter`
  filter_asn1_string_with_character_bound t count_character lb ub

let serialize_asn1_string_TLV_with_character_bound
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
: serializer (parse_asn1_string_TLV_with_character_bound t len_of_string filter_string synth_string prf count_character lb ub)
= serialize_asn1_string_TLV t len_of_string filter_string synth_string synth_string_inverse prf
  `serialize_filter`
  filter_asn1_string_with_character_bound t count_character lb ub
