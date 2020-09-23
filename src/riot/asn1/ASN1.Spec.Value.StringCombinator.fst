module ASN1.Spec.Value.StringCombinator

open ASN1.Spec.Base
open LowParse.Spec.Bytes

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers

module B32 = FStar.Bytes

let parse_asn1_string t len_of_string filter_string synth_string prf len
= parse_flbytes (v len)
  `parse_filter`
  filter_string len
  `parse_synth`
  synth_string len

let serialize_asn1_string t len_of_string filter_string synth_string synth_string_inverse prf len
= serialize_synth
  (* p1 *) (parse_flbytes (v len)
            `parse_filter`
            filter_string len)
  (* f2 *) (synth_string len)
  (* s1 *) (serialize_flbytes (v len)
            `serialize_filter`
            filter_string len)
  (* g1 *) (synth_string_inverse len)
  (* Prf*) (prf)


let lemma_serialize_asn1_string_unfold t len_of_string filter_string synth_string synth_string_inverse prf len x
= serialize_synth_eq
  (* p1 *) (parse_flbytes (v len)
            `parse_filter`
            filter_string len)
  (* f2 *) (synth_string len)
  (* s1 *) (serialize_flbytes (v len)
            `serialize_filter`
            filter_string len)
  (* g1 *) (synth_string_inverse len)
  (* Prf*) (prf)
  (* in *) (x)

let lemma_serialize_asn1_string_size t len_of_string filter_string synth_string synth_string_inverse prf len x
= lemma_serialize_asn1_string_unfold t len_of_string filter_string synth_string synth_string_inverse prf len x

let parser_tag_of_asn1_string t len_of_string x
= (t, len_of_string x)

let synth_asn1_string_V t len_of_string tag value
= value

noextract inline_for_extraction
let synth_asn1_string_V_inverse t len_of_string tag value'
= value'

let parse_asn1_string_V t len_of_string filter_string synth_string prf tag
= weak_kind_of_type t
  `weaken`
  parse_asn1_string t len_of_string filter_string synth_string prf (snd tag)
  `parse_synth`
  synth_asn1_string_V t len_of_string tag

let serialize_asn1_string_V t len_of_string filter_string synth_string synth_string_inverse prf tag
= serialize_synth
  (* p1 *) (weak_kind_of_type t
            `weaken`
            parse_asn1_string t len_of_string filter_string synth_string prf (snd tag))
  (* f2 *) (synth_asn1_string_V t len_of_string tag)
  (* s1 *) (weak_kind_of_type t
            `serialize_weaken`
            serialize_asn1_string t len_of_string filter_string synth_string synth_string_inverse prf (snd tag))
  (* g1 *) (synth_asn1_string_V_inverse t len_of_string tag)
  (* prf*) (prf)

let lemma_serialize_asn1_string_V_unfold
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
  (x: refine_with_tag (parser_tag_of_asn1_string t len_of_string) tag)
: Lemma (
  serialize (serialize_asn1_string_V t len_of_string filter_string synth_string synth_string_inverse prf tag) x ==
  serialize (serialize_asn1_string t len_of_string filter_string synth_string synth_string_inverse prf (snd tag)) x
)
= serialize_synth_eq
  (* p1 *) (weak_kind_of_type t
            `weaken`
            parse_asn1_string t len_of_string filter_string synth_string prf (snd tag))
  (* f2 *) (synth_asn1_string_V t len_of_string tag)
  (* s1 *) (weak_kind_of_type t
            `serialize_weaken`
            serialize_asn1_string t len_of_string filter_string synth_string synth_string_inverse prf (snd tag))
  (* g1 *) (synth_asn1_string_V_inverse t len_of_string tag)
  (* prf*) (prf)
  (* in *) (x)

let parse_asn1_string_TLV t len_of_string filter_string synth_string prf
= parse_tagged_union
  (* pt *) (parse_asn1_tag_of_type t
            `nondep_then`
            parse_asn1_length_of_type t)
  (* tg *) (parser_tag_of_asn1_string t len_of_string)
  (* p  *) (parse_asn1_string_V t len_of_string filter_string synth_string prf)

let serialize_asn1_string_TLV t len_of_string filter_string synth_string synth_string_inverse prf
= serialize_tagged_union
  (* st *) (serialize_asn1_tag_of_type t
            `serialize_nondep_then`
            serialize_asn1_length_of_type t)
  (* tg *) (parser_tag_of_asn1_string t len_of_string)
  (* s  *) (serialize_asn1_string_V t len_of_string filter_string synth_string synth_string_inverse prf)

#push-options "--z3rlimit 32"
let lemma_serialize_asn1_string_TLV_unfold t len_of_string filter_string synth_string synth_string_inverse prf x
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type t)
  (* s2 *) (serialize_asn1_length_of_type t)
  (* in *) (parser_tag_of_asn1_string t len_of_string x);
  lemma_serialize_asn1_string_V_unfold t len_of_string filter_string synth_string synth_string_inverse prf (parser_tag_of_asn1_string t len_of_string x) x;
  serialize_tagged_union_eq
  (* st *) (serialize_asn1_tag_of_type t
            `serialize_nondep_then`
            serialize_asn1_length_of_type t)
  (* tg *) (parser_tag_of_asn1_string t len_of_string)
  (* s  *) (serialize_asn1_string_V t len_of_string filter_string synth_string synth_string_inverse prf)
  (* in *) (x)


let lemma_serialize_asn1_string_TLV_size t len_of_string filter_string synth_string synth_string_inverse prf x
= lemma_serialize_asn1_string_TLV_unfold t len_of_string filter_string synth_string synth_string_inverse prf x;
  lemma_serialize_asn1_tag_of_type_size t t;
  lemma_serialize_asn1_length_size (len_of_string x);
  serialize_asn1_length_of_type_eq t (len_of_string x);
  lemma_serialize_asn1_string_size t len_of_string filter_string synth_string synth_string_inverse prf (len_of_string x) x
#pop-options

let filter_asn1_string_with_character_bound t count_character lb ub x
= lb <= count_character x && count_character x <= ub

let parse_asn1_string_TLV_with_character_bound t len_of_string filter_string synth_string prf count_character lb ub
= parse_asn1_string_TLV t len_of_string filter_string synth_string prf
  `parse_filter`
  filter_asn1_string_with_character_bound t count_character lb ub

let serialize_asn1_string_TLV_with_character_bound t len_of_string filter_string synth_string synth_string_inverse prf count_character lb ub
= serialize_asn1_string_TLV t len_of_string filter_string synth_string synth_string_inverse prf
  `serialize_filter`
  filter_asn1_string_with_character_bound t count_character lb ub
