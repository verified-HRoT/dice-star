module ASN1.Low.Value.StringCombinator

open ASN1.Base
open ASN1.Spec.Value.StringCombinator
open ASN1.Low.Base
open LowParse.Low.Bytes

open ASN1.Low.Tag
open ASN1.Low.Length

open FStar.Integers

module B = LowStar.Buffer

module B32 = FStar.Bytes

friend ASN1.Spec.Value.StringCombinator

noextract inline_for_extraction
let serialize32_asn1_string_backwards
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
= fun (x: datatype_of_asn1_type t { v (len_of_string x) == v len })
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
-> (* Prf *) lemma_serialize_asn1_string_unfold t len_of_string filter_string synth_string synth_string_inverse prf len x;

    store_bytes
    (* src *) (synth_string_inverse len x)
    (* from*) 0ul
    (* to  *) len
    (* dst *) b
    (* pos *) (pos - len);

(* return *) len

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"
noextract inline_for_extraction
let serialize32_asn1_string_TLV_backwards
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
= serialize32_tagged_union_backwards
  (* lst*) (serialize32_asn1_tag_of_type_backwards t
            `serialize32_nondep_then_backwards`
            serialize32_asn1_length_of_type_backwards t)
  (* tg *) (fun x -> parser_tag_of_asn1_string t len_of_string x)
  (* ls *) (fun x -> (serialize32_synth_backwards
                    (* ls *) (weak_kind_of_type t
                              `serialize32_weaken_backwards`
                              serialize32_asn1_string_backwards t len_of_string filter_string synth_string synth_string_inverse prf (msnd x))
                    (* f2 *) (synth_asn1_string_V t len_of_string x)
                    (* g1 *) (synth_asn1_string_V_inverse t len_of_string x)
                    (* g1'*) (synth_asn1_string_V_inverse t len_of_string x)
                    (* prf*) ()))

noextract inline_for_extraction
let serialize32_asn1_string_TLV_with_character_bound_backwards
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
= serialize32_asn1_string_TLV_backwards t len_of_string filter_string synth_string synth_string_inverse prf
  `serialize32_filter_backwards`
  filter_asn1_string_with_character_bound t count_character lb ub
