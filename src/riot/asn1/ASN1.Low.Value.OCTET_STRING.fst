module ASN1.Low.Value.OCTET_STRING

open ASN1.Base
open ASN1.Spec.Value.OCTET_STRING
open ASN1.Low.Base
open LowParse.Low.Bytes

open FStar.Integers

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

module B32 = FStar.Bytes

friend ASN1.Spec.Value.OCTET_STRING

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length` *)

let serialize32_asn1_octet_string_backwards len
= fun (value: datatype_of_asn1_type OCTET_STRING { v (dfst value) == v len })
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
->  (* Prf *) lemma_serialize_asn1_octet_string_unfold (v len) (value);

    store_bytes
    (* src *) (dsnd value)
    (* from*) 0ul
    (* to  *) len
    (* dst *) b
    (* pos *) (pos - len);

(* retuen *) len

open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Low.Tag
open ASN1.Low.Length

inline_for_extraction
let parser_tag_of_octet_string_impl
  (x: datatype_of_asn1_type OCTET_STRING)
: Tot (tg: (the_asn1_tag OCTET_STRING & asn1_value_int32_of_type OCTET_STRING) {tg == parser_tag_of_octet_string x})
= (OCTET_STRING, dfst x)

inline_for_extraction
let synth_asn1_octet_string_V_inverse_impl
  (tag: (the_asn1_tag OCTET_STRING & asn1_value_int32_of_type OCTET_STRING))
  (value': refine_with_tag parser_tag_of_octet_string tag)
: Tot (value: datatype_of_asn1_type OCTET_STRING { v (dfst value) == v (snd tag) /\ value == synth_asn1_octet_string_V_inverse tag value'})
= value'

// inline_for_extraction
let serialize32_asn1_octet_string_TLV_backwards ()
= serialize32_tagged_union_backwards
  (* lst *) (serialize32_asn1_tag_of_type_backwards OCTET_STRING
             `serialize32_nondep_then_backwards`
             serialize32_asn1_length_of_type_backwards OCTET_STRING)
  (* tg  *) (parser_tag_of_octet_string_impl)
  (* ls  *) (fun x -> (serialize32_synth_backwards
                     (* ls1 *) (weak_kind_of_type OCTET_STRING
                                `serialize32_weaken_backwards`
                                serialize32_asn1_octet_string_backwards (snd x))
                     (* f2  *) (synth_asn1_octet_string_V x)
                     (* g1  *) (synth_asn1_octet_string_V_inverse x)
                     (* g1' *) (synth_asn1_octet_string_V_inverse_impl x)
                     (* Prf *) ()))
