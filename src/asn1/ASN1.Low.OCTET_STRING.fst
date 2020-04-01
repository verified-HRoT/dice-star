module ASN1.Low.OCTET_STRING

open ASN1.Base
open ASN1.Spec.OCTET_STRING
open ASN1.Low.Base
open LowParse.Bytes

open FStar.Integers

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

let serialize32_asn1_octet_string
  (len: size_t)
: Tot (serializer32 (serialize_asn1_octet_string (v len)))
= fun (s: lbytes_t (v len))
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  store_seqbytes
    (* src *) s
    (* from*) 0ul
    (* to  *) len
    (* dst *) b
    (* pos *) pos;
(* retuen *) len

let serialize32_asn1_octet_string_backwards
  (len: size_t)
: Tot (serializer32_backwards (serialize_asn1_octet_string (v len)))
= fun (s: lbytes_t (v len))
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  (* Prf *) let h0 = HST.get () in

    store_seqbytes
    (* src *) s
    (* from*) 0ul
    (* to  *) len
    (* dst *) b
    (* pos *) (pos - len);

(* retuen *) len

open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Low.Tag
open ASN1.Low.Length

let parser_tag_of_octet_string_impl
  (x: datatype_of_asn1_type OCTET_STRING)
: Tot (tg: (the_asn1_type OCTET_STRING & asn1_int32_of_tag OCTET_STRING) {tg == parser_tag_of_octet_string x})
= (OCTET_STRING, dfst x)

let synth_asn1_octet_string_V_inverse_impl
  (len: asn1_int32_of_tag OCTET_STRING)
  (x: the_asn1_type OCTET_STRING & asn1_int32_of_tag OCTET_STRING{x == (OCTET_STRING, len)})
  (value: refine_with_tag parser_tag_of_octet_string x)
: Tot (s: lbytes (v len){s == synth_asn1_octet_string_V_inverse len x value})
= dsnd
    #asn1_int32
    #(fun (len:asn1_int32) -> s:bytes{Seq.length s == v len})
    value

let serialize32_asn1_octet_string_TLV_backwards ()
: Tot (serializer32_backwards serialize_asn1_octet_string_TLV)
= serialize32_tagged_union_backwards
  (* lst *) (serialize32_the_asn1_tag_backwards OCTET_STRING
             `serialize32_nondep_then_backwards`
             serialize32_asn1_length_of_tag_backwards OCTET_STRING)
  (* tg  *) (parser_tag_of_octet_string_impl)
  (* ls  *) (fun x -> let OCTET_STRING, len = x in
                    let l = v len in
                    (parse_asn1_octet_string_kind_weak
                    `serialize32_weaken_backwards`
                    (serialize32_synth_backwards
                     (* ls1 *) (serialize32_asn1_octet_string_backwards len)
                     (* f2  *) (synth_asn1_octet_string_V len x)
                     (* g1  *) (synth_asn1_octet_string_V_inverse len x)
                     (* g1' *) (synth_asn1_octet_string_V_inverse_impl len x)
                     (* Prf *) ())) <: serializer32_backwards (serialize_asn1_octet_string_data_weak x))
