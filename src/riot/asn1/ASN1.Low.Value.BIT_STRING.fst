module ASN1.Low.Value.BIT_STRING

open ASN1.Base
open ASN1.Spec.Value.BIT_STRING

open ASN1.Low.Base
open ASN1.Low.Tag
open ASN1.Low.Length

open LowParse.Low.Bytes

open FStar.Integers

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module B32 = FStar.Bytes

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length`, `ASN1.Spec.Value.OCTET_STRING` *)

#push-options "--z3rlimit 64"
inline_for_extraction
let serialize32_asn1_bit_string_backwards
  (len: asn1_value_int32_of_type BIT_STRING)
: Tot (serializer32_backwards (serialize_asn1_bit_string (v len)))
= fun (value: datatype_of_asn1_type BIT_STRING { v len == v (Mkbit_string_t?.bs_len value) })
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
->  (* Prf *) lemma_serialize_asn1_bit_string_unfold (v len) (value);
    (* Prf *) let h0 = HST.get () in
    // let (|len, unused_bits, s32|) = value in
    let leading_byte: byte = FStar.Int.Cast.uint32_to_uint8 value.bs_unused_bits in
    (* Prf *) writable_weaken
              (* buf *) b
              (*range*) (v pos - v len) (v pos)
              (* mem *) h0
              (* from*) (v pos - v len)
              (* to  *) (v pos - v len + 1);

    mbuffer_upd (* <-- NOTE: Serializing the leading "unused_bits" byte. *)
      (* buf *) b
      (*range*) (v pos - v len) (v pos)
      (* pos *) (pos - len)
      (* val *) leading_byte;

    (* Prf *) let h1 = HST.get () in
    (* Prf *) writable_modifies
              (* buf *) b
              (*range*) (v pos - v len) (v pos)
              (* mem *) h0
              (*other*) B.loc_none
              (* mem'*) h1;
    (* Prf *) writable_weaken
              (* buf *) b
              (*range*) (v pos - v len) (v pos)
              (* mem *) h1
              (* from*) (v pos - v len + 1)
              (* to  *) (v pos);

    store_bytes (* <-- NOTE: Serializing the following bytes. *)
      (* src *) value.bs_s
      (*range*) 0ul (len - 1ul)
      (* dst *) b
      (* pos *) (pos - len + 1ul);

    (* Prf *) let h2 = HST.get () in
    (* Prf *) B.modifies_buffer_from_to_elim
              (* buf *) b
              (*frame*) (pos - len) (pos - len + 1ul)
              (* new *) (B.loc_buffer_from_to b (pos - len + 1ul) pos)
              (* mem *) h1
              (* mem'*) h2;
    (* Prf *) Seq.lemma_split (Seq.slice (B.as_seq h2 b) (v pos - v len) (v pos)) 1;
(*return*) (Mkbit_string_t?.bs_len value)
#pop-options

inline_for_extraction
let parser_tag_of_bit_string_impl
  (x: datatype_of_asn1_type BIT_STRING)
: Tot (tg: (the_asn1_tag BIT_STRING & asn1_value_int32_of_type BIT_STRING) {
           tg == parser_tag_of_bit_string x
  })
= (BIT_STRING, (Mkbit_string_t?.bs_len x))

inline_for_extraction
let synth_asn1_bit_string_V_inverse_impl
  (tag: (the_asn1_tag BIT_STRING & asn1_value_int32_of_type BIT_STRING))
  (value': refine_with_tag parser_tag_of_bit_string tag)
: Tot (value: datatype_of_asn1_type BIT_STRING {
                 v (snd tag) == v (Mkbit_string_t?.bs_len value) /\
                 value == synth_asn1_bit_string_V_inverse tag value'})
= value'

// inline_for_extraction
let serialize32_asn1_bit_string_TLV_backwards ()
: Tot (serializer32_backwards (serialize_asn1_bit_string_TLV))
= serialize32_tagged_union_backwards
  (* lst *) (serialize32_asn1_tag_of_type_backwards BIT_STRING
             `serialize32_nondep_then_backwards`
             serialize32_asn1_length_of_type_backwards BIT_STRING)
  (* ltg *) (parser_tag_of_bit_string_impl)
  (* ls  *) (fun parser_tag -> (serialize32_synth_backwards
                              (* ls *) (weak_kind_of_type BIT_STRING
                                        `serialize32_weaken_backwards`
                                        serialize32_asn1_bit_string_backwards (snd parser_tag))
                              (* f2 *) (synth_asn1_bit_string_V parser_tag)
                              (* g1 *) (synth_asn1_bit_string_V_inverse parser_tag)
                              (* g1'*) (synth_asn1_bit_string_V_inverse_impl parser_tag)
                              (* prf*) ()))
