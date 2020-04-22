module ASN1.Low.BIT_STRING

open ASN1.Base
open ASN1.Spec.BIT_STRING

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

// let encode_asn1_bit_string
//   (len: asn1_int32_of_type BIT_STRING)
//   (x: datatype_of_asn1_type BIT_STRING {
//            let (|bits, s|) = x in
//            let bytes_length = normalize_term ((bits + 7) / 8) in
//            let unused_bits = normalize_term ((bytes_length * 8) - bits) in
//            v len == bytes_length + 1 })
// : Tot (ls: parse_filter_refine (filter_asn1_bit_string (v len)) { ls == synth_asn1_bit_string_inverse (v len) x })
// = let (|bits, s|) = x in
//   let bytes_len: len:asn1_int32 { v len <= asn1_length_max - 1 } = len - 1ul in
//   let unused_bits: n:nat{0 <= n /\ n <= 7} = normalize_term ((v bytes_len * 8) - bits) in
//   // assert (Seq.length s == bytes_length);
//   let ls: parse_filter_refine (filter_asn1_bit_string (v len))
//       = normalize_term (Seq.create 1 (u unused_bits) `Seq.append` s) in
//   // assert_norm (bytes_length == 0 ==>
//   //                unused_bits == 0);
//   // assert_norm (bytes_length <> 0 ==>
//   //                unused_bits <= 7 /\
//   //               (bytes_length * 8 - unused_bits == bits));
//   // assert (Seq.slice ls 1 l `Seq.equal` s);
//   // assert (x == synth_asn1_bit_string l ls);
//   ls

// let encode_asn1_bit_string
//   (l: asn1_length_of_type BIT_STRING)
//   (value: datatype_of_asn1_type BIT_STRING {
//           let (|len, unused_bits, s|) = value in
//           l == v len })
// : Tot (raw: parse_filter_refine (filter_asn1_bit_string l) { raw == synth_asn1_bit_string_inverse l value })
// = let raw = B32.create 1ul ()

//   let (|len, unused_bits, s32|) = value in
//   let raw = cast unused_bits `Seq.cons` B32.reveal s32 in
//   let (|len', unused_bits', s32'|) = synth_asn1_bit_string l raw in
//   B32.extensionality s32 s32';
//   raw

#push-options "--query_stats --z3rlimit 32"
let serialize32_asn1_bit_string_backwards
  (len: asn1_int32_of_type BIT_STRING)
: Tot (serializer32_backwards (serialize_asn1_bit_string (v len)))
= fun (value: datatype_of_asn1_type BIT_STRING {
            let (|len', unused_bits, s|) = value in
            v len == v len' })
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  (* Prf *) serialize_asn1_bit_string_unfold (v len) (value);
    (* Prf *) let h0 = HST.get () in
    let (|len, unused_bits, s32|) = value in
    let leading_byte: byte = cast unused_bits in
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
      (* src *) s32
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
(*return*) len

let parser_tag_of_bit_string_impl
  (x: datatype_of_asn1_type BIT_STRING)
: Tot (tg: (the_asn1_type BIT_STRING & asn1_int32_of_type BIT_STRING) {
           tg == parser_tag_of_bit_string x
  })
= let (|len, unused_bits, s32|) = x in
  (BIT_STRING, len)

let synth_asn1_bit_string_TLV_inverse_impl
  (tag: (the_asn1_type BIT_STRING & asn1_int32_of_type BIT_STRING))
  (value': refine_with_tag parser_tag_of_bit_string tag)
: Tot (value: datatype_of_asn1_type BIT_STRING {
                 let (|len, unused_bits, s|) = value in
                 v (snd tag) == v len /\
                 value == synth_asn1_bit_string_TLV_inverse tag value'})
= value'

let serialize32_asn1_bit_string_TLV_backwards ()
: Tot (serializer32_backwards (serialize_asn1_bit_string_TLV))
= serialize32_tagged_union_backwards
  (* lst *) (serialize32_the_asn1_tag_backwards BIT_STRING
             `serialize32_nondep_then_backwards`
             serialize32_asn1_length_of_type_backwards BIT_STRING)
  (* ltg *) (parser_tag_of_bit_string_impl)
  (* ls  *) (fun parser_tag -> (serialize32_synth_backwards
                              (* ls *) (weak_kind_of_type BIT_STRING
                                        `serialize32_weaken_backwards`
                                        serialize32_asn1_bit_string_backwards (snd parser_tag))
                              (* f2 *) (synth_asn1_bit_string_TLV parser_tag)
                              (* g1 *) (synth_asn1_bit_string_TLV_inverse parser_tag)
                              (* g1'*) (synth_asn1_bit_string_TLV_inverse_impl parser_tag)
                              (* prf*) ()))
