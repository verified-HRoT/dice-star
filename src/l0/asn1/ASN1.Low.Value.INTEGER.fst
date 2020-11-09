module ASN1.Low.Value.INTEGER

open ASN1.Base
open ASN1.Spec.Value.INTEGER
open ASN1.Low.Base
open LowParse.Bytes

open FStar.Integers

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module E = LowParse.Endianness
module LE = LowParse.Low.Endianness

friend ASN1.Spec.Value.INTEGER

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length` *)

#set-options "--z3rlimit 256 --fuel 0 --ifuel 0"

(*
NOTE: Since there are no low-level machine-integer to bytes implementations
      available, the (big-endian) serialization of integers are tricky. For
      1-byte, 2-byte and 4-byte integers, we could use `LowStar.Endianness`
      16-bit, 32-bit integer store interfaces. For 3-byte, we need to store
      the first 2 bytes and the last byte separately.
*)
inline_for_extraction noextract
let serialize32_asn1_integer_backwards_1byte_without_leading_zero
  (len: asn1_value_int32_of_type INTEGER)
: Tot (serializer32_backwards (serialize_asn1_integer (v len)
                               `serialize_filter`
                              (fun (value: datatype_of_asn1_type INTEGER { v len == length_of_asn1_integer value })
                                 -> 0l <= value && value <= 0x7Fl)))
= fun (value)//: datatype_of_asn1_type INTEGER { v len == length_of_asn1_integer value })
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
->(* Prf *) lemma_serialize_asn1_integer_unfold (length_of_asn1_integer value) value;
  (* Prf *) lemma_serialize_asn1_integer_size (length_of_asn1_integer value) value;
  let b0: byte = FStar.Int.Cast.int32_to_uint8 value in
  (* Prf *) E.reveal_be_to_n (Seq.create 1 b0);
  (* Prf *) E.reveal_be_to_n (Seq.slice (Seq.create 1 b0) 1 1);
  mbuffer_upd (* <-- NOTE: Serializing the 1-byte integer. *)
    (* dst *) b
    (*range*) (v pos - 1) (v pos)
    (* pos *) (pos - 1ul)
    (* val *) b0;
(*return*) 1ul

inline_for_extraction noextract
let serialize32_asn1_integer_backwards_2byte_with_leading_zero
  (len: asn1_value_int32_of_type INTEGER)
: Tot (serializer32_backwards (serialize_asn1_integer (v len)
                               `serialize_filter`
                              (fun (value: datatype_of_asn1_type INTEGER { v len == length_of_asn1_integer value })
                                 -> 0x7Fl < value && value <= 0xFFl)))
= fun (value)//: datatype_of_asn1_type INTEGER { v len == length_of_asn1_integer value })
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
->(* Prf *) lemma_serialize_asn1_integer_unfold (length_of_asn1_integer value) value;
  (* Prf *) lemma_serialize_asn1_integer_size (length_of_asn1_integer value) value;
  (* Prf *) let h0 = HST.get () in
  (* Prf *) writable_weaken
            (* buf *) b
            (*range*) (v pos - 2) (v pos)
            (* mem *) h0
            (* from*) (v pos - 2)
            (* to  *) (v pos - 1);
  mbuffer_upd (* <-- NOTE: Serializing the leading zero. *)
    (* dst *) b
    (*range*) (v pos - 2) (v pos - 1)
    (* pos *) (pos - 2ul)
    (* val *) 0x00uy;
  (* Prf *) let h1 = HST.get () in
  (* Prf *) writable_modifies
            (* buf *) b
            (*range*) (v pos - 2) (v pos)
            (* mem *) h0
            (* loc *) (B.loc_none)
            (* mem *) h1;
  (* Prf *) writable_weaken
            (* buf *) b
            (*range*) (v pos - 2) (v pos)
            (* mem *) h1
            (* from*) (v pos - 1)
            (* to  *) (v pos);
  let b0: byte = FStar.Int.Cast.int32_to_uint8 value in
  (* Prf *) E.reveal_be_to_n (Seq.create 1 b0);
  (* Prf *) E.reveal_be_to_n (Seq.slice (Seq.create 1 b0) 1 1);
  mbuffer_upd (* <-- NOTE: Serializing the 1-byte integer. *)
    (* dst *) b
    (*range*) (v pos - 2) (v pos)
    (* pos *) (pos - 1ul)
    (* val *) b0;
  (* Prf *) let h2 = HST.get () in
  (* Prf *) B.modifies_buffer_from_to_elim
            (* buf *) b
            (*frame*) (pos - 2ul) (pos - 1ul)
            (* new *) (B.loc_buffer_from_to b (pos - 1ul) (pos))
            (* mem *) h1 h2;
  (* Prf *) Seq.lemma_split (Seq.slice (B.as_seq h2 b) (v pos - 2) (v pos)) 1;
(*return*) 2ul

inline_for_extraction noextract
let serialize32_asn1_integer_backwards_2byte_without_leading_zero
  (len: asn1_value_int32_of_type INTEGER)
: Tot (serializer32_backwards (serialize_asn1_integer (v len)
                               `serialize_filter`
                              (fun (value: datatype_of_asn1_type INTEGER { v len == length_of_asn1_integer value })
                                 -> 0xFFl < value && value <= 0x7FFFl)))
= fun (value)//: datatype_of_asn1_type INTEGER { v len == length_of_asn1_integer value })
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
->(* Prf *) lemma_serialize_asn1_integer_unfold (length_of_asn1_integer value) value;
  (* Prf *) lemma_serialize_asn1_integer_size (length_of_asn1_integer value) value;
  (* Prf *) let h0 = HST.get () in
  (* Prf *) LE.writable_store_pre
            (* buf *) b
            (* from*) (v pos - 2)
            (* len *) 2
            (*  p  *) (fun s -> E.be_to_n s == v #(Signed W32) value)
            (* mem *) h0;
  LE.store16_be_i  (* <-- NOTE: Serializing the 2-byte integer. *)
    (* buf *) b
    (* pos *) (pos - 2ul)
    (* val *) (FStar.Int.Cast.int32_to_uint16 value);
  (* Prf *) let h1 = HST.get () in
  (* Prf *) LE.store_post_modifies
            (* buf *) b
            (* from*) (v pos - 2)
            (* len *) 2
            (*  p  *) (fun s -> E.be_to_n s == v #(Signed W32) value)
            (* mem *) h0 h1;
(*return*) 2ul

inline_for_extraction noextract
let serialize32_asn1_integer_backwards_3byte_with_leading_zero
  (len: asn1_value_int32_of_type INTEGER)
: Tot (serializer32_backwards (serialize_asn1_integer (v len)
                               `serialize_filter`
                              (fun (value: datatype_of_asn1_type INTEGER { v len == length_of_asn1_integer value })
                                 -> 0x7FFFl < value && value <= 0xFFFFl)))
= fun (value)//: datatype_of_asn1_type INTEGER { v len == length_of_asn1_integer value })
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
->(* Prf *) lemma_serialize_asn1_integer_unfold (length_of_asn1_integer value) value;
  (* Prf *) lemma_serialize_asn1_integer_size (length_of_asn1_integer value) value;
  (* Prf *) let h0 = HST.get () in
  (* Prf *) writable_weaken
            (* buf *) b
            (*range*) (v pos - 3) (v pos)
            (* mem *) h0
            (* from*) (v pos - 3)
            (* to  *) (v pos - 2);
  mbuffer_upd  (* <-- NOTE: Serializing the leading zero. *)
    (* buf *) b
    (*range*) (v pos - 3) (v pos)
    (* pos *) (pos - 3ul)
    (* val *) 0x00uy;
  (* Prf *) let h1 = HST.get () in
  (* Prf *) writable_modifies
            (* buf *) b
            (*range*) (v pos - 3) (v pos)
            (* mem *) h0
            (*other*) B.loc_none
            (* mem'*) h1;
  (* Prf *) writable_weaken
            (* buf *) b
            (*range*) (v pos - 3) (v pos)
            (* mem *) h1
            (* from*) (v pos - 2)
            (* to  *) (v pos);
  (* Prf *) LE.writable_store_pre
            (* buf *) b
            (* from*) (v pos - 2)
            (* len *) 2
            (*  p  *) (fun s -> E.be_to_n s == v #(Signed W32) value)
            (* mem *) h1;
  LE.store16_be_i (* <-- NOTE: Serializing the 2-byte integer. *)
    (* buf *) b
    (* pos *) (pos - 2ul)
    (* val *) (FStar.Int.Cast.int32_to_uint16 value);
  (* Prf *) let h2 = HST.get () in
  (* Prf *) LE.store_post_modifies
            (* buf *) b
            (* from*) (v pos - 2)
            (* len *) 2
            (*  p  *) (fun s -> E.be_to_n s == v #(Signed W32) value)
            (* mem *) h1
            (* mem'*) h2;
  (* Prf *) B.modifies_buffer_from_to_elim
            (* buf *) b
            (*frame*) (pos - 3ul) (pos - 2ul)
            (* new *) (B.loc_buffer_from_to b (pos - 2ul) pos)
            (* mem *) h1
            (* mem'*) h2;
  (* Prf *) Seq.lemma_split (Seq.slice (B.as_seq h2 b) (v pos - 3) (v pos)) 1;
(*return*) 3ul

inline_for_extraction noextract
let serialize32_asn1_integer_backwards_3byte_without_leading_zero
  (len: asn1_value_int32_of_type INTEGER)
: Tot (serializer32_backwards (serialize_asn1_integer (v len)
                               `serialize_filter`
                              (fun (value: datatype_of_asn1_type INTEGER { v len == length_of_asn1_integer value })
                                 -> 0xFFFFl < value && value <= 0x7FFFFFl)))
= fun (value)//: datatype_of_asn1_type INTEGER { v len == length_of_asn1_integer value })
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
->(* Prf *) lemma_serialize_asn1_integer_unfold (length_of_asn1_integer value) value;
  (* Prf *) lemma_serialize_asn1_integer_size (length_of_asn1_integer value) value;
  (* Prf *) assert_norm (v #(Signed W32) value < pow2 (8 * 3 - 1) /\
                         v #(Signed W32) value < pow2 (8 * 3));
  (* Prf *) E.reveal_n_to_be 3 (v #(Signed W32) value);
  (* Prf *) let h0 = HST.get () in
  (* Prf *) writable_weaken
            (* buf *) b
            (*range*) (v pos - 3) (v pos)
            (* mem *) h0
            (* from*) (v pos - 3)
            (* to  *) (v pos - 1);
  let first_2_bytes: uint_16 = FStar.Int.Cast.int32_to_uint16 (normalize_term (value / 0x100l)) in
  (* Prf *) LE.writable_store_pre
            (* buf *) b
            (* from*) (v pos - 3)
            (* len *) 2
            (*  p  *) (fun s -> E.be_to_n s == v first_2_bytes)
            (* mem *) h0;
  LE.store16_be_i  (* NOTE: <-- Serializing the first 2 bytes *)
    (* buf *) b
    (* pos *) (pos - 3ul)
    (* val *) first_2_bytes;
  (* Prf *) let h1 = HST.get () in
  (* Prf *) LE.store_post_modifies
            (* buf *) b
            (* from*) (v pos - 3)
            (* len *) 2
            (*  p  *) (fun s -> E.be_to_n s == v first_2_bytes)
            (* mem *) h0
            (* mem'*) h1;
  (* Prf *) writable_modifies
            (* buf *) b
            (*range*) (v pos - 3) (v pos)
            (* mem *) h0
            (*other*) B.loc_none
            (* mem'*) h1;
  (* Prf *) writable_weaken
            (* buf *) b
            (*range*) (v pos - 3) (v pos)
            (* mem *) h1
            (* from*) (v pos - 1)
            (* to  *) (v pos);
  let last_byte: uint_8 = FStar.Int.Cast.int32_to_uint8 (normalize_term (value % 0x100l)) in
  mbuffer_upd  (* NOTE: <-- Serializing the last byte *)
    (* buf *) b
    (*range*) (v pos - 3) (v pos)
    (* pos *) (pos - 1ul)
    (* val *) last_byte;
  (* Prf *) let h2 = HST.get () in
  (* Prf *) B.modifies_buffer_from_to_elim
            (* buf *) b
            (*frame*) (pos - 3ul) (pos - 1ul)
            (* new *) (B.loc_buffer_from_to b (pos - 1ul) pos)
            (* mem *) h1
            (* mem'*) h2;
   (* Prf *) Seq.lemma_split (Seq.slice (B.as_seq h2 b) (v pos - 3) (v pos)) 2;
(*return*) 3ul


inline_for_extraction noextract
let serialize32_asn1_integer_backwards_4byte_with_leading_zero
  (len: asn1_value_int32_of_type INTEGER)
: Tot (serializer32_backwards (serialize_asn1_integer (v len)
                               `serialize_filter`
                              (fun (value: datatype_of_asn1_type INTEGER { v len == length_of_asn1_integer value })
                                 -> 0x7FFFFFl < value && value <= 0xFFFFFFl)))
= fun (value)//: datatype_of_asn1_type INTEGER { v len == length_of_asn1_integer value })
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
->(* Prf *) lemma_serialize_asn1_integer_unfold (length_of_asn1_integer value) value;
  (* Prf *) lemma_serialize_asn1_integer_size (length_of_asn1_integer value) value;
  (* Prf *) assert_norm (v #(Signed W32) value < pow2 (8 * 3));
  (* Prf *) E.reveal_n_to_be 3 (v #(Signed W32) value);
  (* Prf *) let h0 = HST.get () in
  (* Prf *) writable_weaken
            (* buf *) b
            (*range*) (v pos - 4) (v pos)
            (* mem *) h0
            (* from*) (v pos - 4)
            (* to  *) (v pos - 3);
  mbuffer_upd
    (* buf *) b
    (*range*) (v pos - 4) (v pos)
    (* pos *) (pos - 4ul)
    (* val *) 0x00uy;
  (* Prf *)let h1 = HST.get () in
  (* Prf *) writable_modifies
            (* buf *) b
            (*range*) (v pos - 4) (v pos)
            (* mem *) h0
            (*other*) B.loc_none
            (* mem'*) h1;
  (* Prf *) writable_weaken
            (* buf *) b
            (*range*) (v pos - 4) (v pos)
            (* mem *) h1
            (* from*) (v pos - 3)
            (* to  *) (v pos - 1);
  let first_2_bytes: uint_16 = FStar.Int.Cast.int32_to_uint16 (normalize_term (value / 0x100l)) in
  (* Prf *) LE.writable_store_pre
            (* buf *) b
            (* from*) (v pos - 3)
            (* len *) 2
            (*  p  *) (fun s -> E.be_to_n s == v first_2_bytes)
            (* mem *) h1;
  LE.store16_be_i
    (* buf *) b
    (* pos *) (pos - 3ul)
    (* val *) first_2_bytes;
  (* Prf *)let h2 = HST.get () in
  (* Prf *) LE.store_post_modifies
            (* buf *) b
            (* from*) (v pos - 3)
            (* len *) 2
            (*  p  *) (fun s -> E.be_to_n s == v first_2_bytes)
            (* mem *) h1
            (* mem'*) h2;
  (* Prf *) B.modifies_buffer_from_to_elim
            (* buf *) b
            (*frame*) (pos - 4ul) (pos - 3ul)
            (* new *) (B.loc_buffer_from_to b (pos - 3ul) (pos - 1ul))
            (* mem *) h1
            (* mem'*) h2;
  (* Prf *) Seq.lemma_split (Seq.slice (B.as_seq h2 b) (v pos - 4) (v pos)) 1;
  (* Prf *) writable_modifies
            (* buf *) b
            (*range*) (v pos - 4) (v pos)
            (* mem *) h1
            (*other*) B.loc_none
            (* mem'*) h2;
  (* Prf *) writable_weaken
            (* buf *) b
            (*range*) (v pos - 4) (v pos)
            (* mem *) h2
            (* from*) (v pos - 1)
            (* to  *) (v pos);
  let last_byte: uint_8 = FStar.Int.Cast.int32_to_uint8 (normalize_term (value % 0x100l)) in
  mbuffer_upd
    (* buf *) b
    (*range*) (v pos - 4) (v pos)
    (* pos *) (pos - 1ul)
    (* val *) last_byte;
  (* Prf *) let h3 = HST.get () in
  (* Prf *) B.modifies_buffer_from_to_elim
            (* buf *) b
            (*frame*) (pos - 4ul) (pos - 1ul)
            (* new *) (B.loc_buffer_from_to b (pos - 1ul) pos)
            (* mem *) h2
            (* mem'*) h3;
  (* Prf *) Seq.lemma_split (Seq.slice (B.as_seq h3 b) (v pos - 4) (v pos)) 1;
  (* Prf *) Seq.lemma_split (Seq.slice (B.as_seq h3 b) (v pos - 4) (v pos)) 3;
(*return*) 4ul


inline_for_extraction noextract
let serialize32_asn1_integer_backwards_4byte_without_leading_zero
  (len: asn1_value_int32_of_type INTEGER)
: Tot (serializer32_backwards (serialize_asn1_integer (v len)
                               `serialize_filter`
                              (fun (value: datatype_of_asn1_type INTEGER { v len == length_of_asn1_integer value })
                                 -> 0xFFFFFFl < value && value <= 0x7FFFFFFFl)))
= fun value//: datatype_of_asn1_type INTEGER { v len == length_of_asn1_integer value })
    #rrel #rel
    b pos
->(* Prf *) lemma_serialize_asn1_integer_unfold (length_of_asn1_integer value) value;
  (* Prf *) lemma_serialize_asn1_integer_size (length_of_asn1_integer value) value;
  (* Prf *) assert_norm (v #(Signed W32) value < pow2 (8 * 4 - 1) /\
                         v #(Signed W32) value < pow2 (8 * 4));
  let value_of_all_4_bytes: uint_32 = (FStar.Int.Cast.int32_to_uint32 value) in
  (* Prf *) let h0 = HST.get () in
  (* Prf *) LE.writable_store_pre
            (* buf *) b
            (* from*) (v pos - 4)
            (* len *) 4
            (*  p  *) (fun s -> E.be_to_n s == v value_of_all_4_bytes)
            (* mem *) h0;
  LE.store32_be_i
  (* buf *) b
     (* pos *) (pos - 4ul)
     (* val *) value_of_all_4_bytes;
  (* Prf *) let h1 = HST.get () in
  (* Prf *) LE.store_post_modifies
            (* buf *) b
            (* from*) (v pos - 4)
            (* len *) 4
            (*  p  *) (fun s -> E.be_to_n s == v value_of_all_4_bytes)
            (* mem *) h0
            (* mem'*) h1;
(*return*) 4ul

let serialize32_asn1_integer_backwards len
= fun value
    #rrel #rel
    b
    pos
->
  (* Using 1 byte to store a 1-byte integer with the most-significant bit `0` *)
  if      (0l         <= value && value <= 0x7Fl      ) then
  ( serialize32_asn1_integer_backwards_1byte_without_leading_zero len value b pos )

  (* Using 2 bytes to store a 1-byte integer with the most-significant bit `1` *)
  else if (0x7Fl       < value && value <= 0xFFl      ) then
  ( serialize32_asn1_integer_backwards_2byte_with_leading_zero    len value b pos )

  (* Using 2 bytes to store a 2-byte integer with the most-significant bit `0` *)
  else if (0xFFl       < value && value <= 0x7FFFl    ) then
  ( serialize32_asn1_integer_backwards_2byte_without_leading_zero len value b pos )

  (* Using 3 bytes to store a 2-byte integer with the most-significant bit `1` *)
  else if (0x7FFFl       < value && value <= 0xFFFFl    ) then
  ( serialize32_asn1_integer_backwards_3byte_with_leading_zero    len value b pos )

  (* Using 3 bytes to store a 3-byte integer with the most-significant bit `0` *)
  else if (0xFFFFl      < value && value <= 0x7FFFFFl  ) then
  ( serialize32_asn1_integer_backwards_3byte_without_leading_zero len value b pos )

  (* Using 4 bytes to store a 3-byte integer with the most-significant bit `1` *)
  else if (0x7FFFFFl      < value && value <= 0xFFFFFFl  ) then
  ( serialize32_asn1_integer_backwards_4byte_with_leading_zero    len value b pos )

  (* Using 4 bytes to store a 4-byte integer with the most-significant bit `0` *)
  else if (0xFFFFFFl    < value && value <= 0x7FFFFFFFl) then
  ( serialize32_asn1_integer_backwards_4byte_without_leading_zero len value b pos )

  (* Unreachable *)
  else
  ( let () = false_elim () in
    LowStar.Failure.failwith "Error: Statically unreachable." )


let parser_tag_of_asn1_integer_impl value
= (INTEGER, len_of_asn1_integer value)

let synth_asn1_integer_V_inverse_impl tag value'
= value'

open ASN1.Low.Tag
open ASN1.Low.Length

// inline_for_extraction
let serialize32_asn1_integer_TLV_backwards ()
= serialize32_tagged_union_backwards
  (* lst *) (serialize32_asn1_tag_of_type_backwards INTEGER
             `serialize32_nondep_then_backwards`
             serialize32_asn1_length_of_type_backwards INTEGER)
  (* ltg *) (parser_tag_of_asn1_integer_impl)
  (* ls  *) (fun parser_tag -> (serialize32_synth_backwards
                              (* ls *) (weak_kind_of_type INTEGER
                                        `serialize32_weaken_backwards`
                                        serialize32_asn1_integer_backwards (snd parser_tag))
                              (* f2 *) (synth_asn1_integer_V parser_tag)
                              (* g1 *) (synth_asn1_integer_V_inverse parser_tag)
                              (* g1'*) (synth_asn1_integer_V_inverse_impl parser_tag)
                              (* prf*) ()))
