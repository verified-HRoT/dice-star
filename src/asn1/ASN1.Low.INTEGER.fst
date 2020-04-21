module ASN1.Low.INTEGER

open ASN1.Base
open ASN1.Spec.INTEGER
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

let len_of_asn1_integer
  (value: datatype_of_asn1_type INTEGER)
: Tot (len: asn1_int32_of_type INTEGER { v len == length_of_asn1_integer value } )
= if      0l         <= value && value <= 0x7Fl      then
  ( 1ul )
  else if 0x7Fl       < value && value <= 0xFFl       then
  ( 2ul )
  else if 0xFFl       < value && value <= 0x7FFFl     then
  ( 2ul )
  else if 0x7FFFl     < value && value <= 0xFFFFl     then
  ( 3ul )
  else if 0xFFFFl     < value && value <= 0x7FFFFFl   then
  ( 3ul )
  else if 0x7FFFFFl   < value && value <= 0xFFFFFFl   then
  ( 4ul )
  else if 0xFFFFFFl   < value && value <= 0x7FFFFFFFl then
  ( 4ul )

(*
NOTE: Since there are no low-level machine-integer to bytes implementations
      available, the (big-endian) serialization of integers are tricky. For
      1-byte, 2-byte and 4-byte integers, we could use `LowStar.Endianness`
      16-bit, 32-bit integer store interfaces. For 3-byte, we may need some
      magic.
*)

open LowParse.Low.BoundedInt

#restart-solver
#push-options "--query_stats --z3rlimit 32"
let serialize32_asn1_integer
  (len: asn1_int32_of_type INTEGER)
: Tot (serializer32 (serialize_asn1_integer (v len)))
= fun (value: datatype_of_asn1_type INTEGER { v len == length_of_asn1_integer value })
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->(* 1-byte integer with the most-significant bit `0` *)
  if      (0l         <= value && value <= 0x7Fl      ) then
  ( admit (); (* Prf *) serialize_asn1_integer_unfold (length_of_asn1_integer value) value
  ; let b0: byte = cast #(Signed W32) #(Unsigned W8) value in
    (* Prf *) E.reveal_be_to_n (Seq.create 1 b0)
  ; (* Prf *) E.reveal_be_to_n (Seq.slice (Seq.create 1 b0) 1 1)
  ; mbuffer_upd
    (* dst *) (b)
    (*range*) (v pos) (v pos + 1)
    (* pos *) (pos)
    (* val *) (b0)
  ; (*return*) 1ul )

  (* 1-byte integer with the most-significant bit `1` *)
  else if (0x7Fl       < value && value <= 0xFFl      ) then
  ( admit ()
  ; (* Prf *) serialize_asn1_integer_unfold (length_of_asn1_integer value) value;
    (* Prf *) let h0 = HST.get () in
    (* Prf *) writable_weaken
              (* buf *) (b)
              (*range*) (v pos) (v pos + 2)
              (* mem *) (h0)
              (* from*) (v pos)
              (* to  *) (v pos + 1);
    (* NOTE: Serializing the leading zero. *)
    mbuffer_upd
      (* dst *) (b)
      (*range*) (v pos) (v pos + 1)
      (* pos *) (pos)
      (* val *) (0x00uy);
    (* Prf *) let h1 = HST.get () in
    (* Prf *) writable_modifies
              (* buf *) (b)
              (*range*) (v pos) (v pos + 2)
              (* mem *) (h0)
              (* loc *) (B.loc_none)
              (* mem *) (h1);
    (* Prf *) writable_weaken
              (* buf *) (b)
              (*range*) (v pos) (v pos + 2)
              (* mem *) (h1)
              (* from*) (v pos + 1)
              (* to  *) (v pos + 2);
    (* NOTE: Serializing the 1-byte integer. *)
    let b0: byte = cast #(Signed W32) #(Unsigned W8) value in
    (* Prf *) E.reveal_be_to_n (Seq.create 1 b0);
    (* Prf *) E.reveal_be_to_n (Seq.slice (Seq.create 1 b0) 1 1);
    mbuffer_upd
      (* dst *) (b)
      (*range*) (v pos) (v pos + 2)
      (* pos *) (pos + 1ul)
      (* val *) (b0);
    (* Prf *) let h2 = HST.get () in
    (* Prf *) Seq.lemma_split
              (*slice*) (Seq.slice (B.as_seq h2 b) (v pos) (v pos + 2))
              (* at  *) (1);
    (* Prf *) B.modifies_buffer_from_to_elim
              (* buf *) (b)
              (*frame*) (pos) (pos + 1ul)
              (* new *) (B.loc_buffer_from_to b (pos + 1ul) (pos + 2ul))
              (* mem *) (h1) (h2);
  (*return*) 2ul )

  (* 2-byte integer with the most-significant bit `0` *)
  else if (0xFFl       < value && value <= 0x7FFFl    ) then
  ( (* Prf *) serialize_asn1_integer_unfold (length_of_asn1_integer value) value;
    (* Prf *) let h0 = HST.get () in
    (* Prf *) LE.writable_store_pre
              (* buf *) b
              (* from*) (v pos)
              (* len *) 2
              (*  p  *) (fun s -> E.be_to_n s == v #(Signed W32) value)
              (* mem *) h0;
    (* Prf *) let h1 = HST.get () in
    LE.store16_be_i
      (* buf *) b
      (* pos *) pos
      (* val *) (cast #(Signed W32) #(Unsigned W16) value);
    (* Prf *) LE.store_post_modifies
              (* buf *) b
              (* from*) (v pos)
              (* len *) 2
              (*  p  *) (fun s -> E.be_to_n s == v #(Signed W32) value);
  (*return*) 2ul )

  (* 2-byte integer with the most-significant bit `1` *)
  else if (0x7FFFl       < value && value <= 0xFFFFl    ) then
  ( (* Prf *) serialize_asn1_integer_unfold (length_of_asn1_integer value) value;
    (* Prf *) serialize_bounded_integer_spec 2 (cast #(Signed W32) #(Unsigned W32) value);
    let h0 = HST.get () in
    writable_weaken b (v pos) (v pos + 3) h0 (v pos) (v pos + 1);
    mbuffer_upd b (v pos) (v pos + 3) pos 0x00uy;
    let h1 = HST.get () in
    writable_modifies b (v pos) (v pos + 3) h0 B.loc_none h1;
    writable_weaken b (v pos) (v pos + 3) h1 (v pos + 1) (v pos + 3);
    let offset = serialize32_bounded_integer_2 () (cast #(Signed W32) #(Unsigned W32) value) b pos in
    let h2 = HST.get () in
    B.modifies_buffer_from_to_elim b pos (pos + 1ul) (B.loc_buffer_from_to b (pos + 1ul) (pos + 3ul)) h1 h2;
  (*return*) 1ul + offset )
  else admit ()


(*)
  (* NOTE: 3-byte integer with the most-significant bit `0` *)
  else if (0xFFFFl      < value && value <= 0x7FFFFFl  ) then
  ( (* Prf *) serialize_asn1_integer_unfold (length_of_asn1_integer value) value;
    (* Prf *) assert_norm (v #(Signed W32) value < pow2 (8 * 3 - 1) /\
                           v #(Signed W32) value < pow2 (8 * 3));
    (* Prf *) E.reveal_n_to_be 3 (v #(Signed W32) value);
    (* NOTE: Serialize the first and second bytes of this 3-byte integer. *)
    let v01: uint_16 = cast #(Signed W32) #(Unsigned W16) (value / 0x100l) in
    (* Prf *) let h0 = HST.get () in
    (* Prf *) writable_weaken
              (* buf *) (b)
              (*range*) (v pos) (v pos + 3)
              (* mem *) (h0)
              (* from*) (v pos)
              (* to  *) (v pos + 2);
    (* Prf *) LE.writable_store_pre
              (* dst *) (b)
              (* from*) (v pos)
              (* len *) (2)
              (*predi*) (fun s -> E.be_to_n s == v v01)
              (* mem *) (h0);
    LE.store16_be_i
    (* dst *) (b)
    (* pos *) (pos)
    (* val *) (v01);
    (* Prf *) let h1 = HST.get () in
    (* Prf *) LE.store_post_modifies
              (* dst *) (b)
              (* from*) (v pos)
              (* len *) (2)
              (*predi*) (fun s -> E.be_to_n s == v v01)
              (* mem *) (h0)
              (* mem'*) (h1);
    (* NOTE: Serialize the third byte of this 3-byte integer. *)
    let b2: byte = cast #(Signed W32) #(Unsigned W8) (value % 0x100l) in
    (* Prf *) let h2 = HST.get () in
    (* Prf *) E.reveal_be_to_n (Seq.create 1 b2);
    (* Prf *) E.reveal_be_to_n (Seq.slice (Seq.create 1 b2) 1 1);
    (* Prf *) writable_modifies
              (* buf *) (b)
              (*range*) (v pos) (v pos + 3)
              (* mem *) (h0)
              (* loc *) (B.loc_none)
              (* mem'*) (h1);
    (* Prf *) writable_weaken
              (* buf *) (b)
              (*range*) (v pos) (v pos + 3)
              (* mem *) (h1)
              (* from*) (v pos + 2)
              (* to  *) (v pos + 3);
    mbuffer_upd
    (* dst *) (b)
    (*range*) (v pos) (v pos + 3)
    (* pos *) (pos + 2ul)
    (* val *) (b2);
    (* Prf *) Seq.lemma_split
              (*slice*) (Seq.slice (B.as_seq h2 b) (v pos) (v pos + 3))
              (* at  *) (2);
    (* Prf *) B.modifies_buffer_from_to_elim
              (* buf *) (b)
              (*frame*) (pos) (pos + 2ul)
              (* new *) (B.loc_buffer_from_to b (pos + 2ul) (pos + 3ul))
              (* mem *) (h1) (h2);
  (*return*) 3ul )

  else (admit ())

(*)
  (* 2-byte integer with the mort-significant bit `0` *)
  else if (0xFFl       < value && value <= 0x7FFFl    ) then
  ( admit ();
    (* Prf *) serialize_asn1_integer_unfold (length_of_asn1_integer value) value
  ; (* Prf *) serialize_bounded_integer_spec 2 (cast #(Signed W32) #(Unsigned W32) value)
  ; let offset = serialize32_bounded_integer_2 ()
    (* val *) (cast #(Signed W32) #(Unsigned W32) value)
    (* dst *) (b)
    (* pos *) (pos) in
  (*return*) offset )
  else
  ( admit () )
#pop-options


  // if      (0l         <= value && value <= 0x7Fl      ) then
  // ( (* Prf *) serialize_asn1_integer_unfold (length_of_asn1_integer value) value
  // ; let b0: byte = cast #(Signed W32) #(Unsigned W8) value in
  //   (* Prf *) E.reveal_be_to_n (Seq.create 1 b0)
  // ; (* Prf *) E.reveal_be_to_n (Seq.slice (Seq.create 1 b0) 1 1)
  // ; mbuffer_upd
  //   (* dst *) (b)
  //   (*range*) (v pos) (v pos + 1)
  //   (* pos *) (pos)
  //   (* val *) (b0)
  // ; (*return*) 1ul )

  // (* 3-byte integer with the most-significant bit `1` *)
  // else if (0x7FFFFFl     < value && value <= 0xFFFFFFl    ) then
  // ( (* Prf *) serialize_asn1_integer_unfold (length_of_asn1_integer value) value
  // ; let b0: byte = cast #(Signed W32) #(Unsigned W8) (value / 0x10000l) in
  //   let v12: uint_16 = cast #(Signed W32) #(Unsigned W16) (value % 0x10000l) in
  //   (* Prf *) E.reveal_be_to_n (Seq.create 1 b0)
  // ; (* Prf *) E.reveal_be_to_n (Seq.slice (Seq.create 1 b0) 1 1)
  // ; mbuffer_upd
  //   (* dst *) (b)
  //   (*range*) (v pos) (v pos + 1)
  //   (* pos *) (pos)
  //   (* val *) (b0)
  // ; LE.store16_be_i
  //   (* dst *) (b)
  //   (* pos *) (pos + 1ul)
  //   (* val *) (v12)
  // ; (*return*) 3ul)
