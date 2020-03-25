module ASN1.Low.Tag
///
/// ASN.1 Low
///
include LowParse.Low.Base
include LowParse.Low.Combinators
include LowParse.Low.Int
friend LowParse.Low.Int

include ASN1.Base
include ASN1.Spec.Tag
friend ASN1.Spec.Tag

open FStar.Integers
open Lib.IntTypes
module I = FStar.Integers
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

let valid_asn1_tag
  (a: asn1_type)
  (h: HS.mem)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: pub_uint32)
: Lemma (
  valid (parse_asn1_tag a) h input pos
  <==>
 (valid parse_u8 h input pos /\
  contents parse_u8 h input pos == asn1_tag_of_type a))
= valid_facts (parse_asn1_tag a) h input pos;
  valid_facts  parse_u8          h input pos;
  parse_asn1_tag_unfold a (bytes_of_slice_from h input pos)

inline_for_extraction
let validate_asn1_tag
  (a: asn1_type)
: Tot (validator (parse_asn1_tag a))
= fun #rrel #rel (input: slice rrel rel) (pos: pub_uint32) ->
  let h = HST.get () in
  let _ =
    valid_asn1_tag a     h input pos;
    valid_equiv parse_u8 h input pos
  in
  if (input.len - pos) < 1ul then
  ( validator_error_not_enough_data )
  else
  ( let tag  = asn1_tag_of_type a in
    let tag' = read_u8 input pos  in
    if tag = tag' then
    ( pos + 1ul )
    else
    ( validator_error_generic ))

(* ZT: Just return the specified `a: asn1_type`.
       Input should already be validated before read.
       precond `valid p h sl pos` *)
inline_for_extraction
let read_asn1_tag
  (a: asn1_type)
: Tot (leaf_reader (parse_asn1_tag a))
= fun #rrel #rel input pos ->
    a

inline_for_extraction
let jump_asn1_tag
  (a: asn1_type)
: jumper (parse_asn1_tag a)
= jump_constant_size (parse_asn1_tag a) 1ul ()

inline_for_extraction
let serialize32_asn1_tag
  (a: asn1_type)
: Tot (serializer32 (serialize_asn1_tag a))
= fun (x: the_asn1_type a) #rrel #rel b pos ->
  let content = asn1_tag_of_type x in
  mbuffer_upd b (Ghost.hide (v pos)) (Ghost.hide (v pos + 1)) pos content;
  1ul

inline_for_extraction
let write_asn1_tag
  (a: asn1_type)
: leaf_writer_strong (serialize_asn1_tag a)
= leaf_writer_strong_of_serializer32 (serialize32_asn1_tag a) ()
