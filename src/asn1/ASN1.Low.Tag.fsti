module ASN1.Low.Tag
///
/// ASN.1 Low
///
include LowParse.Low.Base
include LowParse.Low.Combinators
include LowParse.Low.Int

include ASN1.Base
include ASN1.Spec.Tag

open Lib.IntTypes
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

val valid_asn1_tag
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

inline_for_extraction
val validate_asn1_tag
  (a: asn1_type)
: Tot (validator (parse_asn1_tag a))

(* ZT: Just return the specified `a: asn1_type`.
       Input should already be validated before read.
       precond `valid p h sl pos` *)
inline_for_extraction
val read_asn1_tag
  (a: asn1_type)
: Tot (leaf_reader (parse_asn1_tag a))

inline_for_extraction
val jump_asn1_tag
  (a: asn1_type)
: jumper (parse_asn1_tag a)

inline_for_extraction
val serialize32_asn1_tag
  (a: asn1_type)
: Tot (serializer32 (serialize_asn1_tag a))

inline_for_extraction
val write_asn1_tag
  (a: asn1_type)
: leaf_writer_strong (serialize_asn1_tag a)
