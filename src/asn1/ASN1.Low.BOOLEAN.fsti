module ASN1.Low.BOOLEAN

include LowParse.Low.Base
include LowParse.Low.Combinators
include LowParse.Low.Int

include ASN1.Base
include ASN1.Spec.BOOLEAN

open Lib.IntTypes
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

(* Boolean *)
inline_for_extraction
val make_constant_size_reader
  (sz: nat)
  (sz' : U32.t { U32.v sz' == sz } )
  (#t: Type0)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
  (u: unit {
    make_constant_size_parser_precond sz t f
  })
  (f' : ((#rrel: _) -> (#rel: _) -> (s: B.mbuffer LowParse.Bytes.byte rrel rel) -> (pos: U32.t) -> HST.Stack (option t)
    (requires (fun h -> B.live h s /\ U32.v pos + sz <= B.length s))
    (ensures (fun h res h' ->
      B.modifies B.loc_none h h' /\
      res == f (Seq.slice (B.as_seq h s) (U32.v pos) (U32.v pos + sz))
  ))))
: Tot (leaf_reader (make_constant_size_parser sz t f))

inline_for_extraction
val read_asn1_boolean: unit -> Tot (leaf_reader (parse_asn1_boolean))

inline_for_extraction
val serialize32_asn1_boolean: unit -> Tot (serializer32 serialize_asn1_boolean)

inline_for_extraction
val write_asn1_boolean: unit -> leaf_writer_strong (serialize_asn1_boolean)

inline_for_extraction
val jump_asn1_boolean: unit -> jumper parse_asn1_boolean

val valid_asn1_boolean
  (h: HS.mem)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: pub_uint32)
: Lemma (
  valid parse_asn1_boolean h input pos
  <==>
 (valid parse_u8 h input pos /\
  Some? (decode_asn1_boolean (Seq.create 1 (contents parse_u8 h input pos)))))

inline_for_extraction
val validate_asn1_boolean: unit -> Tot (validator parse_asn1_boolean)
