module ASN1.Spec.Bytes32

open LowParse.Spec.Base
open LowParse.Spec.Bytes
open ASN1.Base

open FStar.Integers
module B32 = FStar.Bytes

let parse_flbytes32_gen
  (len: asn1_int32 )
  (s: bytes { Seq.length s == v len } )
: GTot (B32.lbytes32 len)
= lt_pow2_32 (v len);
  B32.hide s

let parse_flbytes32
  (len: asn1_int32 )
: Tot (parser (total_constant_size_parser_kind (v len)) (B32.lbytes32 len))
= make_total_constant_size_parser (v len) (B32.lbytes32 len) (parse_flbytes32_gen len)

let serialize_flbytes32'
  (len: asn1_int32)
: Tot (bare_serializer (B32.lbytes32 len))
= fun (x: B32.lbytes32 len) -> (
    lt_pow2_32 (v len);
    B32.reveal x
  )

#push-options "--z3rlimit 16"
let serialize_flbytes32_correct
  (len: asn1_int32)
: Lemma
  (serializer_correct (parse_flbytes (v len)) (serialize_flbytes32' len))
= let prf
    (input: B32.lbytes32 len)
  : Lemma
    (
      let ser = serialize_flbytes32' len input in
      Seq.length ser == v len /\
      parse (parse_flbytes32 len) ser == Some (input, (v len))
    )
  = ()
  in
  Classical.forall_intro prf

let serialize_flbytes32
  (len: asn1_int32)
: Tot (serializer (parse_flbytes32 len))
= serialize_flbytes32_correct len;
  serialize_flbytes32' len

let lemma_serialize_flbytes32_unfold
  (len: asn1_int32)
  (s32: B32.lbytes32 len)
: Lemma (
  serialize_flbytes32 len `serialize` s32 ==
  B32.reveal s32
)
= ()

let lemma_serialize_flbytes32_size
  (len: asn1_int32)
  (s32: B32.lbytes32 len)
: Lemma (
  Seq.length (serialize_flbytes32 len `serialize` s32) ==
  v len
)
= ()
