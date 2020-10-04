module X509.BasicFields.SerialNumber

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers
module B32 = FStar.Bytes

(*
 4.1.2.2.  Serial Number

   The serial number MUST be a positive integer assigned by the CA to
   each certificate.  It MUST be unique for each certificate issued by a
   given CA (i.e., the issuer name and serial number identify a unique
   certificate).  CAs MUST force the serialNumber to be a non-negative
   integer.

   Given the uniqueness requirements above, serial numbers can be
   expected to contain long integers.  Certificate users MUST be able to
   handle serialNumber values up to 20 octets.  Conforming CAs MUST NOT
   use serialNumber values longer than 20 octets.

   Note: Non-conforming CAs may issue certificates with serial numbers
   that are negative or zero.  Certificate users SHOULD be prepared to
   gracefully handle such certificates.
*)

(* NOTE: 1. `big_integer_as_octet_string_t` is the UN-ENCODED PLAIN integer represented as octets;
         2. the 20 octets restriction is on this plain serialNumber value. *)
let filter_x509_serialNumber
  (x: big_integer_as_octet_string_t)
: GTot bool
= let (|len, s32|) = x in
(* Conforming RFC 5280 -- serialNumber __value__ should not longer then 20 octets *)
  len <= 20ul &&
(* Non-Negative -- the first bit is zero *)
  B32.index s32 0 < 0x80uy &&
(* Non-Zero -- when length is 1, the only octet is not 0 *)
 (len > 1ul || B32.index s32 0 > 0x00uy)

let x509_serialNumber_t
= parse_filter_refine filter_x509_serialNumber

// let x509_serialNumber_dummy: x509_serialNumber_t
// = [@inline_let] let x: big_integer_as_octet_string_t = (|1ul, B32.create 1ul 1uy|) in
//   assert_norm (filter_x509_serialNumber x);
//   x

val parse_x509_serialNumber
: parser (parse_filter_kind parse_big_integer_as_octet_string_TLV_kind) x509_serialNumber_t

val serialize_x509_serialNumber
: serializer parse_x509_serialNumber

val lemma_serialize_x509_serialNumber_unfold
  (x: x509_serialNumber_t)
: Lemma (
  let tg = parser_tag_of_big_integer_as_octet_string x in
  serialize_x509_serialNumber `serialize` x ==
 (serialize_asn1_tag_of_type INTEGER `serialize` INTEGER)
  `Seq.append`
 (serialize_asn1_length_of_big_integer `serialize` (snd tg))
  `Seq.append`
 (serialize_big_integer_as_octet_string (v (snd tg)) `serialize` x)
)

noextract unfold [@@ "opaque_to_smt"]
let len_of_x509_serialNumber_max = 23ul

let lemma_serialize_x509_serialNumber_size
  (x: x509_serialNumber_t)
: Lemma (
  length_of_opaque_serialization serialize_x509_serialNumber x ==
  v (len_of_big_integer_as_octet_string_TLV x) /\
  length_of_opaque_serialization serialize_x509_serialNumber x
  <= v (len_of_x509_serialNumber_max)
)
= lemma_serialize_x509_serialNumber_unfold x;
  lemma_serialize_big_integer_as_octet_string_TLV_unfold x;
  lemma_serialize_big_integer_as_octet_string_TLV_size x

let len_of_x509_serialNumber
  (x: x509_serialNumber_t)
: Tot (len: asn1_value_int32_of_big_integer
            { v len == length_of_opaque_serialization serialize_x509_serialNumber x /\
              v len <= v len_of_x509_serialNumber_max })
= lemma_serialize_x509_serialNumber_size x;
  len_of_big_integer_as_octet_string_TLV x

val serialize32_x509_serialNumber_backwards
: serializer32_backwards serialize_x509_serialNumber
