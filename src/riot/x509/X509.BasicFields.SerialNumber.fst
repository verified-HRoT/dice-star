module X509.BasicFields.SerialNumber

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers
module B32 = FStar.Bytes

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

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
// let x509_serialNumber_dummy: x509_serialNumber_t
// = [@inline_let] let x: big_integer_as_octet_string_t = (|1ul, B32.create 1ul 1uy|) in
//   assert_norm (filter_x509_serialNumber x);
//   x

let serialize_x509_serialNumber
= serialize_big_integer_as_octet_string_TLV
  `serialize_filter`
  filter_x509_serialNumber

let lemma_serialize_x509_serialNumber_unfold x
= lemma_serialize_big_integer_as_octet_string_TLV_unfold x

let lemma_serialize_x509_serialNumber_size x
= lemma_serialize_big_integer_as_octet_string_TLV_size x

let serialize32_x509_serialNumber_backwards
= serialize32_big_integer_as_octet_string_TLV_backwards ()
  `serialize32_filter_backwards`
  filter_x509_serialNumber
