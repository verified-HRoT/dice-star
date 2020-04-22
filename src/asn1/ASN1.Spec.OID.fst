module ASN1.Spec.OID

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.SeqBytes.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers
(*)
(* FIXME: Use real OIDs *)
let riot_oid              : datatype_of_asn1_type OCTET_STRING = (|5ul, Seq.create 5 0x00uy|)
let ecdsa_with_sha256_oid : datatype_of_asn1_type OCTET_STRING = (|5ul, Seq.create 5 0x00uy|)
let key_usage_oid         : datatype_of_asn1_type OCTET_STRING = (|5ul, Seq.create 5 0x00uy|)

let filter_asn1_oid
  (l: asn1_length_of_type OID)
  (ls: lbytes l)
: GTot (bool)
= ls = dsnd riot_oid ||
  ls = dsnd ecdsa_with_sha256_oid ||
  ls = dsnd key_usage_oid

let synth_asn1_oid
  (l: asn1_length_of_type OID)
  (ls: parse_filter_refine (filter_asn1_oid l))
: GTot (datatype_of_asn1_type OID)
= match ls with
  | riot_oid              -> RIOT_OID
  | ecdsa_with_sha256_oid -> ECDSA_WITH_SHA256_OID
  | key_usage_oid         -> KEY_USAGE_OID

let synth_asn1_oid_inverse
  (l: asn1_length_of_type OID)
  (oid: datatype_of_asn1_type OID)
: GTot (ls: parse_filter_refine (filter_asn1_oid l) {oid == synth_asn1_oid l ls})
= match oid with
  | RIOT_OID              -> riot_oid
  | ECDSA_WITH_SHA256_OID -> ecdsa_with_sha256_oid
  | KEY_USAGE_OID         -> key_usage_oid

