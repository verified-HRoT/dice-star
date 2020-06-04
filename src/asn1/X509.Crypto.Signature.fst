module X509.Crypto.Signature

open LowParse.Low.Base
// open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers
module B32 = FStar.Bytes
(*)
noeq
type x509_signature_ECDSA_P256_t = {
  r: 
  s:
  }
