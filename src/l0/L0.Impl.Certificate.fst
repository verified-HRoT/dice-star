module L0.Impl.Certificate

open ASN1.Spec

open RIoT.Base
open RIoT.Declassify
open RIoT.X509

module B32 = FStar.Bytes
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

open X509

open Lib.IntTypes
module Ed25519 = Hacl.Ed25519

open LowStar.Comment
open LowStar.Printf

open RIoT.Spec.Certificate

#set-options "--fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

(* Create AliasKey To-Be-Signed Certificate
  =======================================
  RFC 5280:
     TBSCertificate  ::=  SEQUENCE  {
        version         [0]  EXPLICIT Version DEFAULT v1,
        serialNumber         CertificateSerialNumber,
        signature            AlgorithmIdentifier,
        issuer               Name,
        validity             Validity,
        subject              Name,
        subjectPublicKeyInfo SubjectPublicKeyInfo,
        issuerUniqueID  [1]  IMPLICIT UniqueIdentifier OPTIONAL,
                             -- If present, version MUST be v2 or v3
        subjectUniqueID [2]  IMPLICIT UniqueIdentifier OPTIONAL,
                             -- If present, version MUST be v2 or v3
        extensions      [3]  EXPLICIT Extensions OPTIONAL
                             -- If present, version MUST be v3
        }

   In our case:
      TBSCertificate  ::=  SEQUENCE  {
        ----------------
        |              |
        |   Template   |
        |              |
        ----------------
        subjectPublicKeyInfo for AliasKey,
        extensions           for RIoT
        }
   NOTE: The SEQUENCE Tag and Length of TBS is __NOT__ part of the template
   NOTE: Other extensions like Key Usage are __NOT__ included in this version.
*)

#push-options "--z3rlimit 16"
unfold
let create_aliasKeyTBS_pre
  (h: HS.mem)
  (crt_version: x509_version_t)
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (notBefore: datatype_of_asn1_type UTC_TIME)
  (notAfter : datatype_of_asn1_type Generalized_Time)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (fwid: B.lbuffer byte_pub 32)
  (ku: key_usage_payload_t)
  (keyID: B.lbuffer byte_pub 20)
  (riot_version: datatype_of_asn1_type INTEGER)
  (deviceID_pub: B.lbuffer byte_pub 32)
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKeyTBS_len: UInt32.t)
  (aliasKeyTBS_buf: B.lbuffer byte_pub (UInt32.v aliasKeyTBS_len)) : Type0
= // let keyID_string = sha1_digest_to_octet_string_spec (B.as_seq h keyID) in
  B.(all_live h [buf fwid;
                 buf deviceID_pub;
                 buf aliasKey_pub;
                 buf keyID;
                 buf aliasKeyTBS_buf]) /\
  B.(all_disjoint [loc_buffer fwid;
                   loc_buffer deviceID_pub;
                   loc_buffer aliasKey_pub;
                   loc_buffer keyID;
                   loc_buffer aliasKeyTBS_buf]) /\
  eq2 #nat (UInt32.v aliasKeyTBS_len) (v (len_of_aliasKeyTBS
                         serialNumber
                         i_common i_org i_country
                         s_common s_org s_country
                         riot_version))
#pop-options

unfold
let create_aliasKeyTBS_post
  (h0: HS.mem)
  (r: unit)
  (h1: HS.mem)
  (crt_version: x509_version_t)
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (notBefore: datatype_of_asn1_type UTC_TIME)
  (notAfter : datatype_of_asn1_type Generalized_Time)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (fwid: B.lbuffer byte_pub 32)
  (ku: key_usage_payload_t)
  (keyID: B.lbuffer byte_pub 20)
  (riot_version: datatype_of_asn1_type INTEGER)
  (deviceID_pub: B.lbuffer byte_pub 32)
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKeyTBS_len: UInt32.t)
  (aliasKeyTBS_buf: B.lbuffer byte_pub (UInt32.v aliasKeyTBS_len)
                    { create_aliasKeyTBS_pre
                     (h0)
                     (crt_version)
                     (serialNumber)
                     (i_common) (i_org) (i_country)
                     (notBefore) (notAfter)
                     (s_common) (s_org) (s_country)
                     (fwid)
                     (ku)
                     (keyID)
                     (riot_version)
                     (deviceID_pub)
                     (aliasKey_pub)
                     (aliasKeyTBS_len) (aliasKeyTBS_buf) })
: Type0
= let aliasKeyTBS = create_aliasKeyTBS_spec
                                     (crt_version)
                                     (serialNumber)
                                     (i_common) (i_org) (i_country)
                                     (notBefore) (notAfter)
                                     (s_common) (s_org) (s_country)
                                     (ku)
                                     (B.as_seq h0 keyID)
                                     (riot_version)
                                     (B.as_seq h0 fwid)
                                     (B.as_seq h0 deviceID_pub)
                                     (B.as_seq h0 aliasKey_pub) in
  (* Prf *) lemma_serialize_aliasKeyTBS_size_exact aliasKeyTBS;
  B.(modifies (loc_buffer aliasKeyTBS_buf) h0 h1) /\
  B.as_seq h1 aliasKeyTBS_buf == serialize_aliasKeyTBS `serialize` aliasKeyTBS

#set-options "--__temp_no_proj RIoT.Impl.Certificate"
noeq
type aliasKeyTBS_bytes = {
  fwid_pub32     : B32.lbytes32 32ul;
  keyID_pub32    : B32.lbytes32 20ul;
  deviceID_pub32 : B32.lbytes32 32ul;
  aliasKey_pub32 : B32.lbytes32 32ul
}


#push-options "--z3rlimit 64"
[@@ "opaque_to_smt"]
inline_for_extraction noextract
let create_aliasKeyTBS_buffers_to_bytes
  (fwid: B.lbuffer byte_pub 32)
  (keyID: B.lbuffer byte_pub 20)
  (deviceID_pub: B.lbuffer byte_pub 32)
  (aliasKey_pub: B.lbuffer byte_pub 32)
  : HST.Stack aliasKeyTBS_bytes
      (requires fun h ->
        B.(all_live h [buf fwid;
                       buf deviceID_pub;
                       buf aliasKey_pub;
                       buf keyID]) /\
        B.(all_disjoint [loc_buffer fwid;
                         loc_buffer deviceID_pub;
                         loc_buffer aliasKey_pub;
                         loc_buffer keyID]))
      (ensures fun h0 r h1 ->
        B.(modifies loc_none h0 h1) /\
        (B32.hide (B.as_seq h0 fwid) == r.fwid_pub32 /\
         B32.hide (B.as_seq h0 deviceID_pub) == r.deviceID_pub32 /\
         B32.hide (B.as_seq h0 aliasKey_pub) == r.aliasKey_pub32 /\
         B32.hide (B.as_seq h0 keyID) == r.keyID_pub32))
  = HST.push_frame ();
    let fwid_pub32    : B32.lbytes32 32ul = B32.of_buffer 32ul fwid in
    let deviceID_pub32: B32.lbytes32 32ul = B32.of_buffer 32ul deviceID_pub in
    let aliasKey_pub32: B32.lbytes32 32ul = B32.of_buffer 32ul aliasKey_pub in
    let keyID_pub32 = B32.of_buffer 20ul keyID in
    HST.pop_frame ();
    { fwid_pub32 = fwid_pub32;
      keyID_pub32 = keyID_pub32;
      deviceID_pub32 = deviceID_pub32;
      aliasKey_pub32 = aliasKey_pub32 }

[@@ "opaque_to_smt"]
let create_aliasKeyTBS
  (crt_version: x509_version_t)
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (notBefore: datatype_of_asn1_type UTC_TIME)
  (notAfter : datatype_of_asn1_type Generalized_Time)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (fwid: B.lbuffer byte_pub 32)
  (ku: key_usage_payload_t)
  (keyID: B.lbuffer byte_pub 20)
  (riot_version: datatype_of_asn1_type INTEGER)
  (deviceID_pub: B.lbuffer byte_pub 32)
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKeyTBS_len: UInt32.t)
  (aliasKeyTBS_buf: B.lbuffer byte_pub (UInt32.v aliasKeyTBS_len))
: HST.Stack unit
  (requires fun h -> create_aliasKeyTBS_pre
                     (h)
                     (crt_version)
                     (serialNumber)
                     (i_common) (i_org) (i_country)
                     (notBefore) (notAfter)
                     (s_common) (s_org) (s_country)
                     (fwid)
                     (ku)
                     (keyID)
                     (riot_version)
                     (deviceID_pub)
                     (aliasKey_pub)
                     (aliasKeyTBS_len) (aliasKeyTBS_buf))
  (ensures fun h0 _ h1 -> create_aliasKeyTBS_post
                         (h0) () (h1)
                         (crt_version)
                         (serialNumber)
                         (i_common) (i_org) (i_country)
                         (notBefore) (notAfter)
                         (s_common) (s_org) (s_country)
                         (fwid)
                         (ku)
                         (keyID)
                         (riot_version)
                         (deviceID_pub)
                         (aliasKey_pub)
                         (aliasKeyTBS_len) (aliasKeyTBS_buf))
= let h0 = FStar.HyperStack.ST.get () in

  let b = create_aliasKeyTBS_buffers_to_bytes fwid keyID deviceID_pub aliasKey_pub in

  let keyID_string: datatype_of_asn1_type OCTET_STRING =
    { ASN1.Base.len = 20ul; ASN1.Base.s = b.keyID_pub32 } in

  printf "Creating AliasKey Certificate TBS Message\n" done;
  let aliasKeyTBS = x509_get_AliasKeyTBS
                                     crt_version
                                     serialNumber
                                     i_common i_org i_country
                                     notBefore notAfter
                                     s_common s_org s_country
                                     ku
                                     keyID_string
                                     riot_version
                                     b.fwid_pub32
                                     b.deviceID_pub32
                                     b.aliasKey_pub32 in
  (* Prf *) lemma_serialize_aliasKeyTBS_size_exact aliasKeyTBS;

  (*
   * Postcondition 2
   *)
  assert (eq2 #aliasKeyTBS_t aliasKeyTBS (create_aliasKeyTBS_spec
                                     (crt_version)
                                     (serialNumber)
                                     (i_common) (i_org) (i_country)
                                     (notBefore) (notAfter)
                                     (s_common) (s_org) (s_country)
                                     (ku)
                                     (B.as_seq h0 keyID)
                                     (riot_version)
                                     (B.as_seq h0 fwid)
                                     (B.as_seq h0 deviceID_pub)
                                     (B.as_seq h0 aliasKey_pub)));

  printf "Serializing AliasKey Certificate TBS\n" done;
  let _offset = serialize32_aliasKeyTBS_backwards
                 aliasKeyTBS
                 aliasKeyTBS_buf
                 aliasKeyTBS_len in ()
#pop-options

(* Sign and Finalize AliasKey Certificate
  =======================================
  RFC 5280:
   Certificate  ::=  SEQUENCE  {
        tbsCertificate       TBSCertificate,
        signatureAlgorithm   AlgorithmIdentifier,
        signatureValue       BIT STRING  }
*)

(* A predicate says that
   1) the length of TBS is valid as Hacl's HKDF message length
   2) the length of created CRT is valid as our ASN.1 TLV SEQUENCE value length
*)

#push-options "--z3rlimit 256"
[@@ "opaque_to_smt"]
let sign_and_finalize_aliasKeyCRT
  (deviceID_priv: B.lbuffer byte_sec 32)
  (aliasKeyTBS_len: size_t)
  (aliasKeyTBS_buf: B.lbuffer byte_pub (v aliasKeyTBS_len))
  (aliasKeyCRT_len: size_t)
  (aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len))
: HST.Stack unit
  (requires fun h ->
    B.(all_live h [buf deviceID_priv;
                   buf aliasKeyTBS_buf;
                   buf aliasKeyCRT_buf]) /\
    B.(all_disjoint [loc_buffer deviceID_priv;
                     loc_buffer aliasKeyTBS_buf;
                     loc_buffer aliasKeyCRT_buf]) /\
    (* For `B.alloca` *)
    0 < v aliasKeyTBS_len /\
    valid_aliasKeyCRT_ingredients aliasKeyTBS_len /\
    (* `aliasKeyCRT_buf` has exact space to write serialization *)
    v aliasKeyCRT_len == length_of_aliasKeyCRT aliasKeyTBS_len
   )
  (ensures fun h0 _ h1 ->
    let aliasKeyCRT: aliasKeyCRT_t aliasKeyTBS_len = sign_and_finalize_aliasKeyCRT_spec
                                                                      (B.as_seq h0 deviceID_priv)
                                                                      (aliasKeyTBS_len)
                                                                      (B.as_seq h0 aliasKeyTBS_buf) in
    (* Prf *) lemma_serialize_aliasKeyCRT_size_exact aliasKeyTBS_len aliasKeyCRT;
    B.(modifies (loc_buffer aliasKeyCRT_buf) h0 h1) /\
    B.as_seq h1 aliasKeyCRT_buf == serialize_aliasKeyCRT aliasKeyTBS_len `serialize` aliasKeyCRT
  )
= HST.push_frame ();

(* Classify AliasKeyTBS *)
  let aliasKeyTBS_buf_sec: B.lbuffer byte_sec (v aliasKeyTBS_len) = B.alloca (u8 0x00) aliasKeyTBS_len in
  classify_public_buffer
    (* len *) aliasKeyTBS_len
    (* src *) aliasKeyTBS_buf
    (* dst *) aliasKeyTBS_buf_sec;

(* Sign Classified AliasKeyTBS *)
  let aliasKeyTBS_sig_sec: B.lbuffer byte_sec 64 = B.alloca (u8 0x00) 64ul in
  Ed25519.sign
    (* sig *) aliasKeyTBS_sig_sec
    (* key *) deviceID_priv
    (* len *) aliasKeyTBS_len
    (* msg *) aliasKeyTBS_buf_sec;

(* Declassify AliasKeyTBS Signature *)
  let aliasKeyTBS_sig: B.lbuffer byte_pub 64 = B.alloca 0x00uy 64ul in
  declassify_secret_buffer
    (* len *) 64ul
    (* src *) aliasKeyTBS_sig_sec
    (* dst *) aliasKeyTBS_sig;

(* Finalize AliasKeyCRT with AliasKeyTBS and Signature *)
  let aliasKeyTBS_buf32: B32.lbytes32 aliasKeyTBS_len = B32.of_buffer aliasKeyTBS_len aliasKeyTBS_buf in
  let aliasKeyTBS_sig32: x509_signature_raw_t = B32.of_buffer 64ul aliasKeyTBS_sig in

  printf "Creating AliasKey Certificate CRT message\n" done;
  let aliasKeyCRT: aliasKeyCRT_t aliasKeyTBS_len = x509_get_AliasKeyCRT
                                                             aliasKeyTBS_len
                                                             aliasKeyTBS_buf32
                                                             aliasKeyTBS_sig32 in
  (* Prf *) lemma_serialize_aliasKeyCRT_size_exact aliasKeyTBS_len aliasKeyCRT;
  HST.pop_frame ();

  printf "Serializing AliasKey Certificate CRT\n" done;
(* Serialize AliasKeyCRT *)
  let _offset = serialize32_aliasKeyCRT_backwards
                 aliasKeyTBS_len
                 aliasKeyCRT
                 aliasKeyCRT_buf
                 aliasKeyCRT_len in ()
#pop-options

(*                 CSR
 *=====================================
 *)

#push-options "--z3rlimit 512"
[@@ "opaque_to_smt"]
let create_deviceIDCRI
  (csr_version: datatype_of_asn1_type INTEGER)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (deviceID_pub: B.lbuffer byte_pub 32)
  (deviceIDCRI_len: size_t)
  (deviceIDCRI_buf: B.lbuffer byte_pub (v deviceIDCRI_len))
: HST.Stack unit
  (requires fun h ->
    B.(all_live h [buf deviceID_pub;
                   buf deviceIDCRI_buf]) /\
    B.(all_disjoint [loc_buffer deviceID_pub;
                     loc_buffer deviceIDCRI_buf]) /\
    v deviceIDCRI_len == v (len_of_deviceIDCRI csr_version s_common s_org s_country)
   )
  (ensures fun h0 _ h1 ->
    let deviceIDCRI: deviceIDCRI_t = create_deviceIDCRI_spec
                                                                      (csr_version)
                                                                      (s_common)
                                                                      (s_org)
                                                                      (s_country)
                                                                      (ku)
                                                                      (B.as_seq h0 deviceID_pub) in
    (* Prf *) lemma_serialize_deviceIDCRI_size_exact deviceIDCRI;
    B.(modifies (loc_buffer deviceIDCRI_buf) h0 h1) /\
    B.as_seq h1 deviceIDCRI_buf == serialize_deviceIDCRI `serialize` deviceIDCRI
  )
=
  HST.push_frame ();

(* Create deviceIDCRI *)
  let deviceID_pub32: B32.lbytes32 32ul = B32.of_buffer 32ul deviceID_pub in

  printf "Creating AliasKey Certificate TBS Message\n" done;
  let deviceIDCRI: deviceIDCRI_t = x509_get_deviceIDCRI
                                                                    csr_version
                                                                    s_common
                                                                    s_org
                                                                    s_country
                                                                    ku
                                                                    deviceID_pub32 in

  (* Prf *) lemma_serialize_deviceIDCRI_size_exact deviceIDCRI;

  printf "Serializing AliasKey Certificate TBS\n" done;
(* Serialize deviceIDCRI *)
  let offset = serialize32_deviceIDCRI_backwards
                 deviceIDCRI
                 deviceIDCRI_buf
                 deviceIDCRI_len in

  HST.pop_frame ()
#pop-options

#push-options "--z3rlimit 256"
[@@ "opaque_to_smt"]
let sign_and_finalize_deviceIDCSR
  (deviceID_priv: B.lbuffer byte_sec 32)
  (deviceIDCRI_len: size_t)
  (deviceIDCRI_buf: B.lbuffer byte_pub (v deviceIDCRI_len))
  (deviceIDCSR_len: size_t)
  (deviceIDCSR_buf: B.lbuffer byte_pub (v deviceIDCSR_len))
: HST.Stack unit
  (requires fun h ->
    B.(all_live h [buf deviceID_priv;
                   buf deviceIDCRI_buf;
                   buf deviceIDCSR_buf]) /\
    B.(all_disjoint [loc_buffer deviceID_priv;
                     loc_buffer deviceIDCRI_buf;
                     loc_buffer deviceIDCSR_buf]) /\
    (* For `B.alloca` *)
    0 < v deviceIDCRI_len /\
    valid_deviceIDCSR_ingredients deviceIDCRI_len /\
    (* `deviceIDCSR_buf` has exact space to write serialization *)
    v deviceIDCSR_len == length_of_deviceIDCSR deviceIDCRI_len
   )
  (ensures fun h0 _ h1 ->
    let deviceIDCSR: deviceIDCSR_t deviceIDCRI_len = sign_and_finalize_deviceIDCSR_spec
                                                                      (B.as_seq h0 deviceID_priv)
                                                                      (deviceIDCRI_len)
                                                                      (B.as_seq h0 deviceIDCRI_buf) in
    (* Prf *) lemma_serialize_deviceIDCSR_size_exact deviceIDCRI_len deviceIDCSR;
    B.(modifies (loc_buffer deviceIDCSR_buf) h0 h1) /\
    B.as_seq h1 deviceIDCSR_buf == serialize_deviceIDCSR deviceIDCRI_len `serialize` deviceIDCSR
  )
=
  HST.push_frame ();

(* Classify AliasKeyTBS *)
  let deviceIDCRI_buf_sec: B.lbuffer byte_sec (v deviceIDCRI_len) = B.alloca (u8 0x00) deviceIDCRI_len in
  classify_public_buffer
    (* len *) deviceIDCRI_len
    (* src *) deviceIDCRI_buf
    (* dst *) deviceIDCRI_buf_sec;

(* Sign Classified AliasKeyTBS *)
  let deviceIDCRI_sig_sec: B.lbuffer byte_sec 64 = B.alloca (u8 0x00) 64ul in
  Ed25519.sign
    (* sig *) deviceIDCRI_sig_sec
    (* key *) deviceID_priv
    (* len *) deviceIDCRI_len
    (* msg *) deviceIDCRI_buf_sec;

(* Declassify AliasKeyTBS Signature *)
  let deviceIDCRI_sig: B.lbuffer byte_pub 64 = B.alloca 0x00uy 64ul in
  declassify_secret_buffer
    (* len *) 64ul
    (* src *) deviceIDCRI_sig_sec
    (* dst *) deviceIDCRI_sig;

(* Finalize AliasKeyCRT with AliasKeyTBS and Signature *)
  let deviceIDCRI_buf32: B32.lbytes32 deviceIDCRI_len = B32.of_buffer deviceIDCRI_len deviceIDCRI_buf in
  let deviceIDCRI_sig32: x509_signature_raw_t = B32.of_buffer 64ul deviceIDCRI_sig in

  printf "Creating AliasKey Certificate CRT message\n" done;
  let deviceIDCSR: deviceIDCSR_t deviceIDCRI_len = x509_get_deviceIDCSR
                                                             deviceIDCRI_len
                                                             deviceIDCRI_buf32
                                                             deviceIDCRI_sig32 in
  (* Prf *) lemma_serialize_deviceIDCSR_size_exact deviceIDCRI_len deviceIDCSR;

  printf "Serializing AliasKey Certificate CRT\n" done;
(* Serialize AliasKeyCRT *)
  let offset = serialize32_deviceIDCSR_backwards
                 deviceIDCRI_len
                 deviceIDCSR
                 deviceIDCSR_buf
                 deviceIDCSR_len in

  HST.pop_frame ()
#pop-options

#push-options "--z3rlimit 256"
[@@ "opaque_to_smt"]
unfold
let riot_core_step2_pre
  (h: HS.mem)
  (csr_version: datatype_of_asn1_type INTEGER)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (deviceID_pub: B.lbuffer byte_pub 32)
  (deviceID_priv: B.lbuffer byte_sec 32)
  (deviceIDCSR_len: size_t)
  (deviceIDCSR_buf: B.lbuffer byte_pub (v deviceIDCSR_len))
= let deviceIDCRI_len: asn1_TLV_int32_of_type SEQUENCE = len_of_deviceIDCRI
                                                            csr_version
                                                            s_common
                                                            s_org
                                                            s_country in
  B.all_live h [B.buf deviceID_pub;
                B.buf deviceID_priv;
                B.buf deviceIDCSR_buf] /\
  B.all_disjoint [B.loc_buffer deviceID_pub;
                  B.loc_buffer deviceID_priv;
                  B.loc_buffer deviceIDCSR_buf] /\
  0 < v deviceIDCRI_len /\ valid_deviceIDCSR_ingredients deviceIDCRI_len /\
  v deviceIDCSR_len == length_of_deviceIDCSR deviceIDCRI_len

#push-options "--z3rlimit 256"
[@@ "opaque_to_smt"]
unfold
let riot_core_step2_post
  (h0: HS.mem) (h1: HS.mem)
  (csr_version: datatype_of_asn1_type INTEGER)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (deviceID_pub: B.lbuffer byte_pub 32)
  (deviceID_priv: B.lbuffer byte_sec 32)
  (deviceIDCSR_len: UInt32.t)
  (deviceIDCSR_buf: B.lbuffer byte_pub (v deviceIDCSR_len))
= let deviceIDCRI_len: asn1_TLV_int32_of_type SEQUENCE = len_of_deviceIDCRI
                                                            csr_version
                                                            s_common
                                                            s_org
                                                            s_country in
  let deviceIDCRI: deviceIDCRI_t = create_deviceIDCRI_spec
                                                                      (csr_version)
                                                                      (s_common)
                                                                      (s_org)
                                                                      (s_country)
                                                                      (ku)
                                                                      (B.as_seq h0 deviceID_pub) in
  let deviceIDCRI_seq = serialize_deviceIDCRI `serialize` deviceIDCRI in
  let (* Prf *) _ = lemma_serialize_deviceIDCRI_size_exact deviceIDCRI in  //AR: TODO: This takes long time
  let deviceIDCSR: deviceIDCSR_t deviceIDCRI_len = sign_and_finalize_deviceIDCSR_spec
                                                                      (B.as_seq h0 deviceID_priv)
                                                                      (deviceIDCRI_len)
                                                                      (deviceIDCRI_seq) in
  (* Prf *) lemma_serialize_deviceIDCSR_size_exact deviceIDCRI_len deviceIDCSR;
  B.modifies (B.loc_buffer deviceIDCSR_buf) h0 h1 /\
  B.as_seq h1 deviceIDCSR_buf == serialize_deviceIDCSR deviceIDCRI_len `serialize` deviceIDCSR
#pop-options

#set-options "--z3rlimit 200 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"
[@@ "opaque_to_smt"]
inline_for_extraction noextract
let riot_core_step2
  (csr_version: datatype_of_asn1_type INTEGER)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (deviceID_pub: B.lbuffer byte_pub 32)
  (deviceID_priv: B.lbuffer byte_sec 32)
  (deviceIDCSR_len: size_t)
  (deviceIDCSR_buf: B.lbuffer byte_pub (v deviceIDCSR_len))
: HST.Stack unit
  (requires fun h -> riot_core_step2_pre (h)
                     (csr_version) (s_common) (s_org) (s_country) (ku)
                     (deviceID_pub) (deviceID_priv)
                     (deviceIDCSR_len) (deviceIDCSR_buf))
  (ensures fun h0 _ h1 -> riot_core_step2_post (h0) (h1)
                     (csr_version) (s_common) (s_org) (s_country) (ku)
                     (deviceID_pub) (deviceID_priv)
                     (deviceIDCSR_len) (deviceIDCSR_buf))
= (**) let h0 = HST.get () in
  HST.push_frame ();
  (**) let hs0 = HST.get () in
  (**) B.fresh_frame_modifies h0 hs0;

  let deviceIDCRI_len: asn1_TLV_int32_of_type SEQUENCE = len_of_deviceIDCRI
                                                            csr_version
                                                            s_common
                                                            s_org
                                                            s_country in
  let deviceIDCRI_buf: B.lbuffer byte_pub (v deviceIDCRI_len) = B.alloca 0x00uy deviceIDCRI_len in
  (**) let hs1 = HST.get () in

  (**) B.modifies_buffer_elim deviceID_pub B.loc_none h0 hs1;
  printf "Creating DeviceID Certificate Signing Request Information\n" done;
  create_deviceIDCRI
    (* version   *) csr_version
                    s_common
                    s_org
                    s_country
                    ku
    (* DeviceID  *) deviceID_pub
    (*DeviceIDCRI*) deviceIDCRI_len
                    deviceIDCRI_buf;
  (**) let hs2 = HST.get () in

  (**) assert (
    let deviceIDCRI: deviceIDCRI_t = create_deviceIDCRI_spec
                                                                      (csr_version)
                                                                      (s_common)
                                                                      (s_org)
                                                                      (s_country)
                                                                      (ku)
                                                                      (B.as_seq h0 deviceID_pub) in
    (* Prf *) lemma_serialize_deviceIDCRI_size_exact deviceIDCRI;
    B.as_seq hs2 deviceIDCRI_buf == serialize_deviceIDCRI `serialize` deviceIDCRI
  );

  (**) B.modifies_trans B.loc_none h0 hs1 (B.loc_buffer deviceIDCRI_buf) hs2;
  (**) B.modifies_buffer_elim deviceID_priv (B.loc_buffer deviceIDCRI_buf) h0 hs2;
  printf "Signing and finalizing DeviceID Certificate Signing Request\n" done;
  sign_and_finalize_deviceIDCSR
    (*Signing Key*) deviceID_priv
    (*DeviceIDCRI*) deviceIDCRI_len
                    deviceIDCRI_buf
    (*DeviceIDCSR*) deviceIDCSR_len
                    deviceIDCSR_buf;
  (**) let hs3 = HST.get () in

  (**) assert (
    let deviceIDCSR: deviceIDCSR_t deviceIDCRI_len = sign_and_finalize_deviceIDCSR_spec
                                                                      (B.as_seq h0 deviceID_priv)
                                                                      (deviceIDCRI_len)
                                                                      (B.as_seq hs2 deviceIDCRI_buf) in
    (* Prf *) lemma_serialize_deviceIDCSR_size_exact deviceIDCRI_len deviceIDCSR;
    B.as_seq hs3 deviceIDCSR_buf == serialize_deviceIDCSR deviceIDCRI_len `serialize` deviceIDCSR
  );

  (**) assert (
    let deviceIDCRI_len: asn1_TLV_int32_of_type SEQUENCE = len_of_deviceIDCRI
                                                            csr_version
                                                            s_common
                                                            s_org
                                                            s_country in
    let deviceIDCRI: deviceIDCRI_t = create_deviceIDCRI_spec
                                                                      (csr_version)
                                                                      (s_common)
                                                                      (s_org)
                                                                      (s_country)
                                                                      (ku)
                                                                      (B.as_seq h0 deviceID_pub) in
    let deviceIDCRI_seq = serialize_deviceIDCRI `serialize` deviceIDCRI in
    let (* Prf *) _ = lemma_serialize_deviceIDCRI_size_exact deviceIDCRI in
    let deviceIDCSR: deviceIDCSR_t deviceIDCRI_len = sign_and_finalize_deviceIDCSR_spec
                                                                      (B.as_seq h0 deviceID_priv)
                                                                      (deviceIDCRI_len)
                                                                      (deviceIDCRI_seq) in
    (* Prf *) lemma_serialize_deviceIDCSR_size_exact deviceIDCRI_len deviceIDCSR;
    B.as_seq hs3 deviceIDCSR_buf == serialize_deviceIDCSR deviceIDCRI_len `serialize` deviceIDCSR
  );

  (**) B.modifies_trans (B.loc_buffer deviceIDCRI_buf) h0 hs2 (B.loc_buffer deviceIDCSR_buf) hs3;
  (**) let hsf = HST.get () in
  HST.pop_frame ();
  (**) let hf = HST.get () in
  (**) B.popped_modifies hsf hf;
  (**) B.modifies_buffer_elim deviceIDCSR_buf (B.loc_region_only false (HS.get_tip hsf)) hsf hf;
  (**) B.modifies_fresh_frame_popped h0 hs0 (
    B.loc_buffer deviceIDCSR_buf
  ) hsf hf;
()

#reset-options
#set-options "--fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"
#push-options "--z3rlimit 50"
[@@ "opaque_to_smt"]
unfold
let riot_core_step3_pre
  (h: HS.mem)
  (crt_version: x509_version_t)
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (notBefore: datatype_of_asn1_type UTC_TIME)
  (notAfter : datatype_of_asn1_type Generalized_Time)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (fwid: B.lbuffer byte_pub 32)
  (ku: key_usage_payload_t)
  (keyID: B.lbuffer byte_pub 20)
  (riot_version: datatype_of_asn1_type INTEGER)
  (deviceID_pub: B.lbuffer byte_pub 32)
  (deviceID_priv: B.lbuffer byte_sec 32)
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKeyCRT_len: UInt32.t)
  (aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len))
: Type0
= let aliasKeyTBS_len: asn1_TLV_int32_of_type SEQUENCE = len_of_aliasKeyTBS
                                                           serialNumber
                                                           i_common i_org i_country
                                                           s_common s_org s_country
                                                           riot_version in
  B.all_live h [B.buf fwid;
                B.buf deviceID_pub;
                B.buf deviceID_priv;
                B.buf aliasKey_pub;
                B.buf keyID;
                B.buf aliasKeyCRT_buf] /\
  B.all_disjoint [B.loc_buffer fwid;
                  B.loc_buffer deviceID_pub;
                  B.loc_buffer deviceID_priv;
                  B.loc_buffer aliasKey_pub;
                  B.loc_buffer keyID;
                  B.loc_buffer aliasKeyCRT_buf] /\
  0 < v aliasKeyTBS_len /\ valid_aliasKeyCRT_ingredients aliasKeyTBS_len /\
  v aliasKeyCRT_len `eq2 #nat` length_of_aliasKeyCRT aliasKeyTBS_len
#pop-options

#push-options "--z3rlimit 512"
[@@ "opaque_to_smt"]
unfold
let riot_core_step3_post
  (h0: HS.mem) (h1: HS.mem)
  (crt_version: x509_version_t)
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (notBefore: datatype_of_asn1_type UTC_TIME)
  (notAfter : datatype_of_asn1_type Generalized_Time)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (fwid: B.lbuffer byte_pub 32)
  (ku: key_usage_payload_t)
  (keyID: B.lbuffer byte_pub 20)
  (riot_version: datatype_of_asn1_type INTEGER)
  (deviceID_pub: B.lbuffer byte_pub 32)
  (deviceID_priv: B.lbuffer byte_sec 32)
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKeyCRT_len: UInt32.t)
  (aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len))
= let aliasKeyTBS_len: asn1_TLV_int32_of_type SEQUENCE = len_of_aliasKeyTBS
                                                           serialNumber
                                                           i_common i_org i_country
                                                           s_common s_org s_country
                                                           riot_version in
  let aliasKeyTBS = create_aliasKeyTBS_spec
                                     (crt_version)
                                     (serialNumber)
                                     (i_common) (i_org) (i_country)
                                     (notBefore) (notAfter)
                                     (s_common) (s_org) (s_country)
                                     (ku)
                                     (B.as_seq h0 keyID)
                                     (riot_version)
                                     (B.as_seq h0 fwid)
                                     (B.as_seq h0 deviceID_pub)
                                     (B.as_seq h0 aliasKey_pub) in
  let aliasKeyTBS_seq = serialize_aliasKeyTBS `serialize` aliasKeyTBS in
  (* Prf *) lemma_serialize_aliasKeyTBS_size_exact aliasKeyTBS;
  let aliasKeyCRT: aliasKeyCRT_t aliasKeyTBS_len = sign_and_finalize_aliasKeyCRT_spec
                                                                      (B.as_seq h0 deviceID_priv)
                                                                      (aliasKeyTBS_len)
                                                                      (aliasKeyTBS_seq) in
  (* Prf *) lemma_serialize_aliasKeyCRT_size_exact aliasKeyTBS_len aliasKeyCRT;
    B.(modifies (loc_buffer aliasKeyCRT_buf) h0 h1) /\
    B.as_seq h1 aliasKeyCRT_buf == serialize_aliasKeyCRT aliasKeyTBS_len `serialize` aliasKeyCRT
#pop-options

#set-options "--z3rlimit 200 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"
[@@ "opaque_to_smt"]
inline_for_extraction noextract
let riot_core_step3
  (crt_version: x509_version_t)
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (notBefore: datatype_of_asn1_type UTC_TIME)
  (notAfter : datatype_of_asn1_type Generalized_Time)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (fwid: B.lbuffer byte_pub 32)
  (ku: key_usage_payload_t)
  (keyID: B.lbuffer byte_pub 20)
  (riot_version: datatype_of_asn1_type INTEGER)
  (deviceID_pub: B.lbuffer byte_pub 32)
  (deviceID_priv: B.lbuffer byte_sec 32)
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKeyCRT_len: UInt32.t)
  (aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len))
: HST.Stack unit
  (requires fun h -> riot_core_step3_pre (h)
                     (crt_version) (serialNumber) (i_common) (i_org) (i_country)
                     (notBefore) (notAfter) (s_common) (s_org) (s_country)
                     (fwid) (ku) (keyID) (riot_version)
                     (deviceID_pub) (deviceID_priv) (aliasKey_pub)
                     (aliasKeyCRT_len) (aliasKeyCRT_buf)
  )
  (ensures fun h0 _ h1 -> riot_core_step3_post (h0) (h1)
                     (crt_version) (serialNumber) (i_common) (i_org) (i_country)
                     (notBefore) (notAfter) (s_common) (s_org) (s_country)
                     (fwid) (ku) (keyID) (riot_version)
                     (deviceID_pub) (deviceID_priv) (aliasKey_pub)
                     (aliasKeyCRT_len) (aliasKeyCRT_buf))
= (**) let h0 = HST.get () in
  HST.push_frame ();
  (**) let hs0 = HST.get () in B.fresh_frame_modifies h0 hs0;

(* Create AliasKeyTBS *)
  let aliasKeyTBS_len: asn1_TLV_int32_of_type SEQUENCE = len_of_aliasKeyTBS
                                                           serialNumber
                                                           i_common
                                                           i_org
                                                           i_country
                                                           s_common
                                                           s_org
                                                           s_country
                                                           riot_version in
  let aliasKeyTBS_buf: B.lbuffer byte_pub (v aliasKeyTBS_len) = B.alloca 0x00uy aliasKeyTBS_len in
  (**) let hs1 = HST.get () in

  (**) B.modifies_buffer_elim fwid         B.loc_none h0 hs1;
  (**) B.modifies_buffer_elim keyID        B.loc_none h0 hs1;
  (**) B.modifies_buffer_elim deviceID_pub B.loc_none h0 hs1;
  (**) B.modifies_buffer_elim aliasKey_pub B.loc_none h0 hs1;
  printf "Creating AliasKey Certificate TBS\n" done;
  create_aliasKeyTBS
    (crt_version) (serialNumber)
    (i_common) (i_org) (i_country)
    (notBefore) (notAfter)
    (s_common) (s_org) (s_country)
    (fwid) (ku) (keyID) (riot_version)
    (* DeviceID  *) deviceID_pub
    (* AliasKey  *) aliasKey_pub
    (*AliasKeyTBS*) aliasKeyTBS_len
                    aliasKeyTBS_buf;
  (**) let hs2 = HST.get () in

  (**) assert (
    let aliasKeyTBS = create_aliasKeyTBS_spec
                                     (crt_version)
                                     (serialNumber)
                                     (i_common) (i_org) (i_country)
                                     (notBefore) (notAfter)
                                     (s_common) (s_org) (s_country)
                                     (ku)
                                     (B.as_seq h0 keyID)
                                     (riot_version)
                                     (B.as_seq h0 fwid)
                                     (B.as_seq h0 deviceID_pub)
                                     (B.as_seq h0 aliasKey_pub) in
    (* Prf *) lemma_serialize_aliasKeyTBS_size_exact aliasKeyTBS;
    B.as_seq hs2 aliasKeyTBS_buf == serialize_aliasKeyTBS `serialize` aliasKeyTBS
  );

  (**) B.modifies_trans B.loc_none h0 hs1 (B.loc_buffer aliasKeyTBS_buf) hs2;
  (**) B.modifies_buffer_elim deviceID_priv (B.loc_buffer aliasKeyTBS_buf) h0 hs2;
  printf "Signing and finalizing AliasKey Certificate\n" done;
  sign_and_finalize_aliasKeyCRT
    (*Signing Key*) deviceID_priv
    (*AliasKeyTBS*) aliasKeyTBS_len
                    aliasKeyTBS_buf
    (*AliasKeyCRT*) aliasKeyCRT_len
                    aliasKeyCRT_buf;
  (**) let hs3 = HST.get () in

  (**) assert (
    let aliasKeyCRT: aliasKeyCRT_t aliasKeyTBS_len = sign_and_finalize_aliasKeyCRT_spec
                                                                      (B.as_seq h0 deviceID_priv)
                                                                      (aliasKeyTBS_len)
                                                                      (B.as_seq hs2 aliasKeyTBS_buf) in
    (* Prf *) lemma_serialize_aliasKeyCRT_size_exact aliasKeyTBS_len aliasKeyCRT;
    B.as_seq hs3 aliasKeyCRT_buf == serialize_aliasKeyCRT aliasKeyTBS_len `serialize` aliasKeyCRT
  );

  (**) assert (
    let aliasKeyTBS_len: asn1_TLV_int32_of_type SEQUENCE = len_of_aliasKeyTBS
                                                           serialNumber
                                                           i_common i_org i_country
                                                           s_common s_org s_country
                                                           riot_version in
    let aliasKeyTBS = create_aliasKeyTBS_spec
                                     (crt_version)
                                     (serialNumber)
                                     (i_common) (i_org) (i_country)
                                     (notBefore) (notAfter)
                                     (s_common) (s_org) (s_country)
                                     (ku)
                                     (B.as_seq h0 keyID)
                                     (riot_version)
                                     (B.as_seq h0 fwid)
                                     (B.as_seq h0 deviceID_pub)
                                     (B.as_seq h0 aliasKey_pub) in
    let aliasKeyTBS_seq = serialize_aliasKeyTBS `serialize` aliasKeyTBS in
    (* Prf *) lemma_serialize_aliasKeyTBS_size_exact aliasKeyTBS;
    let aliasKeyCRT: aliasKeyCRT_t aliasKeyTBS_len = sign_and_finalize_aliasKeyCRT_spec
                                                                      (B.as_seq h0 deviceID_priv)
                                                                      (aliasKeyTBS_len)
                                                                      (aliasKeyTBS_seq) in
    (* Prf *) lemma_serialize_aliasKeyCRT_size_exact aliasKeyTBS_len aliasKeyCRT;
    B.as_seq hs3 aliasKeyCRT_buf == serialize_aliasKeyCRT aliasKeyTBS_len `serialize` aliasKeyCRT
  );

  (**) B.modifies_trans (B.loc_buffer aliasKeyTBS_buf) h0 hs2 (B.loc_buffer aliasKeyCRT_buf) hs3;
  (**) let hsf = HST.get () in
  HST.pop_frame ();
  (**) let hf = HST.get () in B.popped_modifies hsf hf;
  (**) B.modifies_buffer_elim aliasKeyCRT_buf (B.loc_region_only false (HS.get_tip hsf)) hsf hf;
  (**) B.modifies_fresh_frame_popped h0 hs0 (
    B.loc_buffer aliasKeyCRT_buf
  ) hsf hf;
()
