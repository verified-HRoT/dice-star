module RIoT.Impl.Certificate

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

unfold
let create_aliasKeyTBS_pre
  (h: HS.mem)
  (crt_version: x509_version_t)
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (notBefore: datatype_of_asn1_type Generalized_Time)
  (notAfter : datatype_of_asn1_type Generalized_Time)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (fwid: B.lbuffer byte_sec 32)
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
  eq2 #nat (UInt32.v aliasKeyTBS_len) (length_of_aliasKeyTBS
                         serialNumber
                         i_common i_org i_country
                         s_common s_org s_country
                         ku riot_version)

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
  (notBefore: datatype_of_asn1_type Generalized_Time)
  (notAfter : datatype_of_asn1_type Generalized_Time)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (fwid: B.lbuffer byte_sec 32)
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

#push-options "--z3rlimit 64"
inline_for_extraction noextract
let create_aliasKeyTBS_buffers_to_bytes
  (fwid: B.lbuffer byte_sec 32)
  (keyID: B.lbuffer byte_pub 20)
  (deviceID_pub: B.lbuffer byte_pub 32)
  (aliasKey_pub: B.lbuffer byte_pub 32)
  : HST.Stack
      (B32.lbytes32 32ul &  //fwid
       B32.lbytes32 20ul &  //key id
       B32.lbytes32 32ul &  //device id
       B32.lbytes32 32ul)  //alias key
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
        (let (fwid_pub32, keyID_pub32, deviceID_pub32, aliasKey_pub32) = r in
         B32.hide (declassify_secret_bytes (B.as_seq h0 fwid)) == fwid_pub32 /\
         B32.hide (B.as_seq h0 deviceID_pub) == deviceID_pub32 /\
         B32.hide (B.as_seq h0 aliasKey_pub) == aliasKey_pub32 /\
         B32.hide (B.as_seq h0 keyID) == keyID_pub32))
  = HST.push_frame ();
    let fwid_pub      : B.lbuffer byte_pub 32 = B.alloca 0x00uy 32ul in
    declassify_secret_buffer 32ul fwid fwid_pub;
    let fwid_pub32    : B32.lbytes32 32ul = B32.of_buffer 32ul fwid_pub in
    let deviceID_pub32: B32.lbytes32 32ul = B32.of_buffer 32ul deviceID_pub in
    let aliasKey_pub32: B32.lbytes32 32ul = B32.of_buffer 32ul aliasKey_pub in
    let keyID_pub32 = B32.of_buffer 20ul keyID in
    HST.pop_frame ();
    fwid_pub32, keyID_pub32, deviceID_pub32, aliasKey_pub32

let create_aliasKeyTBS
  (crt_version: x509_version_t)
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (notBefore: datatype_of_asn1_type Generalized_Time)
  (notAfter : datatype_of_asn1_type Generalized_Time)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (fwid: B.lbuffer byte_sec 32)
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

  let fwid_pub32, keyID_pub32, deviceID_pub32, aliasKey_pub32 =
    create_aliasKeyTBS_buffers_to_bytes fwid keyID deviceID_pub aliasKey_pub in

  let keyID_string: datatype_of_asn1_type OCTET_STRING = (|20ul, keyID_pub32|) in

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
                                     fwid_pub32
                                     deviceID_pub32
                                     aliasKey_pub32 in
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
    valid_deviceIDCRI_ingredients csr_version s_common s_org s_country ku /\
    v deviceIDCRI_len == length_of_deviceIDCRI csr_version s_common s_org s_country ku
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
