module RIoT.Impl.Certificate

open ASN1.Spec
open X509

open RIoT.Base
open RIoT.Declassify
open RIoT.X509

open Lib.IntTypes
module Ed25519 = Hacl.Ed25519

module B32 = FStar.Bytes
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

open LowStar.Comment
open LowStar.Printf

open RIoT.Spec.Certificate

#set-options "--z3rlimit 512 --fuel 0 --ifuel 0"

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

let create_aliasKeyTBS
  (fwid: B.lbuffer byte_sec 32)
  (ku: key_usage_payload_t)
  (riot_version: datatype_of_asn1_type INTEGER)
  (deviceID_pub: B.lbuffer byte_pub 32)
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKeyTBS_template_len: size_t)
  (aliasKeyTBS_template: B.lbuffer byte_pub (v aliasKeyTBS_template_len))
  (aliasKeyTBS_len: size_t)
  (aliasKeyTBS_buf: B.lbuffer byte_pub (v aliasKeyTBS_len))
: HST.Stack unit
  (requires fun h ->
    B.(all_live h [buf fwid;
                   buf deviceID_pub;
                   buf aliasKey_pub;
                   buf aliasKeyTBS_template;
                   buf aliasKeyTBS_buf]) /\
    B.(all_disjoint [loc_buffer fwid;
                     loc_buffer deviceID_pub;
                     loc_buffer aliasKey_pub;
                     loc_buffer aliasKeyTBS_template;
                     loc_buffer aliasKeyTBS_buf]) /\
    valid_aliasKeyTBS_ingredients aliasKeyTBS_template_len ku riot_version /\
    v aliasKeyTBS_len == length_of_aliasKeyTBS aliasKeyTBS_template_len ku riot_version
   )
  (ensures fun h0 _ h1 ->
    let aliasKeyTBS: aliasKeyTBS_t aliasKeyTBS_template_len = create_aliasKeyTBS_spec
                                                                      (aliasKeyTBS_template_len)
                                                                      (B.as_seq h0 aliasKeyTBS_template)
                                                                      (ku)
                                                                      (riot_version)
                                                                      (B.as_seq h0 fwid)
                                                                      (B.as_seq h0 deviceID_pub)
                                                                      (B.as_seq h0 aliasKey_pub) in
    (* Prf *) lemma_serialize_aliasKeyTBS_size_exact aliasKeyTBS_template_len aliasKeyTBS;
    B.(modifies (loc_buffer aliasKeyTBS_buf) h0 h1) /\
    B.as_seq h1 aliasKeyTBS_buf == serialize_aliasKeyTBS aliasKeyTBS_template_len `serialize` aliasKeyTBS
  )
=
  HST.push_frame ();

(* Create AliasKeyTBS *)
  let aliasKeyTBS_template32: B32.lbytes32 aliasKeyTBS_template_len = B32.of_buffer aliasKeyTBS_template_len aliasKeyTBS_template in
  let fwid_pub      : B.lbuffer byte_pub 32 = B.alloca 0x00uy 32ul in
  declassify_secret_buffer 32ul fwid fwid_pub;
  let fwid_pub32    : B32.lbytes32 32ul = B32.of_buffer 32ul fwid_pub in
  let deviceID_pub32: B32.lbytes32 32ul = B32.of_buffer 32ul deviceID_pub in
  let aliasKey_pub32: B32.lbytes32 32ul = B32.of_buffer 32ul aliasKey_pub in

  printf "Creating AliasKey Certificate TBS Message\n" done;
  let aliasKeyTBS: aliasKeyTBS_t aliasKeyTBS_template_len = x509_get_AliasKeyTBS
                                                                    aliasKeyTBS_template_len
                                                                    aliasKeyTBS_template32
                                                                    ku
                                                                    riot_version
                                                                    fwid_pub32
                                                                    deviceID_pub32
                                                                    aliasKey_pub32 in

  (* Prf *) lemma_serialize_aliasKeyTBS_size_exact aliasKeyTBS_template_len aliasKeyTBS;

  printf "Serializing AliasKey Certificate TBS\n" done;
(* Serialize AliasKeyTBS *)
  let offset = serialize32_aliasKeyTBS_backwards
                 aliasKeyTBS_template_len
                 aliasKeyTBS
                 aliasKeyTBS_buf
                 aliasKeyTBS_len in

  HST.pop_frame ()


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
=
  HST.push_frame ();

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

  printf "Serializing AliasKey Certificate CRT\n" done;
(* Serialize AliasKeyCRT *)
  let offset = serialize32_aliasKeyCRT_backwards
                 aliasKeyTBS_len
                 aliasKeyCRT
                 aliasKeyCRT_buf
                 aliasKeyCRT_len in

  HST.pop_frame ()

(*                 CSR
 *=====================================
 *)


let create_deviceIDCRI
  (csr_version: datatype_of_asn1_type INTEGER)
  (ku: key_usage_payload_t)
  (deviceID_pub: B.lbuffer byte_pub 32)
  (deviceIDCRI_template_len: size_t)
  (deviceIDCRI_template: B.lbuffer byte_pub (v deviceIDCRI_template_len))
  (deviceIDCRI_len: size_t)
  (deviceIDCRI_buf: B.lbuffer byte_pub (v deviceIDCRI_len))
: HST.Stack unit
  (requires fun h ->
    B.(all_live h [buf deviceID_pub;
                   buf deviceIDCRI_template;
                   buf deviceIDCRI_buf]) /\
    B.(all_disjoint [loc_buffer deviceID_pub;
                     loc_buffer deviceIDCRI_template;
                     loc_buffer deviceIDCRI_buf]) /\
    valid_deviceIDCRI_ingredients deviceIDCRI_template_len csr_version ku /\
    v deviceIDCRI_len == length_of_deviceIDCRI deviceIDCRI_template_len csr_version ku
   )
  (ensures fun h0 _ h1 ->
    let deviceIDCRI: deviceIDCRI_t deviceIDCRI_template_len = create_deviceIDCRI_spec
                                                                      (deviceIDCRI_template_len)
                                                                      (B.as_seq h0 deviceIDCRI_template)
                                                                      (csr_version)
                                                                      (ku)
                                                                      (B.as_seq h0 deviceID_pub) in
    (* Prf *) lemma_serialize_deviceIDCRI_size_exact deviceIDCRI_template_len deviceIDCRI;
    B.(modifies (loc_buffer deviceIDCRI_buf) h0 h1) /\
    B.as_seq h1 deviceIDCRI_buf == serialize_deviceIDCRI deviceIDCRI_template_len `serialize` deviceIDCRI
  )
=
  HST.push_frame ();

(* Create deviceIDCRI *)
  let deviceIDCRI_template32: B32.lbytes32 deviceIDCRI_template_len = B32.of_buffer deviceIDCRI_template_len deviceIDCRI_template in
  let deviceID_pub32: B32.lbytes32 32ul = B32.of_buffer 32ul deviceID_pub in

  printf "Creating AliasKey Certificate TBS Message\n" done;
  let deviceIDCRI: deviceIDCRI_t deviceIDCRI_template_len = x509_get_deviceIDCRI
                                                                    deviceIDCRI_template_len
                                                                    deviceIDCRI_template32
                                                                    csr_version
                                                                    ku
                                                                    deviceID_pub32 in

  (* Prf *) lemma_serialize_deviceIDCRI_size_exact deviceIDCRI_template_len deviceIDCRI;

  printf "Serializing AliasKey Certificate TBS\n" done;
(* Serialize deviceIDCRI *)
  let offset = serialize32_deviceIDCRI_backwards
                 deviceIDCRI_template_len
                 deviceIDCRI
                 deviceIDCRI_buf
                 deviceIDCRI_len in

  HST.pop_frame ()

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