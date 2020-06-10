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

open RIoT.Spec.Certificate

#set-options "--z3rlimit 256 --fuel 0 --ifuel 0"

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
    valid_aliasKeyTBS_ingredients aliasKeyTBS_template_len riot_version /\
    v aliasKeyTBS_len == length_of_AliasKeyTBS aliasKeyTBS_template_len riot_version
   )
  (ensures fun h0 _ h1 ->
    let aliasKeyTBS: aliasKeyTBS_t_inbound aliasKeyTBS_template_len = create_aliasKeyTBS_spec
                                                                      (aliasKeyTBS_template_len)
                                                                      (B.as_seq h0 aliasKeyTBS_template)
                                                                      (riot_version)
                                                                      (B.as_seq h0 fwid)
                                                                      (B.as_seq h0 deviceID_pub)
                                                                      (B.as_seq h0 aliasKey_pub) in
    (* Prf *) lemma_serialize_aliasKeyTBS_sequence_TLV_size_exact aliasKeyTBS_template_len aliasKeyTBS;
    B.(modifies (loc_buffer aliasKeyTBS_buf) h0 h1) /\
    B.as_seq h1 aliasKeyTBS_buf == serialize_aliasKeyTBS_sequence_TLV aliasKeyTBS_template_len `serialize` aliasKeyTBS
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
  let aliasKeyTBS: aliasKeyTBS_t_inbound aliasKeyTBS_template_len = x509_get_AliasKeyTBS
                                                                    aliasKeyTBS_template_len
                                                                    aliasKeyTBS_template32
                                                                    riot_version
                                                                    fwid_pub32
                                                                    deviceID_pub32
                                                                    aliasKey_pub32 in

  (* Prf *) lemma_serialize_aliasKeyTBS_sequence_TLV_size_exact aliasKeyTBS_template_len aliasKeyTBS;

(* Serialize AliasKeyTBS *)
  let offset = serialize32_aliasKeyTBS_sequence_TLV_backwards
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
    v aliasKeyCRT_len == length_of_AliasKeyCRT aliasKeyTBS_len
   )
  (ensures fun h0 _ h1 ->
    let aliasKeyCRT: aliasKeyCRT_t_inbound aliasKeyTBS_len = sign_and_finalize_aliasKeyCRT_spec
                                                                      (B.as_seq h0 deviceID_priv)
                                                                      (aliasKeyTBS_len)
                                                                      (B.as_seq h0 aliasKeyTBS_buf) in
    (* Prf *) lemma_serialize_aliasKeyCRT_sequence_TLV_size_exact aliasKeyTBS_len aliasKeyCRT;
    B.(modifies (loc_buffer aliasKeyCRT_buf) h0 h1) /\
    B.as_seq h1 aliasKeyCRT_buf == serialize_aliasKeyCRT_sequence_TLV aliasKeyTBS_len `serialize` aliasKeyCRT
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
  let aliasKeyTBS_sig32: x509_signature_raw_t alg_AliasKey = B32.of_buffer 64ul aliasKeyTBS_sig in
  let aliasKeyCRT: aliasKeyCRT_t_inbound aliasKeyTBS_len = x509_get_AliasKeyCRT
                                                             aliasKeyTBS_len
                                                             aliasKeyTBS_buf32
                                                             aliasKeyTBS_sig32 in
  (* Prf *) lemma_serialize_aliasKeyCRT_sequence_TLV_size_exact aliasKeyTBS_len aliasKeyCRT;

(* Serialize AliasKeyCRT *)
  let offset = serialize32_aliasKeyCRT_sequence_TLV_backwards
                 aliasKeyTBS_len
                 aliasKeyCRT
                 aliasKeyCRT_buf
                 aliasKeyCRT_len in

  HST.pop_frame ()
