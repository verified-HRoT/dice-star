/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/RIoT/Core/RIoT.cpp
module RIoT.Core

open LowStar.Comment
open LowStar.Printf
module Fail = LowStar.Failure
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B32 = FStar.Bytes

open Lib.IntTypes
open Spec.Hash.Definitions
open Hacl.Hash.Definitions

open ASN1.Spec
open ASN1.Low
open X509

open RIoT.X509
open RIoT.Base
open RIoT.Declassify
open RIoT.Spec
open RIoT.Impl

#restart-solver
#push-options "--query_stats --z3rlimit 1024 --fuel 0 --ifuel 0"
let riot
(* inputs *)
  (cdi : B.lbuffer byte_sec 32)
  (fwid: B.lbuffer byte_sec 32)
  (version: datatype_of_asn1_type INTEGER)
  (aliasKeyTBS_template_len: size_t)
  (aliasKeyTBS_template: B.lbuffer byte_pub (v aliasKeyTBS_template_len))
  (deviceID_label_len: size_t)
  (deviceID_label: B.lbuffer byte_sec (v deviceID_label_len))
  (aliasKey_label_len: size_t)
  (aliasKey_label: B.lbuffer byte_sec (v aliasKey_label_len))
(* outputs *)
  (aliasKeyCRT_len: size_t)
  (aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len))
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKey_priv: B.lbuffer uint8 32)
: HST.Stack unit
  (requires fun h ->
    B.(all_live h [buf cdi;
                   buf fwid;
                   buf aliasKeyTBS_template;
                   buf deviceID_label;
                   buf aliasKey_label;
                   buf aliasKeyCRT_buf;
                   buf aliasKey_pub;
                   buf aliasKey_priv]) /\
    B.(all_disjoint [loc_buffer cdi;
                     loc_buffer fwid;
                     loc_buffer aliasKeyTBS_template;
                     loc_buffer deviceID_label;
                     loc_buffer aliasKey_label;
                     loc_buffer aliasKeyCRT_buf;
                     loc_buffer aliasKey_pub;
                     loc_buffer aliasKey_priv]) /\
   (* Pre: labels have enough length for HKDF *)
   valid_hkdf_lbl_len deviceID_label_len /\
   valid_hkdf_lbl_len aliasKey_label_len /\
   (* Pre: AliasKeyTBS template has a valid length *)
   valid_aliasKeyTBS_ingredients aliasKeyTBS_template_len version /\
   (* Pre: AliasKeyTBS will have a valid length *)
   valid_aliasKeyCRT_ingredients (len_of_AliasKeyTBS aliasKeyTBS_template_len version) /\
   (* Pre: `aliasKeyCRT_buf` has exact size to write AliasKeyCRT *)
   v aliasKeyCRT_len == length_of_AliasKeyCRT (len_of_AliasKeyTBS aliasKeyTBS_template_len version)
   )
   (ensures fun h0 _ h1 -> True /\
    (* Post: Modifies *)
     B.(modifies (loc_buffer aliasKeyCRT_buf `loc_union` loc_buffer aliasKey_pub `loc_union` loc_buffer aliasKey_priv) h0 h1) /\
    (* Post: AliasKey *)
    ((B.as_seq h1 aliasKey_pub  <: lbytes_pub 32),
     (B.as_seq h1 aliasKey_priv <: lbytes_sec 32)) == derive_AliasKey_spec
                                                        (B.as_seq h0 cdi)
                                                        (B.as_seq h0 fwid)
                                                        aliasKey_label_len                                                        (B.as_seq h0 aliasKey_label) /\
    (* Post: AliasKeyCRT *)
    (let deviceID_pub_seq, deviceID_priv_seq = derive_DeviceID_spec
                                                 (B.as_seq h0 cdi)
                                                 (deviceID_label_len)
                                                 (B.as_seq h0 deviceID_label) in
     let aliasKeyTBS: aliasKeyTBS_t_inbound aliasKeyTBS_template_len = create_aliasKeyTBS_spec
                                                                         (aliasKeyTBS_template_len)
                                                                         (B.as_seq h0 aliasKeyTBS_template)
                                                                         (version)
                                                                         (B.as_seq h0 fwid)
                                                                         (deviceID_pub_seq)
                                                                         (B.as_seq h1 aliasKey_pub)
                                                                         in
     let aliasKeyTBS_seq = serialize_aliasKeyTBS_sequence_TLV aliasKeyTBS_template_len `serialize` aliasKeyTBS in
     let aliasKeyTBS_len = len_of_AliasKeyTBS aliasKeyTBS_template_len version in
     (* Prf *) lemma_serialize_aliasKeyTBS_sequence_TLV_size_exact aliasKeyTBS_template_len aliasKeyTBS;
    (let aliasKeyCRT: aliasKeyCRT_t_inbound aliasKeyTBS_len = sign_and_finalize_aliasKeyCRT_spec
                                                                (deviceID_priv_seq)
                                                                (aliasKeyTBS_len)
                                                                (aliasKeyTBS_seq) in
     B.as_seq h1 aliasKeyCRT_buf == serialize_aliasKeyCRT_sequence_TLV aliasKeyTBS_len `serialize` aliasKeyCRT)))
=
 HST.push_frame ();

(* Derive DeviceID *)
  let deviceID_pub : B.lbuffer byte_pub 32 = B.alloca 0x00uy    32ul in
  let deviceID_priv: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  printf "Deriving DeviceID\\n" done;
  derive_DeviceID
    (* pub *) deviceID_pub
    (* priv*) deviceID_priv
    (* cdi *) cdi
    (* lbl *) deviceID_label_len
              deviceID_label;

(* Derive AliasKey *)
  printf "Deriving AliasKey\\n" done;
  derive_AliasKey
    (* pub *) aliasKey_pub
    (* priv*) aliasKey_priv
    (* cdi *) cdi
    (* fwid*) fwid
    (* lbl *) aliasKey_label_len
              aliasKey_label;

(* Create AliasKeyTBS *)
  let aliasKeyTBS_len: asn1_TLV_int32_of_type SEQUENCE = len_of_AliasKeyTBS aliasKeyTBS_template_len version in
  let aliasKeyTBS_buf: B.lbuffer byte_pub (v aliasKeyTBS_len) = B.alloca 0x00uy aliasKeyTBS_len in
  printf "Creating AliasKey Certificate TBS\\n" done;
  create_aliasKeyTBS
    (* FWID      *) fwid
    (* Version   *) version
    (* DeviceID  *) deviceID_pub
    (* AliasKey  *) aliasKey_pub
    (* Template  *) aliasKeyTBS_template_len
                    aliasKeyTBS_template
    (*AliasKeyTBS*) aliasKeyTBS_len
                    aliasKeyTBS_buf;

(* Sign AliasKeyTBS and Finalize AliasKeyCRT *)
  printf "SIgning and finalizing AliasKey Certificate\\n" done;
  sign_and_finalize_aliasKeyCRT
    (*Signing Key*) deviceID_priv
    (*AliasKeyTBS*) aliasKeyTBS_len
                    aliasKeyTBS_buf
    (*AliasKeyCRT*) aliasKeyCRT_len
                    aliasKeyCRT_buf;

  HST.pop_frame()
#pop-options

#restart-solver
#push-options "--query_stats --z3rlimit 1024 --fuel 0 --ifuel 0"
let main ()
: HST.ST C.exit_code
  (requires fun h -> True)
  (ensures fun _ _ _ -> True)
=
  HST.push_frame();

  comment "Inputs";
  let cdi : B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  let fwid: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  let version: datatype_of_asn1_type INTEGER = 1l in
  let template_len = 100ul in
  let template_buf: B.lbuffer byte_pub (v template_len) = B.alloca 0x00uy template_len in
  let deviceID_lbl_len: x:size_t {normalize (valid_hkdf_lbl_len x)} = 5ul in
  let deviceID_lbl: B.lbuffer byte_sec (v deviceID_lbl_len) = B.alloca (u8 0x00) deviceID_lbl_len in
  let aliasKey_lbl_len: x:size_t {normalize (valid_hkdf_lbl_len x)} = 5ul in
  let aliasKey_lbl: B.lbuffer byte_sec (v aliasKey_lbl_len) = B.alloca (u8 0x00) aliasKey_lbl_len in
  (* Prf *) assert_norm (valid_hkdf_lbl_len deviceID_lbl_len /\ valid_hkdf_lbl_len aliasKey_lbl_len);

  comment "Outputs";
  let aliasKeyCRT_len = len_of_AliasKeyCRT (len_of_AliasKeyTBS template_len version) in
  let aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len) = B.alloca 0x00uy aliasKeyCRT_len in
  let aliasKey_pub : B.lbuffer byte_pub 32 = B.alloca 0x00uy 32ul in
  let aliasKey_priv: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in

  comment "Call riot main function";
  printf "Enter RIoT\n" done;
  riot
    (* cdi       *) cdi
    (* fwid      *) fwid
    (* version   *) version
    (* template  *) template_len
                    template_buf
    (* labels    *) deviceID_lbl_len
                    deviceID_lbl
                    aliasKey_lbl_len
                    aliasKey_lbl
    (*aliasKeyCRT*) aliasKeyCRT_len
                    aliasKeyCRT_buf
    (* aliasKey  *) aliasKey_pub
                    aliasKey_priv;
  printf "Exit RIoT\n" done;
  printf "AliasKey Public  Key: %xuy \n" 32ul aliasKey_pub  done;
  // printf "AliasKey Private Key: %xuy \n" 32ul aliasKey_priv done;
  printf "AliasKey Certificate: %xuy \n" aliasKeyCRT_len aliasKeyCRT_buf done;

  HST.pop_frame ();
  C.EXIT_SUCCESS
#pop-options

(* A example template in HEX form, where
   1) the outmost SEQUENCE (the leading SEQUENCE Tag and Length)
   2) the SubjectPublicKeyInfo in TBS SEQUENCE
   3) the Signature AlgorithmIdnetifier and Value
   are trimed.

A003020102020100300D06092A864886F70D010105050030819B310B3009060355040613024A50310E300C06035504081305546F6B796F3110300E060355040713074368756F2D6B753111300F060355040A13084672616E6B34444431183016060355040B130F5765624365727420537570706F7274311830160603550403130F4672616E6B344444205765622043413123302106092A864886F70D0109011614737570706F7274406672616E6B3464642E636F6D3022180F31393031313231333230343535325A180F32303338303131393033313430375A304A310B3009060355040613024A50310E300C06035504080C05546F6B796F3111300F060355040A0C084672616E6B3444443118

whose full veriosn is

-----BEGIN CERTIFICATE-----
MIICGjCCAYOgAwIBAgIBADANBgkqhkiG9w0BAQUFADCBmzELMAkGA1UEBhMCSlAx
DjAMBgNVBAgTBVRva3lvMRAwDgYDVQQHEwdDaHVvLWt1MREwDwYDVQQKEwhGcmFu
azRERDEYMBYGA1UECxMPV2ViQ2VydCBTdXBwb3J0MRgwFgYDVQQDEw9GcmFuazRE
RCBXZWIgQ0ExIzAhBgkqhkiG9w0BCQEWFHN1cHBvcnRAZnJhbms0ZGQuY29tMCIY
DzE5MDExMjEzMjA0NTUyWhgPMjAzODAxMTkwMzE0MDdaMEoxCzAJBgNVBAYTAkpQ
MQ4wDAYDVQQIDAVUb2t5bzERMA8GA1UECgwIRnJhbms0REQxGDAWBgNVBAMMD3d3
dy5leGFtcGxlLmNvbTBcMA0GCSqGSIb3DQEBAQUAA0sAMEgCQQCb/GaQeYRCu6sT
/St7+N4VEuXxk+MGinu4seGeJruVAb/nMO1khQLdFWmoNLAG7D81PB4bK4/6jwAb
3wfGrFMHAgMBAAEwDQYJKoZIhvcNAQEFBQADgYEAnzdeQBG2crXnvZyHgCL9dSnm
lnaXJITO//+G59uCvDKbnX+BKvXXxXQIa7GmtzYuw3LC/jJJL307r/CECZr6vV9I
KHn27+yOtrPDOwTDtXyaYOaf8V6fkSVN3iLx7tbEP6R0uEKxaVaqMZ71ed3SO1OL
wq0j8GkKY/K/zl2Nwzc=
-----END CERTIFICATE-----

  0 538: SEQUENCE {
  4 387:   SEQUENCE {
----------------------------------------NOTE: Template Start-------------------------------------------
  8   3:     [0] {
 10   1:       INTEGER 2
       :       }
 13   1:     INTEGER 0
 16  13:     SEQUENCE {
 18   9:       OBJECT IDENTIFIER sha1WithRSAEncryption (1 2 840 113549 1 1 5)
 29   0:       NULL
       :       }
 31 155:     SEQUENCE {
 34  11:       SET {
 36   9:         SEQUENCE {
 38   3:           OBJECT IDENTIFIER countryName (2 5 4 6)
 43   2:           PrintableString 'JP'
       :           }
       :         }
 47  14:       SET {
 49  12:         SEQUENCE {
 51   3:           OBJECT IDENTIFIER stateOrProvinceName (2 5 4 8)
 56   5:           PrintableString 'Tokyo'
       :           }
       :         }
 63  16:       SET {
 65  14:         SEQUENCE {
 67   3:           OBJECT IDENTIFIER localityName (2 5 4 7)
 72   7:           PrintableString 'Chuo-ku'
       :           }
       :         }
 81  17:       SET {
 83  15:         SEQUENCE {
 85   3:           OBJECT IDENTIFIER organizationName (2 5 4 10)
 90   8:           PrintableString 'Frank4DD'
       :           }
       :         }
100  24:       SET {
102  22:         SEQUENCE {
104   3:           OBJECT IDENTIFIER organizationalUnitName (2 5 4 11)
109  15:           PrintableString 'WebCert Support'
       :           }
       :         }
126  24:       SET {
128  22:         SEQUENCE {
130   3:           OBJECT IDENTIFIER commonName (2 5 4 3)
135  15:           PrintableString 'Frank4DD Web CA'
       :           }
       :         }
152  35:       SET {
154  33:         SEQUENCE {
156   9:           OBJECT IDENTIFIER emailAddress (1 2 840 113549 1 9 1)
167  20:           IA5String 'support@frank4dd.com'
       :           }
       :         }
       :       }
189  34:     SEQUENCE {
191  15:       GeneralizedTime 13/12/1901 20:45:52 GMT
208  15:       GeneralizedTime 19/01/2038 03:14:07 GMT
       :       }
225  74:     SEQUENCE {
227  11:       SET {
229   9:         SEQUENCE {
231   3:           OBJECT IDENTIFIER countryName (2 5 4 6)
236   2:           PrintableString 'JP'
       :           }
       :         }
240  14:       SET {
242  12:         SEQUENCE {
244   3:           OBJECT IDENTIFIER stateOrProvinceName (2 5 4 8)
249   5:           UTF8String 'Tokyo'
       :           }
       :         }
256  17:       SET {
258  15:         SEQUENCE {
260   3:           OBJECT IDENTIFIER organizationName (2 5 4 10)
265   8:           UTF8String 'Frank4DD'
       :           }
       :         }
275  24:       SET {
277  22:         SEQUENCE {
279   3:           OBJECT IDENTIFIER commonName (2 5 4 3)
284  15:           UTF8String 'www.example.com'
       :           }
       :         }
       :       }
----------------------------------------NOTE: Template End-------------------------------------------
301  92:     SEQUENCE {
303  13:       SEQUENCE {
305   9:         OBJECT IDENTIFIER rsaEncryption (1 2 840 113549 1 1 1)
316   0:         NULL
       :         }
318  75:       BIT STRING
       :         30 48 02 41 00 9B FC 66 90 79 84 42 BB AB 13 FD
       :         2B 7B F8 DE 15 12 E5 F1 93 E3 06 8A 7B B8 B1 E1
       :         9E 26 BB 95 01 BF E7 30 ED 64 85 02 DD 15 69 A8
       :         34 B0 06 EC 3F 35 3C 1E 1B 2B 8F FA 8F 00 1B DF
       :         07 C6 AC 53 07 02 03 01 00 01
       :       }
       :     }
395  13:   SEQUENCE {
397   9:     OBJECT IDENTIFIER sha1WithRSAEncryption (1 2 840 113549 1 1 5)
408   0:     NULL
       :     }
410 129:   BIT STRING
       :     9F 37 5E 40 11 B6 72 B5 E7 BD 9C 87 80 22 FD 75
       :     29 E6 96 76 97 24 84 CE FF FF 86 E7 DB 82 BC 32
       :     9B 9D 7F 81 2A F5 D7 C5 74 08 6B B1 A6 B7 36 2E
       :     C3 72 C2 FE 32 49 2F 7D 3B AF F0 84 09 9A FA BD
       :     5F 48 28 79 F6 EF EC 8E B6 B3 C3 3B 04 C3 B5 7C
       :     9A 60 E6 9F F1 5E 9F 91 25 4D DE 22 F1 EE D6 C4
       :     3F A4 74 B8 42 B1 69 56 AA 31 9E F5 79 DD D2 3B
       :     53 8B C2 AD 23 F0 69 0A 63 F2 BF CE 5D 8D C3 37
       :   }

*)
