module RIoTCore

open FStar.Buffer
open FStar.UInt32

module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U32 = FStar.UInt32
module U8  = FStar.UInt8

let uint32 = U32.t
let uint8 = U8.t

// TODO: Date Types
// TODO: Modules

// NOTE: Getting familiar with F* and DICE/RIoT by simply re-implement reference code (https://github.com/microsoft/RIoT/blob/master/Reference/RIoT/Core/RIoT.cpp) in F*.

(*digest lengths*)
assume val _SHA256_DIGEST_LENGTH : U32.t
assume val _RIOT_DIGEST_LENGTH : uint32

assume val _RIOT_LABEL_IDENTITY : uint32
assume val _RIOT_LABEL_IDENTITY_SIZE : uint32

assume val _fwImage : uint32
assume val _fwSize : uint32

effect ST
  (a:Type)
  (pre :HS.mem -> Type0)
  (post:HS.mem -> a -> HS.mem -> Type0)
= FStar.HyperStack.ST.ST a pre post

effect St (a:Type) = FStar.HyperStack.ST.St a

val _DICEStart (something:unit) : ST unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)
let _DICEStart () = ()
let a = _DICEStart ()
(*
let _RiotStart (_CDI:string) (_CDILen:nat) =
  // DONE: Get CDI Digest
  // REF: RiotCrypt_Hash(cDigest, RIOT_DIGEST_LENGTH, CDI, CDILen);
  // NOTE: pointer in F*?
  let cDigest = (_RiotCrypt_Hash _RIOT_DIGEST_LENGTH
                                 _CDI // <--
                                 _CDILen) in

  // DONE: Derive DeviceID Key pair
  // REF: RiotCrypt_DeriveEccKey(&DeviceIDPub,
  //                             &deviceIDPriv,
  //                             cDigest, RIOT_DIGEST_LENGTH,
  //                             (const uint8_t * )RIOT_LABEL_IDENTITY,
  //                             lblSize(RIOT_LABEL_IDENTITY));
  // NOTE: F* represents a record (inductive type) in a form of product type?
  let (_DeviceIDPub, _DeviceIDPriv) =
                     (_RiotCrypt_DeriveEccKey cDigest // <--
                                              _RIOT_DIGEST_LENGTH
                                              _RIOT_LABEL_IDENTITY
                                              _RIOT_LABEL_IDENTITY_SIZE) in

  // TODO: Set the serial number for DeviceID certificate
  // REF: RiotSetSerialNumber(&x509DeviceTBSData, cDigest, RIOT_DIGEST_LENGTH);

  // TODO: Output Device Identity Key pair
  // REF:

  // TODO: Locate firmware image
  // REF: fwDLL = LoadLibrary(FWImagePath);
  //      if (fwDLL == NULL) {
  //          printf("RIOT: ERROR: Failed to load firmware image.\n");
  //          return;
  //      }

  // TODO: Locate entry point for FW
  // REF: FirmwareEntry = (fpFirmwareEntry)GetProcAddress(fwDLL, FIRMWARE_ENTRY);
  //      if (!FirmwareEntry) {
  //          printf("RIOT: ERROR: Failed to locate fw start\n");
  //          return;
  //      }

  // TODO: Get base offset and size of FW image
  // REF: if (!RiotGetFWInfo(fwDLL, &offset, &fwSize)) {
  //          fprintf(stderr, "FW: Failed to locate FW code\n");
  //          return;
  //      }

  // TODO: Calculate base VA of FW code
  // REF: fwImage = (BYTE *)((uint64_t)fwDLL + offset);

  // DONE: Measure FW, i.e., calculate FWID
  // REF: RiotCrypt_Hash(FWID, RIOT_DIGEST_LENGTH, fwImage, fwSize);
  let _FWID = (_RiotCrypt_Hash _RIOT_DIGEST_LENGTH
                               _fwImage // <--
                               _fwSize) in

  // DONE: Combine CDI and FWID, result in cDigest
  // REF: RiotCrypt_Hash2(cDigest, RIOT_DIGEST_LENGTH,
  //       cDigest, RIOT_DIGEST_LENGTH,
  //       FWID,    RIOT_DIGEST_LENGTH);
  let cDigest = (_RiotCrypt_Hash2 _RIOT_DIGEST_LENGTH
                                  cDigest // <--
                                  _RIOT_DIGEST_LENGTH
                                  _FWID // <--
                                  _RIOT_DIGEST_LENGTH) in

  // DONE: Derive Alias key pair from CDI and FWID
  // REF: RiotCrypt_DeriveEccKey(&AliasKeyPub,
  //                             &AliasKeyPriv,
  //                             cDigest, RIOT_DIGEST_LENGTH,
  //                             (const uint8_t *)RIOT_LABEL_ALIAS,
  //                             lblSize(RIOT_LABEL_ALIAS));
  let (_AliasKeyPub, _AliasKeyPriv) = (_RiotCrypt_DeriveEccKey cDigest // <--
                                                               _RIOT_DIGEST_LENGTH
                                                               _RIOT_LABEL_IDENTITY
                                                               _RIOT_LABEL_IDENTITY_SIZE) in

  // TODO: With the Alias Key pair derived, we can now Seed DRBG
  // REF: RiotCrypt_SeedDRBG((uint8_t*)&AliasKeyPriv, sizeof(RIOT_ECC_PRIVATE));
  // NOTE: DRBG for Deterministic Random Bit Generator?

  // TODO: Set the serial number
  // REF: RiotSetSerialNumber(&x509AliasTBSData, cDigest, RIOT_DIGEST_LENGTH);

  // TODO: Clean up potentially sensative data
  // REF: memset(cDigest, 0x00, RIOT_DIGEST_LENGTH);
  // NOTE: Does F* supports memory operation?

  // TODO: Build the TBS (to be signed) region of Alias Key Certificate
  // REF: DERInitContext(&derCtx, derBuffer, DER_MAX_TBS);
  //      X509GetAliasCertTBS(&derCtx, &x509AliasTBSData,
  //                          &AliasKeyPub, &DeviceIDPub,
  //                          FWID, RIOT_DIGEST_LENGTH);

  // TODO: Sign the Alias Key Certificate's TBS region
  // REF: RiotCrypt_Sign(&tbsSig, derCtx.Buffer, derCtx.Position, &deviceIDPriv);
  //let tbsSig = (_RiotCrypt_Sign derCtx.Buffer
  //                              derCtx.Position
  //                              deviceIDPriv) in

  // TODO: Generate Alias Key Certificate
  // REF: X509MakeAliasCert(&derCtx, &tbsSig);

  // TODO: Copy Alias Key Certificate
  // REF: length = sizeof(AliasCert);
  //      DERtoPEM(&derCtx, CERT_TYPE, AliasCert, &length);
  //      AliasCert[length] = '\0';

false
*)
