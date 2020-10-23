module RIoT.X509.AliasKeyTBS

open ASN1.Spec
open ASN1.Low
open X509
open RIoT.X509.AliasKeyTBS.Issuer
open RIoT.X509.AliasKeyTBS.Subject
open RIoT.X509.AliasKeyTBS.Extensions
open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 512 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

let aliasKeyTBS_payload_t' = (
(*
//  *       version         [0]  EXPLICIT Version DEFAULT v1,
//  *)
  x509_version_t `tuple2`
(*
//  *       serialNumber         CertificateSerialNumber,
//  *)
  x509_serialNumber_t `tuple2`
(*
//  *       signature            AlgorithmIdentifier,
//  *)
  algorithmIdentifier_t `tuple2`
(*
//  *       issuer               Name,
//  *)
  aliasKeyTBS_issuer_t `tuple2`
(*
//  *       validity             Validity,
//  *)
  x509_validity_t `tuple2`
(*
//  *       subject              Name,
//  *)
  aliasKeyTBS_subject_t `tuple2`
(*
//  *      subjectPublicKeyInfo SubjectPublicKeyInfo
//  *)
  subjectPublicKeyInfo_t `tuple2`
(*
//  *      extensions      [3]  EXPLICIT Extensions OPTIONAL
//  *)
  x509_extensions_t_inbound serialize_aliasKeyTBS_extensions
)

let synth_aliasKeyTBS_payload_t
  (x': aliasKeyTBS_payload_t')
: GTot (aliasKeyTBS_payload_t)
= { aliasKeyTBS_version      = fst (fst (fst (fst (fst (fst (fst x'))))));
    aliasKeyTBS_serialNumber = snd (fst (fst (fst (fst (fst (fst x'))))));
    aliasKeyTBS_signatureAlg = snd (fst (fst (fst (fst (fst x')))));
    aliasKeyTBS_issuer       = snd (fst (fst (fst (fst x'))));
    aliasKeyTBS_validity     = snd (fst (fst (fst x')));
    aliasKeyTBS_subject      = snd (fst (fst x'));
    aliasKeyTBS_aliasKey_pub = snd (fst x');
    aliasKeyTBS_extensions   = snd x' }

let synth_aliasKeyTBS_payload_t'
  (x: aliasKeyTBS_payload_t)
: Tot (x': aliasKeyTBS_payload_t' { x == synth_aliasKeyTBS_payload_t x' })
= ((((((x.aliasKeyTBS_version,
        x.aliasKeyTBS_serialNumber),
        x.aliasKeyTBS_signatureAlg),
        x.aliasKeyTBS_issuer),
        x.aliasKeyTBS_validity),
        x.aliasKeyTBS_subject),
        x.aliasKeyTBS_aliasKey_pub),
        x.aliasKeyTBS_extensions

let parse_aliasKeyTBS_payload
= parse_x509_version
  `nondep_then`
  parse_x509_serialNumber
  `nondep_then`
  parse_algorithmIdentifier
  `nondep_then`
  parse_aliasKeyTBS_issuer
  `nondep_then`
  parse_x509_validity
  `nondep_then`
  parse_aliasKeyTBS_subject
  `nondep_then`
  parse_subjectPublicKeyInfo
  `nondep_then`
  parse_x509_extensions_TLV serialize_aliasKeyTBS_extensions
  `parse_synth`
  synth_aliasKeyTBS_payload_t

let serialize_aliasKeyTBS_payload
=
  serialize_synth
  (* p1 *) (parse_x509_version
            `nondep_then`
            parse_x509_serialNumber
            `nondep_then`
            parse_algorithmIdentifier
            `nondep_then`
            parse_aliasKeyTBS_issuer
            `nondep_then`
            parse_x509_validity
            `nondep_then`
            parse_aliasKeyTBS_subject
            `nondep_then`
            parse_subjectPublicKeyInfo
            `nondep_then`
            parse_x509_extensions_TLV serialize_aliasKeyTBS_extensions)
  (* f2 *) (synth_aliasKeyTBS_payload_t)
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_x509_serialNumber
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_aliasKeyTBS_issuer
            `serialize_nondep_then`
            serialize_x509_validity
            `serialize_nondep_then`
            serialize_aliasKeyTBS_subject
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo
            `serialize_nondep_then`
            serialize_x509_extensions_TLV serialize_aliasKeyTBS_extensions
            `coerce_parser_serializer _`
            ())
  (* g1 *) (synth_aliasKeyTBS_payload_t')
  (* prf*) ()

let lemma_serialize_aliasKeyTBS_payload_unfold x
= serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version)
  (* s2 *) (serialize_x509_serialNumber)
  (* in *) (fst (fst (fst(fst (fst (fst (synth_aliasKeyTBS_payload_t' x)))))));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_x509_serialNumber)
  (* s2 *) (serialize_algorithmIdentifier)
  (* in *) (fst (fst(fst (fst (fst (synth_aliasKeyTBS_payload_t' x))))));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_x509_serialNumber
            `serialize_nondep_then`
            serialize_algorithmIdentifier)
  (* s2 *) (serialize_aliasKeyTBS_issuer)
  (* in *) (fst (fst (fst (fst (synth_aliasKeyTBS_payload_t' x)))));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_x509_serialNumber
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_aliasKeyTBS_issuer)
  (* s2 *) (serialize_x509_validity)
  (* in *) (fst (fst (fst (synth_aliasKeyTBS_payload_t' x))));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_x509_serialNumber
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_aliasKeyTBS_issuer
            `serialize_nondep_then`
            serialize_x509_validity)
  (* s2 *) (serialize_aliasKeyTBS_subject)
  (* in *) (fst (fst (synth_aliasKeyTBS_payload_t' x)));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_x509_serialNumber
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_aliasKeyTBS_issuer
            `serialize_nondep_then`
            serialize_x509_validity
            `serialize_nondep_then`
            serialize_aliasKeyTBS_subject)
  (* s2 *) (serialize_subjectPublicKeyInfo)
  (* in *) (fst (synth_aliasKeyTBS_payload_t' x));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_x509_serialNumber
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_aliasKeyTBS_issuer
            `serialize_nondep_then`
            serialize_x509_validity
            `serialize_nondep_then`
            serialize_aliasKeyTBS_subject
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo)
  (* s2 *) (serialize_x509_extensions_TLV serialize_aliasKeyTBS_extensions)
  (* in *) (synth_aliasKeyTBS_payload_t' x);

  serialize_synth_eq
  (* p1 *) (parse_x509_version
            `nondep_then`
            parse_x509_serialNumber
            `nondep_then`
            parse_algorithmIdentifier
            `nondep_then`
            parse_aliasKeyTBS_issuer
            `nondep_then`
            parse_x509_validity
            `nondep_then`
            parse_aliasKeyTBS_subject
            `nondep_then`
            parse_subjectPublicKeyInfo
            `nondep_then`
            parse_x509_extensions_TLV serialize_aliasKeyTBS_extensions)
  (* f2 *) (synth_aliasKeyTBS_payload_t)
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_x509_serialNumber
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_aliasKeyTBS_issuer
            `serialize_nondep_then`
            serialize_x509_validity
            `serialize_nondep_then`
            serialize_aliasKeyTBS_subject
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo
            `serialize_nondep_then`
            serialize_x509_extensions_TLV serialize_aliasKeyTBS_extensions
            `coerce_parser_serializer _`
            ())
  (* g1 *) (synth_aliasKeyTBS_payload_t')
  (* prf*) ()
  (* in *) (x)

#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection -LowParse'"
let lemma_serialize_aliasKeyTBS_payload_size x
= lemma_serialize_aliasKeyTBS_payload_unfold x;
  Seq.lemma_len_append
    (serialize_x509_version `serialize` x.aliasKeyTBS_version)
    (serialize_x509_serialNumber `serialize` x.aliasKeyTBS_serialNumber);
  Seq.lemma_len_append
    ((serialize_x509_version `serialize` x.aliasKeyTBS_version)
      `Seq.append`
     (serialize_x509_serialNumber `serialize` x.aliasKeyTBS_serialNumber))
    (serialize_algorithmIdentifier `serialize` x.aliasKeyTBS_signatureAlg);
  Seq.lemma_len_append
    ((serialize_x509_version `serialize` x.aliasKeyTBS_version)
      `Seq.append`
     (serialize_x509_serialNumber `serialize` x.aliasKeyTBS_serialNumber)
      `Seq.append`
     (serialize_algorithmIdentifier `serialize` x.aliasKeyTBS_signatureAlg))
    (serialize_aliasKeyTBS_issuer `serialize` x.aliasKeyTBS_issuer);
  Seq.lemma_len_append
    ((serialize_x509_version `serialize` x.aliasKeyTBS_version)
      `Seq.append`
     (serialize_x509_serialNumber `serialize` x.aliasKeyTBS_serialNumber)
      `Seq.append`
     (serialize_algorithmIdentifier `serialize` x.aliasKeyTBS_signatureAlg)
      `Seq.append`
     (serialize_aliasKeyTBS_issuer `serialize` x.aliasKeyTBS_issuer))
    (serialize_x509_validity `serialize` x.aliasKeyTBS_validity);
   Seq.lemma_len_append
     ((serialize_x509_version `serialize` x.aliasKeyTBS_version)
       `Seq.append`
      (serialize_x509_serialNumber `serialize` x.aliasKeyTBS_serialNumber)
       `Seq.append`
      (serialize_algorithmIdentifier `serialize` x.aliasKeyTBS_signatureAlg)
       `Seq.append`
      (serialize_aliasKeyTBS_issuer `serialize` x.aliasKeyTBS_issuer)
       `Seq.append`
      (serialize_x509_validity `serialize` x.aliasKeyTBS_validity))
     (serialize_aliasKeyTBS_subject `serialize` x.aliasKeyTBS_subject);
   Seq.lemma_len_append
      ((serialize_x509_version `serialize` x.aliasKeyTBS_version)
        `Seq.append`
       (serialize_x509_serialNumber `serialize` x.aliasKeyTBS_serialNumber)
        `Seq.append`
       (serialize_algorithmIdentifier `serialize` x.aliasKeyTBS_signatureAlg)
        `Seq.append`
       (serialize_aliasKeyTBS_issuer `serialize` x.aliasKeyTBS_issuer)
        `Seq.append`
       (serialize_x509_validity `serialize` x.aliasKeyTBS_validity)
        `Seq.append`
       (serialize_aliasKeyTBS_subject `serialize` x.aliasKeyTBS_subject))
      (serialize_subjectPublicKeyInfo `serialize` x.aliasKeyTBS_aliasKey_pub);
   Seq.lemma_len_append
      ((serialize_x509_version `serialize` x.aliasKeyTBS_version)
        `Seq.append`
       (serialize_x509_serialNumber `serialize` x.aliasKeyTBS_serialNumber)
        `Seq.append`
       (serialize_algorithmIdentifier `serialize` x.aliasKeyTBS_signatureAlg)
        `Seq.append`
       (serialize_aliasKeyTBS_issuer `serialize` x.aliasKeyTBS_issuer)
        `Seq.append`
       (serialize_x509_validity `serialize` x.aliasKeyTBS_validity)
        `Seq.append`
       (serialize_aliasKeyTBS_subject `serialize` x.aliasKeyTBS_subject)
        `Seq.append`
       (serialize_subjectPublicKeyInfo `serialize` x.aliasKeyTBS_aliasKey_pub))
      (serialize_x509_extensions_TLV serialize_aliasKeyTBS_extensions `serialize` x.aliasKeyTBS_extensions);
    lemma_serialize_x509_version_size_exact x.aliasKeyTBS_version;
    lemma_serialize_x509_serialNumber_size x.aliasKeyTBS_serialNumber;
    lemma_serialize_algorithmIdentifier_size_exact x.aliasKeyTBS_signatureAlg;
    lemma_serialize_aliasKeyTBS_issuer_size_exact x.aliasKeyTBS_issuer;
    lemma_serialize_x509_validity_size_exact x.aliasKeyTBS_validity;
    lemma_serialize_aliasKeyTBS_subject_size_exact x.aliasKeyTBS_subject;
    lemma_serialize_subjectPublicKeyInfo_size_exact x.aliasKeyTBS_aliasKey_pub;
    lemma_serialize_x509_extensions_TLV_size serialize_aliasKeyTBS_extensions x.aliasKeyTBS_extensions;
      lemma_serialize_aliasKeyTBS_extensions_size_exact x.aliasKeyTBS_extensions

let lemma_serialize_aliasKeyTBS_unfold x
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_aliasKeyTBS_payload) x

let lemma_serialize_aliasKeyTBS_size x
= lemma_serialize_asn1_sequence_TLV_size (serialize_aliasKeyTBS_payload) x

let lemma_serialize_aliasKeyTBS_size_exact x
=
  // lemma_aliasKeyTBS_ingredients_valid
  //         x.aliasKeyTBS_serialNumber
  //         (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Common)
  //         (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Organization)
  //         (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Country)
  //         (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Common)
  //         (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Organization)
  //         (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Country)
  //         RIoT.X509.Extension.(x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version);
  lemma_serialize_aliasKeyTBS_size x;
    lemma_serialize_aliasKeyTBS_payload_size x
#pop-options

(* low *)
let serialize32_aliasKeyTBS_payload_backwards
= serialize32_synth_backwards
  (* s1 *) (serialize32_x509_version_backwards
            `serialize32_nondep_then_backwards`
            serialize32_x509_serialNumber_backwards
            `serialize32_nondep_then_backwards`
            serialize32_algorithmIdentifier_backwards
            `serialize32_nondep_then_backwards`
            serialize32_aliasKeyTBS_issuer_backwards
            `serialize32_nondep_then_backwards`
            serialize32_x509_validity_backwards
            `serialize32_nondep_then_backwards`
            serialize32_aliasKeyTBS_subject_backwards
            `serialize32_nondep_then_backwards`
            serialize32_subjectPublicKeyInfo_backwards
            `serialize32_nondep_then_backwards`
            serialize32_x509_extensions_TLV_backwards serialize32_aliasKeyTBS_extensions_backwards)
  (* f2 *) (synth_aliasKeyTBS_payload_t)
  (* g1 *) (synth_aliasKeyTBS_payload_t')
  (* g1'*) (synth_aliasKeyTBS_payload_t')
  (* prf*) ()
  `coerce_serializer32_backwards serialize_aliasKeyTBS_payload`
  ()

let serialize32_aliasKeyTBS_backwards
= coerce_serializer32_backwards
  (* s2 *) (serialize_aliasKeyTBS)
  (* s32*) (serialize32_asn1_sequence_TLV_backwards
             (serialize32_aliasKeyTBS_payload_backwards))
  (* prf*) ()

let () = ()
