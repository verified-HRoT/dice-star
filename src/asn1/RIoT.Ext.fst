module RIoT.Ext

open LowParse.Low.Base
open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

open FStar.Integers

noeq
type algorithmIdentifier_t = {
  algorithm_oid: datatype_of_asn1_type OCTET_STRING; (* OID *)
  parameters   : datatype_of_asn1_type OCTET_STRING  (* ANY *)
}
let algorithmIdentifier_t' = (datatype_of_asn1_type OCTET_STRING & datatype_of_asn1_type OCTET_STRING)

let synth_algorithmIdentifier_t
  (x': algorithmIdentifier_t')
: GTot (algorithmIdentifier_t)
= { algorithm_oid = fst x';
    parameters    = snd x' }

let synth_algorithmIdentifier_t'
  (x: algorithmIdentifier_t)
: Tot (x': algorithmIdentifier_t' { x == synth_algorithmIdentifier_t x' })
= (x.algorithm_oid, x.parameters)

let parse_algorithmIdentifier_value
: parser _ algorithmIdentifier_t
= parse_asn1_TLV_of_type OCTET_STRING
  `nondep_then`
  parse_asn1_TLV_of_type OCTET_STRING
  `parse_synth`
  synth_algorithmIdentifier_t

let serialize_algorithmIdentifier_value
: serializer parse_algorithmIdentifier_value
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type OCTET_STRING
            `nondep_then`
            parse_asn1_TLV_of_type OCTET_STRING)
  (* f2 *) (synth_algorithmIdentifier_t)
  (* s1 *) (serialize_asn1_TLV_of_type OCTET_STRING
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type OCTET_STRING)
  (* g1 *) (synth_algorithmIdentifier_t')
  (* prf*) ()

let x2: datatype_of_asn1_type NULL = ()

let serialize_algorithmIdentifier_value_unfold
  (x: algorithmIdentifier_t)
: Lemma (
  serialize serialize_algorithmIdentifier_value x ==
  serialize (serialize_asn1_TLV_of_type OCTET_STRING) x.algorithm_oid
  `Seq.append`
  serialize (serialize_asn1_TLV_of_type OCTET_STRING) x.parameters
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type OCTET_STRING)
  (* s2 *) (serialize_asn1_TLV_of_type OCTET_STRING)
  (* in *) (synth_algorithmIdentifier_t' x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type OCTET_STRING
            `nondep_then`
            parse_asn1_TLV_of_type OCTET_STRING)
  (* f2 *) (synth_algorithmIdentifier_t)
  (* s1 *) (serialize_asn1_TLV_of_type OCTET_STRING
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type OCTET_STRING)
  (* g1 *) (synth_algorithmIdentifier_t')
  (* prf*) ()
  (* in *) x

(* NOTE: Define the `inbound` version of value type after we defined then serializer. *)
let algorithmIdentifier_t_inbound
= inbound_sequence_value_of serialize_algorithmIdentifier_value

/// TLV
///
let parse_algorithmIdentifier_sequence_TLV
: parser _ algorithmIdentifier_t_inbound
= parse_asn1_sequence_TLV serialize_algorithmIdentifier_value

let serialize_algorithmIdentifier_sequence_TLV
: serializer parse_algorithmIdentifier_sequence_TLV
= serialize_asn1_sequence_TLV serialize_algorithmIdentifier_value

let serialize_algorithmIdentifier_sequence_TLV_unfold
= serialize_asn1_sequence_TLV_unfold serialize_algorithmIdentifier_value

let serialize_algorithmIdentifier_sequence_TLV_size
= serialize_asn1_sequence_TLV_size serialize_algorithmIdentifier_value

/// Low
///
#push-options "--query_stats --z3rlimit 32"
let len_of_algorithmIdentifier_value_inbound
  (x: algorithmIdentifier_t_inbound)
: Tot (inbound_sequence_value_len_of serialize_algorithmIdentifier_value x)
= serialize_algorithmIdentifier_value_unfold x;
  len_of_asn1_primitive_TLV x.algorithm_oid +
  len_of_asn1_primitive_TLV x.parameters

let len_of_algorithmIdentifier_TLV_inbound
  (x: algorithmIdentifier_t_inbound)
(* FIXME: F* stuck here if I un-comment the following line. *)
// : Tot (inbound_sequence_value_len_of serialize_algorithmIdentifier_sequence_TLV x)
= len_of_sequence_TLV
  (* s *) serialize_algorithmIdentifier_value
  (*len*) len_of_algorithmIdentifier_value_inbound
  (*val*) x
#pop-options

let serialize32_algorithmIdentifier_value_backwards
: serializer32_backwards serialize_algorithmIdentifier_value
= serialize32_synth_backwards
  (* ls *) (serialize32_asn1_TLV_backwards_of_type OCTET_STRING
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type OCTET_STRING)
  (* f2 *) (synth_algorithmIdentifier_t)
  (* g1 *) (synth_algorithmIdentifier_t')
  (* g1'*) (synth_algorithmIdentifier_t')
  (* prf*) ()

let serialize32_algorithmIdentifier_sequence_backwards
= serialize32_asn1_sequence_TLV_backwards
  (* ls *) (serialize32_algorithmIdentifier_value_backwards)
  (*flen*) (len_of_algorithmIdentifier_value_inbound)

/////////////////////////////////
noeq
type subjectPublicKeyInfo_t = {
  algorithm       : algorithmIdentifier_t_inbound;
  subjectPublicKey: datatype_of_asn1_type BIT_STRING  (* BIT STRING *)
}

let subjectPublicKeyInfo_t' = (algorithmIdentifier_t_inbound & datatype_of_asn1_type BIT_STRING)

(* NOTE: Define serializer spec *)
let synth_subjectPublicKeyInfo_t
  (x': subjectPublicKeyInfo_t')
: GTot (subjectPublicKeyInfo_t)
= { algorithm        = fst x';
    subjectPublicKey = snd x' }

let synth_subjectPublicKeyInfo_t'
  (x: subjectPublicKeyInfo_t)
: Tot (x': subjectPublicKeyInfo_t' { x == synth_subjectPublicKeyInfo_t x' })
= (x.algorithm, x.subjectPublicKey)

#push-options "--query_stats"
let parse_subjectPublicKeyInfo_value
: parser _ subjectPublicKeyInfo_t
= parse_algorithmIdentifier_sequence_TLV
  `nondep_then`
  parse_asn1_TLV_of_type BIT_STRING
  `parse_synth`
  synth_subjectPublicKeyInfo_t

let serialize_subjectPublicKeyInfo_value
: serializer parse_subjectPublicKeyInfo_value
= serialize_synth
  (* p1 *) (parse_algorithmIdentifier_sequence_TLV
            `nondep_then`
            parse_asn1_TLV_of_type BIT_STRING)
  (* f2 *) (synth_subjectPublicKeyInfo_t)
  (* s1 *) (serialize_algorithmIdentifier_sequence_TLV
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BIT_STRING)
  (* g1 *) (synth_subjectPublicKeyInfo_t')
  (* prf*) ()

let serialize_subjectPublicKeyInfo_value_unfold
  (x: subjectPublicKeyInfo_t)
: Lemma (
  serialize serialize_subjectPublicKeyInfo_value x ==
  serialize serialize_algorithmIdentifier_sequence_TLV x.algorithm
  `Seq.append`
  serialize serialize_asn1_bit_string_TLV x.subjectPublicKey
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_algorithmIdentifier_sequence_TLV)
  (* s2 *) (serialize_asn1_TLV_of_type BIT_STRING)
  (* in *) (synth_subjectPublicKeyInfo_t' x);
  serialize_synth_eq
  (* p1 *) (parse_algorithmIdentifier_sequence_TLV
            `nondep_then`
            parse_asn1_TLV_of_type BIT_STRING)
  (* f2 *) (synth_subjectPublicKeyInfo_t)
  (* s1 *) (serialize_algorithmIdentifier_sequence_TLV
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BIT_STRING)
  (* g1 *) (synth_subjectPublicKeyInfo_t')
  (* prf*) ()
  (* in *) x

(* NOTE: Define inbound sub type *)
let subjectPublicKeyInfo_t_inbound
= inbound_sequence_value_of serialize_subjectPublicKeyInfo_value

/// TLV
let parse_subjectPublicKeyInfo_sequence_TLV
: parser _ subjectPublicKeyInfo_t_inbound
= parse_asn1_sequence_TLV serialize_subjectPublicKeyInfo_value

let serialize_subjectPublicKeyInfo_sequence_TLV
: serializer parse_subjectPublicKeyInfo_sequence_TLV
= serialize_asn1_sequence_TLV serialize_subjectPublicKeyInfo_value

let serialize_subjectPublicKeyInfo_sequence_TLV_unfold
= serialize_asn1_sequence_TLV_unfold serialize_subjectPublicKeyInfo_value

let serialize_subjectPublicKeyInfo_sequence_TLV_size
= serialize_asn1_sequence_TLV_size serialize_subjectPublicKeyInfo_value

/// Low
let serialize32_subjectPublicKeyInfo_value
: serializer32_backwards serialize_subjectPublicKeyInfo_value
= serialize32_synth_backwards
  (* ls *) (serialize32_algorithmIdentifier_sequence_backwards
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type BIT_STRING)
  (* f2 *) (synth_subjectPublicKeyInfo_t)
  (* g1 *) (synth_subjectPublicKeyInfo_t')
  (* g1'*) (synth_subjectPublicKeyInfo_t')
  (* prf*) ()

#push-options "--z3rlimit 64"
let len_of_subjectPublicKeyInfo_value_inbound
  (x: subjectPublicKeyInfo_t_inbound)
: Tot (inbound_sequence_value_len_of serialize_subjectPublicKeyInfo_value x)
= serialize_subjectPublicKeyInfo_value_unfold x;
  serialize_algorithmIdentifier_sequence_TLV_size x.algorithm;
  len_of_algorithmIdentifier_TLV_inbound x.algorithm +
  len_of_asn1_primitive_TLV    x.subjectPublicKey
#pop-options

let len_of_subjectPublicKeyInfo_TLV_inbound
  (x: subjectPublicKeyInfo_t_inbound)
// : Tot (inbound_sequence_value_len_of serialize_subjectPublicKeyInfo_sequence_TLV x)
= len_of_sequence_TLV
  (* s *) serialize_subjectPublicKeyInfo_value
  (*len*) len_of_subjectPublicKeyInfo_value_inbound
  (*val*) x

let serialize32_subjectPublicKeyInfo_sequence_TLV_backwards
: serializer32_backwards serialize_subjectPublicKeyInfo_sequence_TLV
= serialize32_asn1_sequence_TLV_backwards
  (* ls *) (serialize32_subjectPublicKeyInfo_value)
  (*flen*) (len_of_subjectPublicKeyInfo_value_inbound)

/////////////////////////////////
noeq
type fwid_t = {
  hashAlg: datatype_of_asn1_type OCTET_STRING; (* OID *)
  fwid   : datatype_of_asn1_type OCTET_STRING
}
let fwid_t' = (datatype_of_asn1_type OCTET_STRING & datatype_of_asn1_type OCTET_STRING)

(* Serialier spec *)
let synth_fwid_t
  (x': fwid_t')
: GTot (fwid_t)
= { hashAlg = fst x';
    fwid    = snd x' }

let synth_fwid_t'
  (x: fwid_t)
: Tot (x': fwid_t' { x == synth_fwid_t x' } )
= (x.hashAlg, x.fwid)

let parse_fwid_value
: parser _ fwid_t
= parse_asn1_TLV_of_type OCTET_STRING
  `nondep_then`
  parse_asn1_TLV_of_type OCTET_STRING
  `parse_synth`
  synth_fwid_t

let serialize_fwid_value
: serializer parse_fwid_value
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type OCTET_STRING
            `nondep_then`
            parse_asn1_TLV_of_type OCTET_STRING)
  (* f2 *) (synth_fwid_t)
  (* s1 *) (serialize_asn1_TLV_of_type OCTET_STRING
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type OCTET_STRING)
  (* g1 *) (synth_fwid_t')
  (* prf*) ()

let serialize_fwid_value_unfold
  (x: fwid_t)
: Lemma (
  serialize serialize_fwid_value x ==
  serialize serialize_asn1_octet_string_TLV x.hashAlg
  `Seq.append`
  serialize serialize_asn1_octet_string_TLV x.fwid
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type OCTET_STRING)
  (* s2 *) (serialize_asn1_TLV_of_type OCTET_STRING)
  (* in *) (synth_fwid_t' x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type OCTET_STRING
            `nondep_then`
            parse_asn1_TLV_of_type OCTET_STRING)
  (* f2 *) (synth_fwid_t)
  (* s1 *) (serialize_asn1_TLV_of_type OCTET_STRING
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type OCTET_STRING)
  (* g1 *) (synth_fwid_t')
  (* prf*) ()
  (* in *) x

(* inbound sub type*)
let fwid_t_inbound
= inbound_sequence_value_of serialize_fwid_value

(* TLV serializer *)
let parse_fwid_sequence_TLV
: parser _ fwid_t_inbound
= parse_asn1_sequence_TLV serialize_fwid_value

let serialize_fwid_sequence_TLV
: serializer parse_fwid_sequence_TLV
= serialize_asn1_sequence_TLV serialize_fwid_value

let serialize_fwid_sequence_TLV_unfold
= serialize_asn1_sequence_TLV_unfold serialize_fwid_value

let serialize_fwid_sequence_TLV_size
= serialize_asn1_sequence_TLV_size serialize_fwid_value

let serialize32_fwid_value
: serializer32_backwards serialize_fwid_value
= serialize32_synth_backwards
  (* ls *) (serialize32_asn1_TLV_backwards_of_type OCTET_STRING
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type OCTET_STRING)
  (* f2 *) (synth_fwid_t)
  (* g1 *) (synth_fwid_t')
  (* g1'*) (synth_fwid_t')
  (* prf*) ()

#push-options "--z3rlimit 32"
let len_of_fwid_value_inbound
  (x: fwid_t_inbound)
: Tot (inbound_sequence_value_len_of serialize_fwid_value x)
= serialize_fwid_value_unfold x;
  len_of_asn1_primitive_TLV x.hashAlg +
  len_of_asn1_primitive_TLV x.fwid
#pop-options

let len_of_fwid_TLV_inbound
  (x: fwid_t_inbound)
// : Tot (inbound_sequence_value_len_of serialize_fwid_sequence_TLV x)
= len_of_sequence_TLV
  (* s *) serialize_fwid_value
  (*len*) len_of_fwid_value_inbound
  (*val*) x

let serialize32_fwid_sequence
: serializer32_backwards serialize_fwid_sequence_TLV
= serialize32_asn1_sequence_TLV_backwards
  (* ls *) (serialize32_fwid_value)
  (*flen*) (len_of_fwid_value_inbound)

//////////////////////////////////
noeq
type compositeDeviceID_t = {
  version : datatype_of_asn1_type INTEGER; (* INTEGER (1) *)
  deviceID: subjectPublicKeyInfo_t_inbound;
  fwid    : fwid_t_inbound
}
let compositeDeviceID_t' = ((datatype_of_asn1_type INTEGER & subjectPublicKeyInfo_t_inbound) & fwid_t_inbound)

let synth_compositeDeviceID_t
  (x': compositeDeviceID_t')
: GTot (compositeDeviceID_t)
= { version  = fst (fst x');
    deviceID = snd (fst x');
    fwid     = snd x' }

let synth_compositeDeviceID_t'
  (x: compositeDeviceID_t)
: Tot (x': compositeDeviceID_t' { x == synth_compositeDeviceID_t x' })
= ((x.version, x.deviceID), x.fwid)

let parse_compositeDeviceID_value
: parser _ compositeDeviceID_t
=(parse_asn1_TLV_of_type INTEGER
  `nondep_then`
  parse_subjectPublicKeyInfo_sequence_TLV)
  `nondep_then`
  parse_fwid_sequence_TLV
  `parse_synth`
  synth_compositeDeviceID_t

let serialize_compositeDeviceID_value
: serializer parse_compositeDeviceID_value
= serialize_synth
  (* p1 *) ((parse_asn1_TLV_of_type INTEGER
             `nondep_then`
             parse_subjectPublicKeyInfo_sequence_TLV)
             `nondep_then`
             parse_fwid_sequence_TLV)
  (* f2 *) (synth_compositeDeviceID_t)
  (* s1 *) ((serialize_asn1_TLV_of_type INTEGER
             `serialize_nondep_then`
             serialize_subjectPublicKeyInfo_sequence_TLV)
             `serialize_nondep_then`
             serialize_fwid_sequence_TLV)
  (* g1 *) (synth_compositeDeviceID_t')
  (* prf*) ()

let serialize_compositeDeviceID_value_unfold
  (x: compositeDeviceID_t)
: Lemma (
  serialize serialize_compositeDeviceID_value x ==
  serialize (serialize_asn1_TLV_of_type INTEGER) x.version
  `Seq.append`
  serialize serialize_subjectPublicKeyInfo_sequence_TLV x.deviceID
  `Seq.append`
  serialize serialize_fwid_sequence_TLV x.fwid
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER)
  (* s2 *) (serialize_subjectPublicKeyInfo_sequence_TLV)
  (* in *) (fst (synth_compositeDeviceID_t' x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo_sequence_TLV)
  (* s2 *) (serialize_fwid_sequence_TLV)
  (* in *) (synth_compositeDeviceID_t' x);
  serialize_synth_eq
  (* p1 *) ((parse_asn1_TLV_of_type INTEGER
             `nondep_then`
             parse_subjectPublicKeyInfo_sequence_TLV)
             `nondep_then`
             parse_fwid_sequence_TLV)
  (* f2 *) (synth_compositeDeviceID_t)
  (* s1 *) ((serialize_asn1_TLV_of_type INTEGER
             `serialize_nondep_then`
             serialize_subjectPublicKeyInfo_sequence_TLV)
             `serialize_nondep_then`
             serialize_fwid_sequence_TLV)
  (* g1 *) (synth_compositeDeviceID_t')
  (* prf*) ()
  (* in  *) x

(* inbound sub type *)
let compositeDeviceID_t_inbound
= inbound_sequence_value_of serialize_compositeDeviceID_value

(*)
(* TLV *)
(* FIXME: F* stuck here. *)
let parse_compositeDeviceID_sequence_TLV
: parser _ compositeDeviceID_t_inbound
= parse_asn1_sequence_TLV serialize_compositeDeviceID_value

let serialize_compositeDeviceID_sequence_TLV
: serializer parse_compositeDeviceID_sequence_TLV
= serialize_asn1_sequence_TLV serialize_compositeDeviceID_value

let serialize32_compositeDeviceID_value
: serializer32_backwards serialize_compositeDeviceID_value
= serialize32_synth_backwards
  (* ls1*) ((serialize32_asn1_TLV_backwards_of_type OCTET_STRING
             `serialize32_nondep_then_backwards`
             serialize32_subjectPublicKeyInfo_sequence)
             `serialize32_nondep_then_backwards`
             serialize32_fwid_sequence)
  (* f2 *) (synth_compositeDeviceID_t)
  (* g1 *) (synth_compositeDeviceID_t')
  (* g1'*) (synth_compositeDeviceID_t')
  (* prf*) ()

let len_of_compositeDeviceID_t_inbound
  (x: compositeDeviceID_t_inbound)
: Tot (inbound_sequence_value_len_of serialize_compositeDeviceID_value x)
= admit()

let serialize32_compositeDeviceID_sequence
: serializer32_backwards serialize_compositeDeviceID_sequence
= serialize32_asn1_sequence_TLV_backwards
  (* ls *) (serialize32_compositeDeviceID_value)
  (*flen*) (len_of_compositeDeviceID_t_inbound)

/////////////////////////////////////
noeq
type ext_t = {
  riot_oid         : datatype_of_asn1_type OCTET_STRING;
  (* NOTE: ENVELOPING OCTETSTRING? *)
  compositeDeviceID: compositeDeviceID_t_inbound;
}
let ext_t' = (datatype_of_asn1_type OCTET_STRING & compositeDeviceID_t_inbound)

let synth_ext_t
  (x': ext_t')
: GTot (x: ext_t)
= { riot_oid          = fst x';
    compositeDeviceID = snd x' }

let synth_ext_t'
  (x: ext_t)
: Tot (x': ext_t' { x == synth_ext_t x' })
= (x.riot_oid, x.compositeDeviceID)

let parse_ext_value
: parser _ ext_t
= parse_asn1_TLV_of_type OCTET_STRING
  `nondep_then`
  parse_compositeDeviceID_sequence
  `parse_synth`
  synth_ext_t

let serialize_ext_value
: serializer parse_ext_value
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type OCTET_STRING
            `nondep_then`
            parse_compositeDeviceID_sequence)
  (* f2 *) (synth_ext_t)
  (* s1 *) (serialize_asn1_TLV_of_type OCTET_STRING
            `serialize_nondep_then`
            serialize_compositeDeviceID_sequence)
  (* g1 *) (synth_ext_t')
  (* prf*) ()

let ext_t_inbound
= inbound_sequence_value_of serialize_ext_value

let parse_ext_sequence
: parser _ ext_t_inbound
= parse_asn1_sequence_TLV serialize_ext_value

let serialize_ext_sequence
: serializer parse_ext_sequence
= serialize_asn1_sequence_TLV serialize_ext_value

let serialize32_ext_value
: serializer32_backwards serialize_ext_value
= serialize32_synth_backwards
  (* s1 *) (serialize32_asn1_TLV_backwards_of_type OCTET_STRING
            `serialize32_nondep_then_backwards`
            serialize32_compositeDeviceID_sequence)
  (* f2 *) (synth_ext_t)
  (* g1 *) (synth_ext_t')
  (* g1'*) (synth_ext_t')
  (* prf*) ()

let len_of_ext_t_inbound
  (x: ext_t_inbound)
: Tot (inbound_sequence_value_len_of serialize_ext_value x)
= admit()

let serialize32_ext_sequence
: serializer32_backwards serialize_ext_sequence
= serialize32_asn1_sequence_TLV_backwards
  (* ls *) (serialize32_ext_value)
  (*flen*) (len_of_ext_t_inbound)
