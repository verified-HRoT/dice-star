module X509.Crypto.BigInteger

open ASN1.Spec.Base
open LowParse.Spec.SeqBytes.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers

module B32 = FStar.Bytes

unfold
let big_integer_as_octet_string_t
= x: datatype_of_asn1_type OCTET_STRING
  { let (.[]) = B32.index in
    v (dfst x) > 0 /\                      // no nil
    ( if (v (dfst x) > 1) then
      ( B32.index (dsnd x) 0 =!= 0x00uy )  // no leading zero byte if length > 1
      else ( True ) ) /\
    ( if ((dsnd x).[0] >= 0x80uy) then   // leave one space for leading zero byte
      ( v (dfst x) <= asn1_length_max - 7 )
      else ( True ) ) }

let asn1_value_length_of_big_integer
= l: asn1_length_t { 0 < l /\ l <= asn1_length_max - 6}

let asn1_value_int32_of_big_integer
= LowParse.Spec.BoundedInt.bounded_int32 1 (asn1_length_max - 6)

unfold
let valid_big_integer_as_octet_string_prop
  (l: asn1_value_length_of_big_integer)
  (x: big_integer_as_octet_string_t)
: Type0
= v (dfst x) > 0 /\
  ( let (.[]) = B32.index in
    if l = 1 then
    ( v (dfst x) == l /\ (dsnd x).[0] < 0x80uy )
    else if ((dsnd x).[0] >= 0x80uy) then
    ( v (dfst x) == l - 1 )
    else
    ( v (dfst x) == l /\ (dsnd x).[0] > 0x00uy ) )

///
let filter_big_integer_as_octet_string
  (l: asn1_value_length_of_big_integer)
  (s: lbytes l)
: GTot bool
= l > 0 &&
  ( if (l = 1) then
    ( s.[0] < 0x80uy )
    else if (s.[0] = 0x00uy) then
    ( s.[1] >= 0x80uy )
    else
    ( s.[0] < 0x80uy ) )

#push-options "--query_stats"
noextract
let synth_big_integer_as_octet_string
  (l: asn1_value_length_of_big_integer)
  (s: parse_filter_refine (filter_big_integer_as_octet_string l))
: GTot (value: big_integer_as_octet_string_t
               { valid_big_integer_as_octet_string_prop l value })
= if (l = 1) then
  ( (|1ul, B32.hide s|) )
  else if (s.[0] = 0x00uy) then
  ( (|u (l - 1), B32.hide (Seq.slice s 1 l)|) )
  else
  ( (|u l, B32.hide s|) )

let lemma_synth_big_integer_as_octet_string_injective'
  (l: asn1_value_length_of_big_integer)
  (s s': parse_filter_refine (filter_big_integer_as_octet_string l))
: Lemma
  (requires synth_big_integer_as_octet_string l s == synth_big_integer_as_octet_string l s')
  (ensures s == s')
= if (l = 1) then
  ( () )
  else if (s.[0] = 0x00uy) then
  ( Seq.lemma_split s  1;
    Seq.lemma_split s' 1;
    assert (s `Seq.equal` s') )
  else
  ( () )

let lemma_synth_big_integer_as_octet_string_injective
  (l: asn1_value_length_of_big_integer)
: Lemma (
  synth_injective (synth_big_integer_as_octet_string l)
)
= synth_injective_intro'
  (* f *) (synth_big_integer_as_octet_string l)
  (*prf*) (lemma_synth_big_integer_as_octet_string_injective' l)

/// Encodes our representation of a OCTET_STRING into bytes
noextract
let synth_big_integer_as_octet_string_inverse
  (l: asn1_value_length_of_big_integer)
  (value: big_integer_as_octet_string_t {valid_big_integer_as_octet_string_prop l value})
: GTot (s32: parse_filter_refine (filter_big_integer_as_octet_string l)
            { value == synth_big_integer_as_octet_string l s32 })
= let (.[]) = B32.index in
  if l = 1 then
  ( B32.reveal (dsnd value) )
  else if (dsnd value).[0] >= 0x80uy then
  ( let s = Seq.create 1 0x00uy `Seq.append` B32.reveal (dsnd value) in
    B32.extensionality (dsnd value) (B32.hide (Seq.slice s 1 l));
    s )
  else
  ( B32.reveal (dsnd value) )

// inline_for_extraction noextract
let parse_big_integer_as_octet_string_kind (l: asn1_value_length_of_big_integer) = constant_size_parser_kind l

///
/// Parser
///
noextract
let parse_big_integer_as_octet_string
  (l: asn1_value_length_of_big_integer)
: parser (parse_big_integer_as_octet_string_kind l) (x: big_integer_as_octet_string_t {valid_big_integer_as_octet_string_prop l x})
= lemma_synth_big_integer_as_octet_string_injective l;
  parse_seq_flbytes l
  `parse_filter`
  filter_big_integer_as_octet_string l
  `parse_synth`
  synth_big_integer_as_octet_string l

///
/// Serializer
///
noextract
let serialize_big_integer_as_octet_string
  (l: asn1_value_length_of_big_integer)
: serializer (parse_big_integer_as_octet_string l)
= serialize_synth
  (* p1 *) (parse_seq_flbytes l
            `parse_filter`
            filter_big_integer_as_octet_string l)
  (* f2 *) (synth_big_integer_as_octet_string l)
  (* s1 *) (serialize_seq_flbytes l
            `serialize_filter`
            filter_big_integer_as_octet_string l)
  (* g1 *) (synth_big_integer_as_octet_string_inverse l)
  (* Prf*) (lemma_synth_big_integer_as_octet_string_injective l)

///
/// Lemmas
///

/// Reveal the computation of serialize
noextract
let lemma_serialize_big_integer_as_octet_string_unfold
  (l: asn1_value_length_of_big_integer)
  (value: get_parser_type (parse_big_integer_as_octet_string l))
: Lemma (
  serialize (serialize_big_integer_as_octet_string l) value ==
  serialize (serialize_seq_flbytes l) (synth_big_integer_as_octet_string_inverse l value))
= serialize_synth_eq
  (* p1 *) (parse_seq_flbytes l
            `parse_filter`
            filter_big_integer_as_octet_string l)
  (* f2 *) (synth_big_integer_as_octet_string l)
  (* s1 *) (serialize_seq_flbytes l
            `serialize_filter`
            filter_big_integer_as_octet_string l)
  (* g1 *) (synth_big_integer_as_octet_string_inverse l)
  (* Prf*) (lemma_synth_big_integer_as_octet_string_injective l)
  (* in *) (value)

/// Reveal the length of a serialzation
noextract
let lemma_serialize_big_integer_as_octet_string_size
  (l: asn1_value_length_of_big_integer)
  (value: get_parser_type (parse_big_integer_as_octet_string l))
: Lemma (
  Seq.length (serialize (serialize_big_integer_as_octet_string l) value) == l)
= lemma_serialize_big_integer_as_octet_string_unfold l value


///////////////////////////////////////////////////////////
//// ASN1 `OCTET_STRING` TLV Parser and Serializer
///////////////////////////////////////////////////////////

/// parser tag for the `tagged_union` combinators
noextract
let parser_tag_of_big_integer_as_octet_string
  (x: big_integer_as_octet_string_t)
: GTot (the_asn1_type INTEGER & asn1_value_int32_of_big_integer)
= let (.[]) = B32.index in
  if ((dsnd x).[0] >= 0x80uy) then
  ( (INTEGER, dfst x + 1ul) )
  else
  ( (INTEGER, dfst x) )

open LowParse.Spec.DER
let parse_asn1_length_kind_of_big_integer
= parse_bounded_der_length32_kind 1 (asn1_length_max - 6)

let parse_asn1_length_of_big_integer
= parse_bounded_der_length32 1 (asn1_length_max - 6)

let serialize_asn1_length_of_big_integer
= serialize_bounded_der_length32 1 (asn1_length_max - 6)

let weak_kind_of_big_integer
= strong_parser_kind 1 (asn1_length_max - 6) None

inline_for_extraction noextract
let parse_big_integer_as_octet_string_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_big_integer
  `and_then_kind`
  weak_kind_of_big_integer

noextract
let synth_big_integer_as_octet_string_V
  (tag: (the_asn1_type INTEGER & asn1_value_int32_of_big_integer))
  (value: big_integer_as_octet_string_t
         { valid_big_integer_as_octet_string_prop (v (snd tag)) value })
: GTot (refine_with_tag parser_tag_of_big_integer_as_octet_string tag)
= value

noextract
let synth_big_integer_as_octet_string_V_inverse
  (tag: (the_asn1_type INTEGER & asn1_value_int32_of_big_integer))
  (value': refine_with_tag parser_tag_of_big_integer_as_octet_string tag)
: GTot (value: big_integer_as_octet_string_t
               { valid_big_integer_as_octet_string_prop (v (snd tag)) value /\
                 value' == synth_big_integer_as_octet_string_V tag value})
= value'


///
/// Aux parser
///
noextract
let parse_big_integer_as_octet_string_V
  (tag: (the_asn1_type INTEGER & asn1_value_int32_of_big_integer))
: parser (weak_kind_of_big_integer) (refine_with_tag parser_tag_of_big_integer_as_octet_string tag)
= weak_kind_of_big_integer
  `weaken`
  parse_big_integer_as_octet_string (v (snd tag))
  `parse_synth`
  synth_big_integer_as_octet_string_V tag

///
/// Aux serializer
///
noextract
let serialize_big_integer_as_octet_string_V
  (tag: (the_asn1_type INTEGER & asn1_value_int32_of_big_integer))
: serializer (parse_big_integer_as_octet_string_V tag)
= serialize_synth
  (* p1 *) (weak_kind_of_big_integer
            `weaken`
            parse_big_integer_as_octet_string (v (snd tag)))
  (* f2 *) (synth_big_integer_as_octet_string_V tag)
  (* s1 *) (weak_kind_of_big_integer
            `serialize_weaken`
            serialize_big_integer_as_octet_string (v (snd tag)))
  (* g1 *) (synth_big_integer_as_octet_string_V_inverse tag)
  (* prf*) ()

///
/// Lemmas
///

/// Reveal the computation of parse
noextract
let lemma_parse_big_integer_as_octet_string_V_unfold
  (tag: (the_asn1_type INTEGER & asn1_value_int32_of_big_integer))
  (input: bytes)
: Lemma (
  parse (parse_big_integer_as_octet_string_V tag) input ==
 (match parse (parse_big_integer_as_octet_string (v (snd tag))) input with
  | None -> None
  | Some (value, consumed) ->  Some (synth_big_integer_as_octet_string_V tag value, consumed)))
= parse_synth_eq
  (* p1 *) (weak_kind_of_big_integer
            `weaken`
            parse_big_integer_as_octet_string (v (snd tag)))
  (* f2 *) (synth_big_integer_as_octet_string_V tag)
  (* in *) input

/// Reveal the computation of serialzation
noextract
let lemma_serialize_big_integer_as_octet_string_V_unfold
  (tag: (the_asn1_type INTEGER & asn1_value_int32_of_big_integer))
  (value: refine_with_tag parser_tag_of_big_integer_as_octet_string tag)
: Lemma (
  serialize (serialize_big_integer_as_octet_string_V tag) value ==
  serialize (serialize_big_integer_as_octet_string (v (snd tag))) value
)
= serialize_synth_eq
  (* p1 *) (weak_kind_of_big_integer
            `weaken`
            parse_big_integer_as_octet_string (v (snd tag)))
  (* f2 *) (synth_big_integer_as_octet_string_V tag)
  (* s1 *) (weak_kind_of_big_integer
            `serialize_weaken`
            serialize_big_integer_as_octet_string (v (snd tag)))
  (* g1 *) (synth_big_integer_as_octet_string_V_inverse tag)
  (* prf*) ()
  (* in *) (value)


//////////////////////////////////////////////////////////

noextract
let parse_big_integer_as_octet_string_TLV
: parser parse_big_integer_as_octet_string_TLV_kind big_integer_as_octet_string_t
= parse_tagged_union
  (* pt *) (parse_asn1_tag_of_type INTEGER
            `nondep_then`
            parse_asn1_length_of_big_integer)
  (* tg *) (parser_tag_of_big_integer_as_octet_string)
  (* p  *) (parse_big_integer_as_octet_string_V)

///
/// Serializer
///
noextract
let serialize_big_integer_as_octet_string_TLV
: serializer parse_big_integer_as_octet_string_TLV
= serialize_tagged_union
  (* st *) (serialize_asn1_tag_of_type INTEGER
            `serialize_nondep_then`
            serialize_asn1_length_of_big_integer)
  (* tg *) (parser_tag_of_big_integer_as_octet_string)
  (* s  *) (serialize_big_integer_as_octet_string_V)

///
/// Lemmas
///

/// Reveal the computation of serialize
#push-options "--z3rlimit 32"
noextract
let lemma_serialize_big_integer_as_octet_string_TLV_unfold
  (value: big_integer_as_octet_string_t)
: Lemma (
  let tg = parser_tag_of_big_integer_as_octet_string value in
  serialize serialize_big_integer_as_octet_string_TLV value ==
  serialize (serialize_asn1_tag_of_type INTEGER) INTEGER
  `Seq.append`
  serialize (serialize_asn1_length_of_big_integer) (snd tg)
  `Seq.append`
  serialize (serialize_big_integer_as_octet_string (v (snd tg))) value
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type INTEGER)
  (* s2 *) (serialize_asn1_length_of_big_integer)
  (* in *) (parser_tag_of_big_integer_as_octet_string value);
  lemma_serialize_big_integer_as_octet_string_V_unfold (parser_tag_of_big_integer_as_octet_string value) value;
  serialize_tagged_union_eq
  (* st *) (serialize_asn1_tag_of_type INTEGER
            `serialize_nondep_then`
            serialize_asn1_length_of_big_integer)
  (* tg *) (parser_tag_of_big_integer_as_octet_string)
  (* s  *) (serialize_big_integer_as_octet_string_V)
  (* in *) (value)
#pop-options

/// Reveal the size of a serialzation
#push-options "--z3rlimit 16"
noextract
let lemma_serialize_big_integer_as_octet_string_TLV_size
  (value: big_integer_as_octet_string_t)
: Lemma (
  let tg = parser_tag_of_big_integer_as_octet_string value in
  Seq.length (serialize serialize_big_integer_as_octet_string_TLV value) ==
  1 + length_of_asn1_length (snd tg) + v (snd tg)
)
= let tg = parser_tag_of_big_integer_as_octet_string value in
  lemma_serialize_big_integer_as_octet_string_TLV_unfold value;
  lemma_serialize_asn1_tag_of_type_size INTEGER INTEGER;
  lemma_serialize_asn1_length_size (snd tg);
  lemma_serialize_asn1_length_unfold (snd tg);
  serialize_bounded_der_length32_unfold 1 (asn1_length_max - 6) (snd tg);
  // serialize_asn1_length_of_type_eq INTEGER (dfst value);
  lemma_serialize_big_integer_as_octet_string_size (v (snd tg)) value
#pop-options


(* Low *)

open ASN1.Low
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
open LowParse.Low.Bytes

#push-options "--query_stats --z3rlimit 32"
inline_for_extraction
let serialize32_big_integer_as_octet_string_backwards
  (len: asn1_value_int32_of_big_integer)
: Tot (serializer32_backwards (serialize_big_integer_as_octet_string (v len)))
= fun (x)
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
->  (* prf *) let h0 = HST.get () in
    (* Prf *) lemma_serialize_big_integer_as_octet_string_unfold (v len) (x);
    (* Prf *) writable_weaken
              (* buf *) b
              (*range*) (v (pos - len)) (v pos)
              (* mem *) h0
              (* from*) (v (pos - dfst x))
              (* to  *) (v pos);
    store_bytes
      (* src *) (dsnd x)
      (* from*) 0ul
      (* to  *) (dfst x)
      (* dst *) b
      (* pos *) (pos - (dfst x));

    if (B32.get (dsnd x) 0ul >= 0x80uy) then
    ( let h1 = HST.get () in
      (* Prf *) writable_modifies
                (* buf *) b
                (*range*) (v (pos - len)) (v pos)
                (* mem *) h0
                (*other*) B.loc_none
                (* mem'*) h1;
      (* Prf *) writable_weaken
                (* buf *) b
                (*range*) (v (pos - len)) (v pos)
                (* mem *) h1
                (* from*) (v (pos - len))
                (* to  *) (v (pos - dfst x));
      mbuffer_upd
        (* buf *) b
        (*range*) (v (pos - len)) (v pos)
        (* pos *) (pos - len)
        (* val *) 0x00uy;
      (* Prf *) let h2 = HST.get () in
      (* Prf *) B.modifies_buffer_from_to_elim
            (* buf *) b
            (*frame*) (pos - dfst x) (pos)
            (* new *) (B.loc_buffer_from_to b (pos - len) (pos - dfst x))
            (* mem *) h1
            (* mem'*) h2;
  (* Prf *) Seq.lemma_split (Seq.slice (B.as_seq h2 b) (v (pos - len)) (v pos)) 1 );

(* retuen *) len
#pop-options

// let serialize32_big_integer_as_octet_string_TLV_backwards ()
// : Tot (serializer32_backwards (serialize_big_integer_as_octet_string_TLV))
// = serialize32_tagged_union_backwards
//   (* lst *) (serialize32_asn1_tag_of_type_backwards INTEGER
//              `serialize32_nondep_then_backwards`
//              serialize32_asn1_length_of_type_backwards INTEGER)
//   (* ltg *) (parser_tag_of_asn1_integer_impl)
//   (* ls  *) (fun parser_tag -> (serialize32_synth_backwards
//                               (* ls *) (weak_kind_of_type INTEGER
//                                         `serialize32_weaken_backwards`
//                                         serialize32_asn1_integer_backwards (snd parser_tag))
//                               (* f2 *) (synth_asn1_integer_V parser_tag)
//                               (* g1 *) (synth_asn1_integer_V_inverse parser_tag)
//                               (* g1'*) (synth_asn1_integer_V_inverse_impl parser_tag)
//                               (* prf*) ()))
