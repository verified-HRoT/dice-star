module ASN1.Spec.TLV.Specialized

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.BOOLEAN
open ASN1.Spec.NULL
open ASN1.Spec.OCTET_STRING
open LowParse.Bytes

module U32 = FStar.UInt32

/// Specialized ASN.1 DER (Primitive) TLV Parser
/// NOTE: For each Tag-Length-Value tuple, we firstly parse the
///       (Tag, Length) pair as the `parser_tag`, then use it to
///       choose a proper Value parser to parse the value.


/// Parser filter for valid ASN.1 DER `Tag`, `Length` pair
let filter_the_TL
  (a: asn1_primitive_type)
  (x: the_asn1_type a * asn1_int32)
: GTot bool
= let a', len = x in
  let min, max = bound_of_asn1_type a' in
  asn1_length_inbound (U32.v len) min max

/// Parser for valid ASN.1 DER `Tag`, `Length` pair
///
let parse_the_TL
  (a: asn1_primitive_type)
= parse_the_asn1_tag a
  `nondep_then`
  parse_asn1_length
  `parse_filter`
  filter_the_TL a

let parse_the_TL_unfold
  (a: asn1_primitive_type)
  (input: bytes)
: Lemma (
  let res = parse (parse_the_TL a) input in
  match parse (parse_the_asn1_tag a) input with
  | None -> res == None
  | Some (a, consumed_a) ->
    (let input_len = Seq.slice input consumed_a (Seq.length input) in
     match parse parse_asn1_length input_len with
     | None -> res == None
     | Some (len, consumed_len) ->
       (if filter_the_TL a (a, len) then
        ( res == Some ((a, len), consumed_a + consumed_len) )
        else
        ( res == None ))))
= nondep_then_eq
  (* p1 *) (parse_the_asn1_tag a)
  (* p2 *) (parse_asn1_length)
  (* in *) (input);
  parse_filter_eq
  (* p  *) (parse_the_asn1_tag a
           `nondep_then`
            parse_asn1_length)
  (* f  *) (filter_the_TL a)
  (* in *) (input)

/// Serializer for valid ASN.1 DER `Tag`, `Length` pair
///
let serialize_the_TL
  (a: asn1_primitive_type)
: serializer (parse_the_TL a)
= serialize_the_asn1_tag a
  `serialize_nondep_then`
  serialize_asn1_length
  `serialize_filter`
  filter_the_TL a

let serialize_the_TL_unfold
  (a: asn1_primitive_type)
  (x: parse_filter_refine (filter_the_TL a))
: Lemma (
  let a, len = x in
  let sx = serialize (serialize_the_TL a) x in
  let sx_T = serialize (serialize_the_asn1_tag a) a in
  let sx_L = serialize serialize_asn1_length len in
  sx == sx_T `Seq.append` sx_L /\
  Seq.length sx == Seq.length sx_T + Seq.length sx_L)
= parser_kind_prop_equiv (get_parser_kind (parse_the_asn1_tag a)) (parse_the_asn1_tag a);
  parser_kind_prop_equiv (get_parser_kind parse_asn1_length) parse_asn1_length;
  serialize_nondep_then_eq
  (* s1 *) (serialize_the_asn1_tag a)
  (* s2 *) (serialize_asn1_length)
  (* in *) x

/// EverParse tagged union tag of asn1_value
/// ASN.1 DER `Value` --> valid ASN.1 DER `Tag`, `Length` pair
/// NOTE: Current considering 1) BOOLEAN: partial encoding; 2) NULL: empty; 3) OCTET_STRING: variable length
///
let parser_tag_of_the_asn1_value
  (a: asn1_primitive_type)
  (v: asn1_value_of_tag a)
: Tot (parse_filter_refine (filter_the_TL a))
= match a, v with
  | BOOLEAN     , BOOLEAN_VALUE      b     -> (BOOLEAN     , 1ul)
  | NULL        , NULL_VALUE        ()     -> (NULL        , 0ul)
  | OCTET_STRING, OCTET_STRING_VALUE len s -> (OCTET_STRING, len)

// let parser_tag_of_asn1_value_impl
//   (v: asn1_value)
// : Tot (x: parse_filter_refine filter_TL{x == parser_tag_of_asn1_value v})
// = match v with
//   | BOOLEAN_VALUE      b   -> (BOOLEAN     , 1ul)
//   | NULL_VALUE        ()   -> (NULL        , 0ul)
//   | OCTET_STRING_VALUE l s -> (OCTET_STRING, U32.uint_to_t l)

/// Synth functions
let synth_the_asn1_boolean_value
  (a: the_asn1_type BOOLEAN)
  (x: parse_filter_refine (filter_the_TL a){x == (BOOLEAN, 1ul)})
  (b: bool)
: GTot (refine_with_tag (parser_tag_of_the_asn1_value a) x)
= BOOLEAN_VALUE b

let synth_the_asn1_boolean_value_inverse
  (a: the_asn1_type BOOLEAN)
  (x: parse_filter_refine (filter_the_TL a){x == (BOOLEAN, 1ul)})
  (value: refine_with_tag (parser_tag_of_the_asn1_value a) x)
: GTot bool
= BOOLEAN_VALUE?.b value

let synth_the_asn1_null_value
  (a: the_asn1_type NULL)
  (x: parse_filter_refine (filter_the_TL a){x == (NULL, 0ul)})
  (n: unit)
: GTot (refine_with_tag (parser_tag_of_the_asn1_value a) x)
= NULL_VALUE n

let synth_the_asn1_null_value_inverse
  (a: the_asn1_type NULL)
  (x: parse_filter_refine (filter_the_TL a){x == (NULL, 0ul)})
  (value: refine_with_tag (parser_tag_of_the_asn1_value a) x)
: GTot unit
= NULL_VALUE?.n value

let lbytes = Seq.Properties.lseq byte

let synth_the_asn1_octet_string_value
  (a: the_asn1_type OCTET_STRING)
  (len: asn1_int32)
  (x: parse_filter_refine (filter_the_TL a){x == (OCTET_STRING, len)})
  (s: lbytes (U32.v len))
: GTot (refine_with_tag (parser_tag_of_the_asn1_value a) x)
= OCTET_STRING_VALUE len s

let synth_the_asn1_octet_string_value_inverse
  (a: the_asn1_type OCTET_STRING)
  (len: asn1_int32)
  (x: parse_filter_refine (filter_the_TL a){x == (OCTET_STRING, len)})
  (value: refine_with_tag (parser_tag_of_the_asn1_value a) x)
: GTot (s: lbytes (U32.v len))
= OCTET_STRING_VALUE?.s value


/// Strong parser kind for ASN.1 DER `Value` parser
let parse_the_asn1_value_kind
  (a: asn1_primitive_type)
  (x: parse_filter_refine (filter_the_TL a))
: parser_kind
= let a, len = x in
  let l = U32.v len in
  strong_parser_kind l l None

/// Weak Strong parser kind for ASN.1 DER `Value` parser, throw "runtime" tag, length
let parse_asn1_value_kind_weak = strong_parser_kind asn1_length_min asn1_length_max None


/// Parser for ASN.1 DER `Value`
///
let parse_the_asn1_value
  (a: asn1_primitive_type)
  (x: parse_filter_refine (filter_the_TL a))
: Tot (parser (parse_the_asn1_value_kind a x) (refine_with_tag (parser_tag_of_the_asn1_value a) x))
= let a, len = x in
  let l: asn1_length_t = U32.v len in
  match a with
  | BOOLEAN      -> (parse_the_asn1_value_kind a x
                     `weaken`
                    (parse_asn1_boolean
                     `parse_synth`
                    // (fun b -> BOOLEAN_VALUE b <: refine_with_tag (parser_tag_of_the_asn1_value) x)
                    (synth_the_asn1_boolean_value a x)))

  | NULL         -> (parse_the_asn1_value_kind a x
                     `weaken`
                    (parse_asn1_null
                     `parse_synth`
                    // (fun n -> NULL_VALUE n <: refine_with_tag (parser_tag_of_the_asn1_value) x)
                    (synth_the_asn1_null_value a x)))

  | OCTET_STRING -> (parse_the_asn1_value_kind a x
                     `weaken`
                    (parse_asn1_octet_string l
                     `parse_synth`
                    // (fun (s: lbytes len) -> OCTET_STRING_VALUE s len <: refine_with_tag (parser_tag_of_the_asn1_value) x)
                    (synth_the_asn1_octet_string_value a len x)))

#push-options "--query_stats --z3rlimit 32 --max_fuel 16 --max_ifuel 16"
let parse_the_asn1_value_unfold
  (_a: asn1_primitive_type)
  (x: parse_filter_refine (filter_the_TL _a))
  (input: bytes)
: Lemma (
  let a, len = x in
  let l: asn1_length_t = U32.v len in
  let value = parse (parse_the_asn1_value a x) input in
  match a with
  | BOOLEAN      -> (match parse parse_asn1_boolean input with
                     | None -> value == None
                     | Some (b, consumed) ->
                            (parser_tag_of_the_asn1_value) a (BOOLEAN_VALUE b) == x /\
                            consumed == l /\
                            value == Some (BOOLEAN_VALUE b, consumed))

  | NULL         -> (match parse parse_asn1_null input with
                     | None -> value == None
                     | Some (null, consumed) ->
                            (parser_tag_of_the_asn1_value) a (NULL_VALUE null) == x /\
                            consumed == l /\
                            value == Some (NULL_VALUE null, consumed))

  | OCTET_STRING -> (match parse (parse_asn1_octet_string l) input with
                     | None -> value == None
                     | Some (s, consumed) -> True \/
                            (parser_tag_of_the_asn1_value) a (OCTET_STRING_VALUE len s) == x /\
                            consumed == l /\
                            value == Some (OCTET_STRING_VALUE len s, consumed)))
= let a, len = x in
  let l = U32.v len in
  match a with
  | BOOLEAN      -> (parse_asn1_boolean_unfold input;
                     parser_kind_prop_equiv (get_parser_kind parse_asn1_boolean) parse_asn1_boolean;
                     parse_synth_eq
                     (* p1 *) (parse_asn1_boolean)
                     (* f2 *) (synth_the_asn1_boolean_value a x)
                           // (fun b -> BOOLEAN_VALUE b <: refine_with_tag (parser_tag_of_the_asn1_value) x)
                     (* in *) input)

  | NULL         -> (parse_synth_eq
                     (* p1 *) (parse_asn1_null)
                     (* f2 *) (synth_the_asn1_null_value a x)
                           // (fun n -> NULL_VALUE n <: refine_with_tag (parser_tag_of_the_asn1_value) x)
                     (* in *) input)

  | OCTET_STRING -> (parse_synth_eq
                     (* p1 *) (parse_asn1_octet_string l)
                     (* f2 *) (synth_the_asn1_octet_string_value a len x)
                           // (fun (s: lbytes len) -> OCTET_STRING_VALUE s len <: refine_with_tag (parser_tag_of_the_asn1_value) x)
                     (* in *) input)

/// Serializer for ASN.1 DER `Value`
///
let serialize_the_asn1_value
  (_a: asn1_primitive_type)
  (x: parse_filter_refine (filter_the_TL _a))
: Tot (serializer (parse_the_asn1_value _a x))
= let a, len = x in
  let l = U32.v len in
  match a with
  | BOOLEAN      -> (parse_the_asn1_value_kind a x
                    `serialize_weaken`
                    (serialize_synth
                     (* p1 *) (parse_asn1_boolean)
                     (* f2 *) (synth_the_asn1_boolean_value a x)
                           // (fun b -> BOOLEAN_VALUE b <: refine_with_tag (parser_tag_of_the_asn1_value) x)
                     (* s1 *) (serialize_asn1_boolean)
                     (* g1 *) (synth_the_asn1_boolean_value_inverse a x)
                           // (fun v -> BOOLEAN_VALUE?.b v)
                     (* prf*) ()))

  | NULL         -> (parse_the_asn1_value_kind a x
                     `serialize_weaken`
                    (serialize_synth
                     (* p1 *) (parse_asn1_null)
                     (* f2 *) (synth_the_asn1_null_value a x)
                           // (fun n -> NULL_VALUE n <: refine_with_tag (parser_tag_of_the_asn1_value) x)
                     (* s1 *) (serialize_asn1_null)
                     (* g1 *) (synth_the_asn1_null_value_inverse a x)
                           // (fun v -> NULL_VALUE?.n v)
                     (* prf*) ()))

  | OCTET_STRING -> (parse_the_asn1_value_kind a x
                     `serialize_weaken`
                    (serialize_synth
                     (* p1 *) (parse_asn1_octet_string l)
                     (* f2 *) (synth_the_asn1_octet_string_value a len x)
                     (* s1 *) (serialize_asn1_octet_string l)
                     (* g1 *) (synth_the_asn1_octet_string_value_inverse a len x)
                     (* prf*) ()))

let serialize_the_asn1_value_unfold
  (_a: asn1_primitive_type)
  (x: parse_filter_refine (filter_the_TL _a))
  (value: refine_with_tag (parser_tag_of_the_asn1_value _a) x)
: Lemma (
  let a, len = x in
  let l = U32.v len in
  let sx = serialize (serialize_the_asn1_value a x) value in
  match a with
  | BOOLEAN      -> (sx == serialize serialize_asn1_boolean      (BOOLEAN_VALUE?.b value)      /\
                     l == Seq.length sx)
  | NULL         -> (sx == serialize serialize_asn1_null         (NULL_VALUE?.n value)         /\
                     l == Seq.length sx)
  | OCTET_STRING -> (sx == serialize (serialize_asn1_octet_string l) (OCTET_STRING_VALUE?.s value) /\
                     l == Seq.length sx))
= let a, len = x in
  let l = U32.v len in
  match a with
  | BOOLEAN      -> (serialize_synth_eq
                     (* p1 *) (parse_asn1_boolean)
                     (* f2 *) (synth_the_asn1_boolean_value a x)
                           // (fun b -> BOOLEAN_VALUE b <: refine_with_tag (parser_tag_of_the_asn1_value) a x)
                     (* s1 *) (serialize_asn1_boolean)
                     (* g1 *) (synth_the_asn1_boolean_value_inverse a x)
                           // (fun v -> BOOLEAN_VALUE?.b v)
                     (* prf*) ()
                     (* x  *) (value))

  | NULL         -> (serialize_synth_eq
                     (* p1 *) (parse_asn1_null)
                     (* f2 *) (synth_the_asn1_null_value a x)
                           // (fun n -> NULL_VALUE n <: refine_with_tag (parser_tag_of_the_asn1_value) a x)
                     (* s1 *) (serialize_asn1_null)
                     (* g1 *) (synth_the_asn1_null_value_inverse a x)
                           // (fun v -> NULL_VALUE?.n v)
                     (* prf*) ()
                     (* x  *) (value))

  | OCTET_STRING -> (serialize_synth_eq
                     (* p1 *) (parse_asn1_octet_string l)
                     (* f2 *) (synth_the_asn1_octet_string_value a len x)
                     (* s1 *) (serialize_asn1_octet_string l)
                     (* g1 *) (synth_the_asn1_octet_string_value_inverse a len x)
                     (* prf*) ()
                     (* x  *) (value))


/// Kind for ASN.1 DER Tag, Length, Value tuple parser
let parse_TLV_kind_of_tag
  (_a: asn1_primitive_type)
= get_parser_kind (parse_the_TL _a)
  `and_then_kind`
  parse_asn1_value_kind_weak

/// Parser for ASN.1 DER Tag, Length, Value tuples
///
let parse_TLV_of_tag
  (_a: asn1_primitive_type)
: parser (parse_TLV_kind_of_tag _a) (asn1_value_of_tag _a)
= parse_tagged_union
    (parse_the_TL _a)
    (parser_tag_of_the_asn1_value _a)
    (fun x -> parse_asn1_value_kind_weak
            `weaken`
            parse_the_asn1_value _a x)

let parse_TLV_of_tag_unfold
  (_a: asn1_primitive_type)
  (input: bytes)
: Lemma (
  parse (parse_TLV_of_tag _a) input ==
  (match parse (parse_the_TL _a) input with
  | None -> None
  | Some (x, consumed_TL) ->
        (let input_value = Seq.slice input consumed_TL (Seq.length input) in
         match (parse_the_asn1_value _a) x input_value with
         | None -> None
         | Some (value', consumed_v) -> Some (value', consumed_TL + consumed_v))))
= parse_tagged_union_eq
  (* pt *) (parse_the_TL _a)
  (* tg *) ((parser_tag_of_the_asn1_value _a))
  (* p  *) (fun x -> parse_asn1_value_kind_weak
                   `weaken`
                   (parse_the_asn1_value _a) x)
  (* in *) (input)

/// Serializer for ASN.1 DER Tag, Length, Value tuples
///
let serialize_TLV_of_tag
  (_a: asn1_primitive_type)
: serializer (parse_TLV_of_tag _a)
= serialize_tagged_union
    (serialize_the_TL _a)
    (parser_tag_of_the_asn1_value _a)
    (fun x -> parse_asn1_value_kind_weak
            `serialize_weaken`
            serialize_the_asn1_value _a x)

let serialize_TLV_of_tag_unfold
  (_a: asn1_primitive_type)
  (value: asn1_value_of_tag _a)
: Lemma (
  let x = (parser_tag_of_the_asn1_value _a) value in
  let sx = serialize (serialize_TLV_of_tag _a) value in
  let sx_TL = serialize (serialize_the_TL _a) x in
  let sx_V  = serialize (serialize_the_asn1_value _a x) value in
  sx == sx_TL `Seq.append` sx_V /\
  Seq.length sx == Seq.length sx_TL + Seq.length sx_V)
= let x = (parser_tag_of_the_asn1_value _a) value in
  parser_kind_prop_equiv (get_parser_kind (parse_the_TL _a)) (parse_the_TL _a);
  parser_kind_prop_equiv (get_parser_kind (parse_the_asn1_value _a x)) (parse_the_asn1_value _a x);
  serialize_tagged_union_eq
  (* st *) (serialize_the_TL _a)
  (* tg *) ((parser_tag_of_the_asn1_value _a))
  (* s  *) (fun x -> parse_asn1_value_kind_weak
                   `serialize_weaken`
                   serialize_the_asn1_value _a x)
  (* in *) (value)
