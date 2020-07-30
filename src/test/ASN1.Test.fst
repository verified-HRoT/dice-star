module ASN1.Test

open LowParse.Spec.Base
open LowParse.Low.Base
open ASN1.Base
open ASN1.Spec
open ASN1.Low

open LowStar.Printf
open LowStar.Comment
open LowStar.Failure

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module C = C
module B32 = FStar.Bytes

open FStar.Integers

open ASN1.Test.Helpers

#push-options "--lax"
let main ()
: HST.St (C.exit_code)
= HST.push_frame ();
  printf "Start Test\n" done;

  let dst_size = 500ul in
  let dst = B.alloca 0x00uy dst_size in

  printf "----------- Test 1 ----------\n" done;
  printf "raw: ASN.1 Write INTEGER 32767l 02027fff\n" done;
  let question = 32767l in
  let solution_len = 4ul in
  let solution = B.alloca_of_list [0x02uy; 0x02uy; 0x7fuy; 0xffuy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) INTEGER
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [INTEGER] 32767l\n" done;
  printf "Solution: %xuy\n" 4ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_INTEGER dst dst_size (dst_size - answer_len);

  printf "----------- Test 2 ----------\n" done;
  printf "raw: ASN.1 Write ASN1_NULL () 0500\n" done;
  let question = () in
  let solution_len = 2ul in
  let solution = B.alloca_of_list [0x05uy; 0x00uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) ASN1_NULL
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [ASN1_NULL] ()\n" done;
  printf "Solution: %xuy\n" 2ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_ASN1_NULL dst dst_size (dst_size - answer_len);

  printf "----------- Test 3 ----------\n" done;
  printf "raw: ASN.1 Write BOOLEAN false 010100\n" done;
  let question = false in
  let solution_len = 3ul in
  let solution = B.alloca_of_list [0x01uy; 0x01uy; 0x00uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) BOOLEAN
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [BOOLEAN] false\n" done;
  printf "Solution: %xuy\n" 3ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_BOOLEAN dst dst_size (dst_size - answer_len);

  printf "----------- Test 4 ----------\n" done;
  printf "raw: ASN.1 Write BOOLEAN true 0101ff\n" done;
  let question = true in
  let solution_len = 3ul in
  let solution = B.alloca_of_list [0x01uy; 0x01uy; 0xffuy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) BOOLEAN
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [BOOLEAN] true\n" done;
  printf "Solution: %xuy\n" 3ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_BOOLEAN dst dst_size (dst_size - answer_len);

  printf "----------- Test 5 ----------\n" done;
  printf "raw: ASN.1 Write INTEGER 0l 020100\n" done;
  let question = 0l in
  let solution_len = 3ul in
  let solution = B.alloca_of_list [0x02uy; 0x01uy; 0x00uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) INTEGER
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [INTEGER] 0l\n" done;
  printf "Solution: %xuy\n" 3ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_INTEGER dst dst_size (dst_size - answer_len);

  printf "----------- Test 6 ----------\n" done;
  printf "raw: ASN.1 Write INTEGER 1l 020101\n" done;
  let question = 1l in
  let solution_len = 3ul in
  let solution = B.alloca_of_list [0x02uy; 0x01uy; 0x01uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) INTEGER
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [INTEGER] 1l\n" done;
  printf "Solution: %xuy\n" 3ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_INTEGER dst dst_size (dst_size - answer_len);

  printf "----------- Test 7 ----------\n" done;
  printf "raw: ASN.1 Write INTEGER 127l 02017f\n" done;
  let question = 127l in
  let solution_len = 3ul in
  let solution = B.alloca_of_list [0x02uy; 0x01uy; 0x7fuy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) INTEGER
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [INTEGER] 127l\n" done;
  printf "Solution: %xuy\n" 3ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_INTEGER dst dst_size (dst_size - answer_len);

  printf "----------- Test 8 ----------\n" done;
  printf "raw: ASN.1 Write INTEGER 128l 02020080\n" done;
  let question = 128l in
  let solution_len = 4ul in
  let solution = B.alloca_of_list [0x02uy; 0x02uy; 0x00uy; 0x80uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) INTEGER
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [INTEGER] 128l\n" done;
  printf "Solution: %xuy\n" 4ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_INTEGER dst dst_size (dst_size - answer_len);

  printf "----------- Test 9 ----------\n" done;
  printf "raw: ASN.1 Write INTEGER 255l 020200ff\n" done;
  let question = 255l in
  let solution_len = 4ul in
  let solution = B.alloca_of_list [0x02uy; 0x02uy; 0x00uy; 0xffuy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) INTEGER
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [INTEGER] 255l\n" done;
  printf "Solution: %xuy\n" 4ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_INTEGER dst dst_size (dst_size - answer_len);

  printf "----------- Test 10 ----------\n" done;
  printf "raw: ASN.1 Write INTEGER 256l 02020100\n" done;
  let question = 256l in
  let solution_len = 4ul in
  let solution = B.alloca_of_list [0x02uy; 0x02uy; 0x01uy; 0x00uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) INTEGER
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [INTEGER] 256l\n" done;
  printf "Solution: %xuy\n" 4ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_INTEGER dst dst_size (dst_size - answer_len);

  printf "----------- Test 11 ----------\n" done;
  printf "raw: ASN.1 Write INTEGER 32767l 02027fff\n" done;
  let question = 32767l in
  let solution_len = 4ul in
  let solution = B.alloca_of_list [0x02uy; 0x02uy; 0x7fuy; 0xffuy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) INTEGER
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [INTEGER] 32767l\n" done;
  printf "Solution: %xuy\n" 4ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_INTEGER dst dst_size (dst_size - answer_len);

  printf "----------- Test 12 ----------\n" done;
  printf "raw: ASN.1 Write INTEGER 32768l 0203008000\n" done;
  let question = 32768l in
  let solution_len = 5ul in
  let solution = B.alloca_of_list [0x02uy; 0x03uy; 0x00uy; 0x80uy; 0x00uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) INTEGER
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [INTEGER] 32768l\n" done;
  printf "Solution: %xuy\n" 5ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_INTEGER dst dst_size (dst_size - answer_len);

  printf "----------- Test 13 ----------\n" done;
  printf "raw: ASN.1 Write INTEGER 65535l 020300ffff\n" done;
  let question = 65535l in
  let solution_len = 5ul in
  let solution = B.alloca_of_list [0x02uy; 0x03uy; 0x00uy; 0xffuy; 0xffuy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) INTEGER
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [INTEGER] 65535l\n" done;
  printf "Solution: %xuy\n" 5ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_INTEGER dst dst_size (dst_size - answer_len);

  printf "----------- Test 14 ----------\n" done;
  printf "raw: ASN.1 Write INTEGER 65536l 0203010000\n" done;
  let question = 65536l in
  let solution_len = 5ul in
  let solution = B.alloca_of_list [0x02uy; 0x03uy; 0x01uy; 0x00uy; 0x00uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) INTEGER
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [INTEGER] 65536l\n" done;
  printf "Solution: %xuy\n" 5ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_INTEGER dst dst_size (dst_size - answer_len);

  printf "----------- Test 15 ----------\n" done;
  printf "raw: ASN.1 Write INTEGER 8388607l 02037fffff\n" done;
  let question = 8388607l in
  let solution_len = 5ul in
  let solution = B.alloca_of_list [0x02uy; 0x03uy; 0x7fuy; 0xffuy; 0xffuy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) INTEGER
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [INTEGER] 8388607l\n" done;
  printf "Solution: %xuy\n" 5ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_INTEGER dst dst_size (dst_size - answer_len);

  printf "----------- Test 16 ----------\n" done;
  printf "raw: ASN.1 Write INTEGER 8388608l 020400800000\n" done;
  let question = 8388608l in
  let solution_len = 6ul in
  let solution = B.alloca_of_list [0x02uy; 0x04uy; 0x00uy; 0x80uy; 0x00uy; 0x00uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) INTEGER
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [INTEGER] 8388608l\n" done;
  printf "Solution: %xuy\n" 6ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_INTEGER dst dst_size (dst_size - answer_len);

  printf "----------- Test 17 ----------\n" done;
  printf "raw: ASN.1 Write INTEGER 0x12345678l 020412345678\n" done;
  let question = 0x12345678l in
  let solution_len = 6ul in
  let solution = B.alloca_of_list [0x02uy; 0x04uy; 0x12uy; 0x34uy; 0x56uy; 0x78uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) INTEGER
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [INTEGER] 0x12345678l\n" done;
  printf "Solution: %xuy\n" 6ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_INTEGER dst dst_size (dst_size - answer_len);

  printf "----------- Test 18 ----------\n" done;
  printf "raw: ASN.1 Write INTEGER 2147483647l 02047fffffff\n" done;
  let question = 2147483647l in
  let solution_len = 6ul in
  let solution = B.alloca_of_list [0x02uy; 0x04uy; 0x7fuy; 0xffuy; 0xffuy; 0xffuy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) INTEGER
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [INTEGER] 2147483647l\n" done;
  printf "Solution: %xuy\n" 6ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_INTEGER dst dst_size (dst_size - answer_len);

  printf "----------- Test 19 ----------\n" done;
  printf "raw: ASN.1 Write OCTET_STRING  0400\n" done;
  let question = B.alloca_of_list [] in
  let solution_len = 2ul in
  let solution = B.alloca_of_list [0x04uy; 0x00uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) OCTET_STRING
                   (* ASN1 Value*) (|0ul, B32.of_buffer 0ul question|)
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [OCTET_STRING] B.alloca_of_list []\n" done;
  printf "Solution: %xuy\n" 2ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_OCTET_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 20 ----------\n" done;
  printf "raw: ASN.1 Write OCTET_STRING 41 040141\n" done;
  let question = B.alloca_of_list [0x41uy] in
  let solution_len = 3ul in
  let solution = B.alloca_of_list [0x04uy; 0x01uy; 0x41uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) OCTET_STRING
                   (* ASN1 Value*) (|1ul, B32.of_buffer 1ul question|)
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [OCTET_STRING] B.alloca_of_list [0x41uy]\n" done;
  printf "Solution: %xuy\n" 3ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_OCTET_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 21 ----------\n" done;
  printf "raw: ASN.1 Write OCTET_STRING 4142 04024142\n" done;
  let question = B.alloca_of_list [0x41uy; 0x42uy] in
  let solution_len = 4ul in
  let solution = B.alloca_of_list [0x04uy; 0x02uy; 0x41uy; 0x42uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) OCTET_STRING
                   (* ASN1 Value*) (|2ul, B32.of_buffer 2ul question|)
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [OCTET_STRING] B.alloca_of_list [0x41uy; 0x42uy]\n" done;
  printf "Solution: %xuy\n" 4ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_OCTET_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 22 ----------\n" done;
  printf "raw: ASN.1 Write OCTET_STRING 99a66790856f7199641f55cadabb660aaed6aa0d9ef8cef4417118c6e8c6e15becbaa21c63faf48726e92357a38b3079a0b9d60be7457ec6552f900dd032577167c91e829927343c3a769b362db4de0ad2ffb8f13cc2eeca9e52dc557118baa88b857477595622bc301a1ae2150030d652c4a482cf88d0ded85d6731ff2d38 047f99a66790856f7199641f55cadabb660aaed6aa0d9ef8cef4417118c6e8c6e15becbaa21c63faf48726e92357a38b3079a0b9d60be7457ec6552f900dd032577167c91e829927343c3a769b362db4de0ad2ffb8f13cc2eeca9e52dc557118baa88b857477595622bc301a1ae2150030d652c4a482cf88d0ded85d6731ff2d38\n" done;
  let question = B.alloca_of_list [0x99uy; 0xa6uy; 0x67uy; 0x90uy; 0x85uy; 0x6fuy; 0x71uy; 0x99uy; 0x64uy; 0x1fuy; 0x55uy; 0xcauy; 0xdauy; 0xbbuy; 0x66uy; 0x0auy; 0xaeuy; 0xd6uy; 0xaauy; 0x0duy; 0x9euy; 0xf8uy; 0xceuy; 0xf4uy; 0x41uy; 0x71uy; 0x18uy; 0xc6uy; 0xe8uy; 0xc6uy; 0xe1uy; 0x5buy; 0xecuy; 0xbauy; 0xa2uy; 0x1cuy; 0x63uy; 0xfauy; 0xf4uy; 0x87uy; 0x26uy; 0xe9uy; 0x23uy; 0x57uy; 0xa3uy; 0x8buy; 0x30uy; 0x79uy; 0xa0uy; 0xb9uy; 0xd6uy; 0x0buy; 0xe7uy; 0x45uy; 0x7euy; 0xc6uy; 0x55uy; 0x2fuy; 0x90uy; 0x0duy; 0xd0uy; 0x32uy; 0x57uy; 0x71uy; 0x67uy; 0xc9uy; 0x1euy; 0x82uy; 0x99uy; 0x27uy; 0x34uy; 0x3cuy; 0x3auy; 0x76uy; 0x9buy; 0x36uy; 0x2duy; 0xb4uy; 0xdeuy; 0x0auy; 0xd2uy; 0xffuy; 0xb8uy; 0xf1uy; 0x3cuy; 0xc2uy; 0xeeuy; 0xcauy; 0x9euy; 0x52uy; 0xdcuy; 0x55uy; 0x71uy; 0x18uy; 0xbauy; 0xa8uy; 0x8buy; 0x85uy; 0x74uy; 0x77uy; 0x59uy; 0x56uy; 0x22uy; 0xbcuy; 0x30uy; 0x1auy; 0x1auy; 0xe2uy; 0x15uy; 0x00uy; 0x30uy; 0xd6uy; 0x52uy; 0xc4uy; 0xa4uy; 0x82uy; 0xcfuy; 0x88uy; 0xd0uy; 0xdeuy; 0xd8uy; 0x5duy; 0x67uy; 0x31uy; 0xffuy; 0x2duy; 0x38uy] in
  let solution_len = 129ul in
  let solution = B.alloca_of_list [0x04uy; 0x7fuy; 0x99uy; 0xa6uy; 0x67uy; 0x90uy; 0x85uy; 0x6fuy; 0x71uy; 0x99uy; 0x64uy; 0x1fuy; 0x55uy; 0xcauy; 0xdauy; 0xbbuy; 0x66uy; 0x0auy; 0xaeuy; 0xd6uy; 0xaauy; 0x0duy; 0x9euy; 0xf8uy; 0xceuy; 0xf4uy; 0x41uy; 0x71uy; 0x18uy; 0xc6uy; 0xe8uy; 0xc6uy; 0xe1uy; 0x5buy; 0xecuy; 0xbauy; 0xa2uy; 0x1cuy; 0x63uy; 0xfauy; 0xf4uy; 0x87uy; 0x26uy; 0xe9uy; 0x23uy; 0x57uy; 0xa3uy; 0x8buy; 0x30uy; 0x79uy; 0xa0uy; 0xb9uy; 0xd6uy; 0x0buy; 0xe7uy; 0x45uy; 0x7euy; 0xc6uy; 0x55uy; 0x2fuy; 0x90uy; 0x0duy; 0xd0uy; 0x32uy; 0x57uy; 0x71uy; 0x67uy; 0xc9uy; 0x1euy; 0x82uy; 0x99uy; 0x27uy; 0x34uy; 0x3cuy; 0x3auy; 0x76uy; 0x9buy; 0x36uy; 0x2duy; 0xb4uy; 0xdeuy; 0x0auy; 0xd2uy; 0xffuy; 0xb8uy; 0xf1uy; 0x3cuy; 0xc2uy; 0xeeuy; 0xcauy; 0x9euy; 0x52uy; 0xdcuy; 0x55uy; 0x71uy; 0x18uy; 0xbauy; 0xa8uy; 0x8buy; 0x85uy; 0x74uy; 0x77uy; 0x59uy; 0x56uy; 0x22uy; 0xbcuy; 0x30uy; 0x1auy; 0x1auy; 0xe2uy; 0x15uy; 0x00uy; 0x30uy; 0xd6uy; 0x52uy; 0xc4uy; 0xa4uy; 0x82uy; 0xcfuy; 0x88uy; 0xd0uy; 0xdeuy; 0xd8uy; 0x5duy; 0x67uy; 0x31uy; 0xffuy; 0x2duy; 0x38uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) OCTET_STRING
                   (* ASN1 Value*) (|127ul, B32.of_buffer 127ul question|)
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [OCTET_STRING] B.alloca_of_list [0x99uy; 0xa6uy; 0x67uy; 0x90uy; 0x85uy; 0x6fuy; 0x71uy; 0x99uy; 0x64uy; 0x1fuy; 0x55uy; 0xcauy; 0xdauy; 0xbbuy; 0x66uy; 0x0auy; 0xaeuy; 0xd6uy; 0xaauy; 0x0duy; 0x9euy; 0xf8uy; 0xceuy; 0xf4uy; 0x41uy; 0x71uy; 0x18uy; 0xc6uy; 0xe8uy; 0xc6uy; 0xe1uy; 0x5buy; 0xecuy; 0xbauy; 0xa2uy; 0x1cuy; 0x63uy; 0xfauy; 0xf4uy; 0x87uy; 0x26uy; 0xe9uy; 0x23uy; 0x57uy; 0xa3uy; 0x8buy; 0x30uy; 0x79uy; 0xa0uy; 0xb9uy; 0xd6uy; 0x0buy; 0xe7uy; 0x45uy; 0x7euy; 0xc6uy; 0x55uy; 0x2fuy; 0x90uy; 0x0duy; 0xd0uy; 0x32uy; 0x57uy; 0x71uy; 0x67uy; 0xc9uy; 0x1euy; 0x82uy; 0x99uy; 0x27uy; 0x34uy; 0x3cuy; 0x3auy; 0x76uy; 0x9buy; 0x36uy; 0x2duy; 0xb4uy; 0xdeuy; 0x0auy; 0xd2uy; 0xffuy; 0xb8uy; 0xf1uy; 0x3cuy; 0xc2uy; 0xeeuy; 0xcauy; 0x9euy; 0x52uy; 0xdcuy; 0x55uy; 0x71uy; 0x18uy; 0xbauy; 0xa8uy; 0x8buy; 0x85uy; 0x74uy; 0x77uy; 0x59uy; 0x56uy; 0x22uy; 0xbcuy; 0x30uy; 0x1auy; 0x1auy; 0xe2uy; 0x15uy; 0x00uy; 0x30uy; 0xd6uy; 0x52uy; 0xc4uy; 0xa4uy; 0x82uy; 0xcfuy; 0x88uy; 0xd0uy; 0xdeuy; 0xd8uy; 0x5duy; 0x67uy; 0x31uy; 0xffuy; 0x2duy; 0x38uy]\n" done;
  printf "Solution: %xuy\n" 129ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_OCTET_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 23 ----------\n" done;
  printf "raw: ASN.1 Write OCTET_STRING 0199a66790856f7199641f55cadabb660aaed6aa0d9ef8cef4417118c6e8c6e15becbaa21c63faf48726e92357a38b3079a0b9d60be7457ec6552f900dd032577167c91e829927343c3a769b362db4de0ad2ffb8f13cc2eeca9e52dc557118baa88b857477595622bc301a1ae2150030d652c4a482cf88d0ded85d6731ff2d38 0481800199a66790856f7199641f55cadabb660aaed6aa0d9ef8cef4417118c6e8c6e15becbaa21c63faf48726e92357a38b3079a0b9d60be7457ec6552f900dd032577167c91e829927343c3a769b362db4de0ad2ffb8f13cc2eeca9e52dc557118baa88b857477595622bc301a1ae2150030d652c4a482cf88d0ded85d6731ff2d38\n" done;
  let question = B.alloca_of_list [0x01uy; 0x99uy; 0xa6uy; 0x67uy; 0x90uy; 0x85uy; 0x6fuy; 0x71uy; 0x99uy; 0x64uy; 0x1fuy; 0x55uy; 0xcauy; 0xdauy; 0xbbuy; 0x66uy; 0x0auy; 0xaeuy; 0xd6uy; 0xaauy; 0x0duy; 0x9euy; 0xf8uy; 0xceuy; 0xf4uy; 0x41uy; 0x71uy; 0x18uy; 0xc6uy; 0xe8uy; 0xc6uy; 0xe1uy; 0x5buy; 0xecuy; 0xbauy; 0xa2uy; 0x1cuy; 0x63uy; 0xfauy; 0xf4uy; 0x87uy; 0x26uy; 0xe9uy; 0x23uy; 0x57uy; 0xa3uy; 0x8buy; 0x30uy; 0x79uy; 0xa0uy; 0xb9uy; 0xd6uy; 0x0buy; 0xe7uy; 0x45uy; 0x7euy; 0xc6uy; 0x55uy; 0x2fuy; 0x90uy; 0x0duy; 0xd0uy; 0x32uy; 0x57uy; 0x71uy; 0x67uy; 0xc9uy; 0x1euy; 0x82uy; 0x99uy; 0x27uy; 0x34uy; 0x3cuy; 0x3auy; 0x76uy; 0x9buy; 0x36uy; 0x2duy; 0xb4uy; 0xdeuy; 0x0auy; 0xd2uy; 0xffuy; 0xb8uy; 0xf1uy; 0x3cuy; 0xc2uy; 0xeeuy; 0xcauy; 0x9euy; 0x52uy; 0xdcuy; 0x55uy; 0x71uy; 0x18uy; 0xbauy; 0xa8uy; 0x8buy; 0x85uy; 0x74uy; 0x77uy; 0x59uy; 0x56uy; 0x22uy; 0xbcuy; 0x30uy; 0x1auy; 0x1auy; 0xe2uy; 0x15uy; 0x00uy; 0x30uy; 0xd6uy; 0x52uy; 0xc4uy; 0xa4uy; 0x82uy; 0xcfuy; 0x88uy; 0xd0uy; 0xdeuy; 0xd8uy; 0x5duy; 0x67uy; 0x31uy; 0xffuy; 0x2duy; 0x38uy] in
  let solution_len = 131ul in
  let solution = B.alloca_of_list [0x04uy; 0x81uy; 0x80uy; 0x01uy; 0x99uy; 0xa6uy; 0x67uy; 0x90uy; 0x85uy; 0x6fuy; 0x71uy; 0x99uy; 0x64uy; 0x1fuy; 0x55uy; 0xcauy; 0xdauy; 0xbbuy; 0x66uy; 0x0auy; 0xaeuy; 0xd6uy; 0xaauy; 0x0duy; 0x9euy; 0xf8uy; 0xceuy; 0xf4uy; 0x41uy; 0x71uy; 0x18uy; 0xc6uy; 0xe8uy; 0xc6uy; 0xe1uy; 0x5buy; 0xecuy; 0xbauy; 0xa2uy; 0x1cuy; 0x63uy; 0xfauy; 0xf4uy; 0x87uy; 0x26uy; 0xe9uy; 0x23uy; 0x57uy; 0xa3uy; 0x8buy; 0x30uy; 0x79uy; 0xa0uy; 0xb9uy; 0xd6uy; 0x0buy; 0xe7uy; 0x45uy; 0x7euy; 0xc6uy; 0x55uy; 0x2fuy; 0x90uy; 0x0duy; 0xd0uy; 0x32uy; 0x57uy; 0x71uy; 0x67uy; 0xc9uy; 0x1euy; 0x82uy; 0x99uy; 0x27uy; 0x34uy; 0x3cuy; 0x3auy; 0x76uy; 0x9buy; 0x36uy; 0x2duy; 0xb4uy; 0xdeuy; 0x0auy; 0xd2uy; 0xffuy; 0xb8uy; 0xf1uy; 0x3cuy; 0xc2uy; 0xeeuy; 0xcauy; 0x9euy; 0x52uy; 0xdcuy; 0x55uy; 0x71uy; 0x18uy; 0xbauy; 0xa8uy; 0x8buy; 0x85uy; 0x74uy; 0x77uy; 0x59uy; 0x56uy; 0x22uy; 0xbcuy; 0x30uy; 0x1auy; 0x1auy; 0xe2uy; 0x15uy; 0x00uy; 0x30uy; 0xd6uy; 0x52uy; 0xc4uy; 0xa4uy; 0x82uy; 0xcfuy; 0x88uy; 0xd0uy; 0xdeuy; 0xd8uy; 0x5duy; 0x67uy; 0x31uy; 0xffuy; 0x2duy; 0x38uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) OCTET_STRING
                   (* ASN1 Value*) (|128ul, B32.of_buffer 128ul question|)
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [OCTET_STRING] B.alloca_of_list [0x01uy; 0x99uy; 0xa6uy; 0x67uy; 0x90uy; 0x85uy; 0x6fuy; 0x71uy; 0x99uy; 0x64uy; 0x1fuy; 0x55uy; 0xcauy; 0xdauy; 0xbbuy; 0x66uy; 0x0auy; 0xaeuy; 0xd6uy; 0xaauy; 0x0duy; 0x9euy; 0xf8uy; 0xceuy; 0xf4uy; 0x41uy; 0x71uy; 0x18uy; 0xc6uy; 0xe8uy; 0xc6uy; 0xe1uy; 0x5buy; 0xecuy; 0xbauy; 0xa2uy; 0x1cuy; 0x63uy; 0xfauy; 0xf4uy; 0x87uy; 0x26uy; 0xe9uy; 0x23uy; 0x57uy; 0xa3uy; 0x8buy; 0x30uy; 0x79uy; 0xa0uy; 0xb9uy; 0xd6uy; 0x0buy; 0xe7uy; 0x45uy; 0x7euy; 0xc6uy; 0x55uy; 0x2fuy; 0x90uy; 0x0duy; 0xd0uy; 0x32uy; 0x57uy; 0x71uy; 0x67uy; 0xc9uy; 0x1euy; 0x82uy; 0x99uy; 0x27uy; 0x34uy; 0x3cuy; 0x3auy; 0x76uy; 0x9buy; 0x36uy; 0x2duy; 0xb4uy; 0xdeuy; 0x0auy; 0xd2uy; 0xffuy; 0xb8uy; 0xf1uy; 0x3cuy; 0xc2uy; 0xeeuy; 0xcauy; 0x9euy; 0x52uy; 0xdcuy; 0x55uy; 0x71uy; 0x18uy; 0xbauy; 0xa8uy; 0x8buy; 0x85uy; 0x74uy; 0x77uy; 0x59uy; 0x56uy; 0x22uy; 0xbcuy; 0x30uy; 0x1auy; 0x1auy; 0xe2uy; 0x15uy; 0x00uy; 0x30uy; 0xd6uy; 0x52uy; 0xc4uy; 0xa4uy; 0x82uy; 0xcfuy; 0x88uy; 0xd0uy; 0xdeuy; 0xd8uy; 0x5duy; 0x67uy; 0x31uy; 0xffuy; 0x2duy; 0x38uy]\n" done;
  printf "Solution: %xuy\n" 131ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_OCTET_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 24 ----------\n" done;
  printf "raw: ASN.1 Write OCTET_STRING 633ed2cb0a2915dc4438a4c063017eb336cd9571d2a0585522c5073ca22a30ca7b8c9bd167d89ba1827bc6fb5d6ef6dcc52ee6eecc47e84ee0dd18fa3ebbdb6edfc679f037160d48d46a0d7e571335b24a28c8fd29b7f4a93d013b74e522bc1f5f605096bb99d438814b77b54d6dde608417b0a0ce9a8cb507fbeb95e9926b4bb6eec725599493d4b156ef3a5fd701426456029111c20f1d03c5d8999d2c042277ef91c5114a6c06218c1ba28d41ef08e4870d0cef260cba9de16d7d11ed5889b88fb93073746ebb158a4246cdb8a4ce403a5d1d598a0d11548f22070f833c1344d15e7a1445c133d19b8295b7c071bf2227178938031249d22d21c6f8e53d 0481ff633ed2cb0a2915dc4438a4c063017eb336cd9571d2a0585522c5073ca22a30ca7b8c9bd167d89ba1827bc6fb5d6ef6dcc52ee6eecc47e84ee0dd18fa3ebbdb6edfc679f037160d48d46a0d7e571335b24a28c8fd29b7f4a93d013b74e522bc1f5f605096bb99d438814b77b54d6dde608417b0a0ce9a8cb507fbeb95e9926b4bb6eec725599493d4b156ef3a5fd701426456029111c20f1d03c5d8999d2c042277ef91c5114a6c06218c1ba28d41ef08e4870d0cef260cba9de16d7d11ed5889b88fb93073746ebb158a4246cdb8a4ce403a5d1d598a0d11548f22070f833c1344d15e7a1445c133d19b8295b7c071bf2227178938031249d22d21c6f8e53d\n" done;
  let question = B.alloca_of_list [0x63uy; 0x3euy; 0xd2uy; 0xcbuy; 0x0auy; 0x29uy; 0x15uy; 0xdcuy; 0x44uy; 0x38uy; 0xa4uy; 0xc0uy; 0x63uy; 0x01uy; 0x7euy; 0xb3uy; 0x36uy; 0xcduy; 0x95uy; 0x71uy; 0xd2uy; 0xa0uy; 0x58uy; 0x55uy; 0x22uy; 0xc5uy; 0x07uy; 0x3cuy; 0xa2uy; 0x2auy; 0x30uy; 0xcauy; 0x7buy; 0x8cuy; 0x9buy; 0xd1uy; 0x67uy; 0xd8uy; 0x9buy; 0xa1uy; 0x82uy; 0x7buy; 0xc6uy; 0xfbuy; 0x5duy; 0x6euy; 0xf6uy; 0xdcuy; 0xc5uy; 0x2euy; 0xe6uy; 0xeeuy; 0xccuy; 0x47uy; 0xe8uy; 0x4euy; 0xe0uy; 0xdduy; 0x18uy; 0xfauy; 0x3euy; 0xbbuy; 0xdbuy; 0x6euy; 0xdfuy; 0xc6uy; 0x79uy; 0xf0uy; 0x37uy; 0x16uy; 0x0duy; 0x48uy; 0xd4uy; 0x6auy; 0x0duy; 0x7euy; 0x57uy; 0x13uy; 0x35uy; 0xb2uy; 0x4auy; 0x28uy; 0xc8uy; 0xfduy; 0x29uy; 0xb7uy; 0xf4uy; 0xa9uy; 0x3duy; 0x01uy; 0x3buy; 0x74uy; 0xe5uy; 0x22uy; 0xbcuy; 0x1fuy; 0x5fuy; 0x60uy; 0x50uy; 0x96uy; 0xbbuy; 0x99uy; 0xd4uy; 0x38uy; 0x81uy; 0x4buy; 0x77uy; 0xb5uy; 0x4duy; 0x6duy; 0xdeuy; 0x60uy; 0x84uy; 0x17uy; 0xb0uy; 0xa0uy; 0xceuy; 0x9auy; 0x8cuy; 0xb5uy; 0x07uy; 0xfbuy; 0xebuy; 0x95uy; 0xe9uy; 0x92uy; 0x6buy; 0x4buy; 0xb6uy; 0xeeuy; 0xc7uy; 0x25uy; 0x59uy; 0x94uy; 0x93uy; 0xd4uy; 0xb1uy; 0x56uy; 0xefuy; 0x3auy; 0x5fuy; 0xd7uy; 0x01uy; 0x42uy; 0x64uy; 0x56uy; 0x02uy; 0x91uy; 0x11uy; 0xc2uy; 0x0fuy; 0x1duy; 0x03uy; 0xc5uy; 0xd8uy; 0x99uy; 0x9duy; 0x2cuy; 0x04uy; 0x22uy; 0x77uy; 0xefuy; 0x91uy; 0xc5uy; 0x11uy; 0x4auy; 0x6cuy; 0x06uy; 0x21uy; 0x8cuy; 0x1buy; 0xa2uy; 0x8duy; 0x41uy; 0xefuy; 0x08uy; 0xe4uy; 0x87uy; 0x0duy; 0x0cuy; 0xefuy; 0x26uy; 0x0cuy; 0xbauy; 0x9duy; 0xe1uy; 0x6duy; 0x7duy; 0x11uy; 0xeduy; 0x58uy; 0x89uy; 0xb8uy; 0x8fuy; 0xb9uy; 0x30uy; 0x73uy; 0x74uy; 0x6euy; 0xbbuy; 0x15uy; 0x8auy; 0x42uy; 0x46uy; 0xcduy; 0xb8uy; 0xa4uy; 0xceuy; 0x40uy; 0x3auy; 0x5duy; 0x1duy; 0x59uy; 0x8auy; 0x0duy; 0x11uy; 0x54uy; 0x8fuy; 0x22uy; 0x07uy; 0x0fuy; 0x83uy; 0x3cuy; 0x13uy; 0x44uy; 0xd1uy; 0x5euy; 0x7auy; 0x14uy; 0x45uy; 0xc1uy; 0x33uy; 0xd1uy; 0x9buy; 0x82uy; 0x95uy; 0xb7uy; 0xc0uy; 0x71uy; 0xbfuy; 0x22uy; 0x27uy; 0x17uy; 0x89uy; 0x38uy; 0x03uy; 0x12uy; 0x49uy; 0xd2uy; 0x2duy; 0x21uy; 0xc6uy; 0xf8uy; 0xe5uy; 0x3duy] in
  let solution_len = 258ul in
  let solution = B.alloca_of_list [0x04uy; 0x81uy; 0xffuy; 0x63uy; 0x3euy; 0xd2uy; 0xcbuy; 0x0auy; 0x29uy; 0x15uy; 0xdcuy; 0x44uy; 0x38uy; 0xa4uy; 0xc0uy; 0x63uy; 0x01uy; 0x7euy; 0xb3uy; 0x36uy; 0xcduy; 0x95uy; 0x71uy; 0xd2uy; 0xa0uy; 0x58uy; 0x55uy; 0x22uy; 0xc5uy; 0x07uy; 0x3cuy; 0xa2uy; 0x2auy; 0x30uy; 0xcauy; 0x7buy; 0x8cuy; 0x9buy; 0xd1uy; 0x67uy; 0xd8uy; 0x9buy; 0xa1uy; 0x82uy; 0x7buy; 0xc6uy; 0xfbuy; 0x5duy; 0x6euy; 0xf6uy; 0xdcuy; 0xc5uy; 0x2euy; 0xe6uy; 0xeeuy; 0xccuy; 0x47uy; 0xe8uy; 0x4euy; 0xe0uy; 0xdduy; 0x18uy; 0xfauy; 0x3euy; 0xbbuy; 0xdbuy; 0x6euy; 0xdfuy; 0xc6uy; 0x79uy; 0xf0uy; 0x37uy; 0x16uy; 0x0duy; 0x48uy; 0xd4uy; 0x6auy; 0x0duy; 0x7euy; 0x57uy; 0x13uy; 0x35uy; 0xb2uy; 0x4auy; 0x28uy; 0xc8uy; 0xfduy; 0x29uy; 0xb7uy; 0xf4uy; 0xa9uy; 0x3duy; 0x01uy; 0x3buy; 0x74uy; 0xe5uy; 0x22uy; 0xbcuy; 0x1fuy; 0x5fuy; 0x60uy; 0x50uy; 0x96uy; 0xbbuy; 0x99uy; 0xd4uy; 0x38uy; 0x81uy; 0x4buy; 0x77uy; 0xb5uy; 0x4duy; 0x6duy; 0xdeuy; 0x60uy; 0x84uy; 0x17uy; 0xb0uy; 0xa0uy; 0xceuy; 0x9auy; 0x8cuy; 0xb5uy; 0x07uy; 0xfbuy; 0xebuy; 0x95uy; 0xe9uy; 0x92uy; 0x6buy; 0x4buy; 0xb6uy; 0xeeuy; 0xc7uy; 0x25uy; 0x59uy; 0x94uy; 0x93uy; 0xd4uy; 0xb1uy; 0x56uy; 0xefuy; 0x3auy; 0x5fuy; 0xd7uy; 0x01uy; 0x42uy; 0x64uy; 0x56uy; 0x02uy; 0x91uy; 0x11uy; 0xc2uy; 0x0fuy; 0x1duy; 0x03uy; 0xc5uy; 0xd8uy; 0x99uy; 0x9duy; 0x2cuy; 0x04uy; 0x22uy; 0x77uy; 0xefuy; 0x91uy; 0xc5uy; 0x11uy; 0x4auy; 0x6cuy; 0x06uy; 0x21uy; 0x8cuy; 0x1buy; 0xa2uy; 0x8duy; 0x41uy; 0xefuy; 0x08uy; 0xe4uy; 0x87uy; 0x0duy; 0x0cuy; 0xefuy; 0x26uy; 0x0cuy; 0xbauy; 0x9duy; 0xe1uy; 0x6duy; 0x7duy; 0x11uy; 0xeduy; 0x58uy; 0x89uy; 0xb8uy; 0x8fuy; 0xb9uy; 0x30uy; 0x73uy; 0x74uy; 0x6euy; 0xbbuy; 0x15uy; 0x8auy; 0x42uy; 0x46uy; 0xcduy; 0xb8uy; 0xa4uy; 0xceuy; 0x40uy; 0x3auy; 0x5duy; 0x1duy; 0x59uy; 0x8auy; 0x0duy; 0x11uy; 0x54uy; 0x8fuy; 0x22uy; 0x07uy; 0x0fuy; 0x83uy; 0x3cuy; 0x13uy; 0x44uy; 0xd1uy; 0x5euy; 0x7auy; 0x14uy; 0x45uy; 0xc1uy; 0x33uy; 0xd1uy; 0x9buy; 0x82uy; 0x95uy; 0xb7uy; 0xc0uy; 0x71uy; 0xbfuy; 0x22uy; 0x27uy; 0x17uy; 0x89uy; 0x38uy; 0x03uy; 0x12uy; 0x49uy; 0xd2uy; 0x2duy; 0x21uy; 0xc6uy; 0xf8uy; 0xe5uy; 0x3duy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) OCTET_STRING
                   (* ASN1 Value*) (|255ul, B32.of_buffer 255ul question|)
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [OCTET_STRING] B.alloca_of_list [0x63uy; 0x3euy; 0xd2uy; 0xcbuy; 0x0auy; 0x29uy; 0x15uy; 0xdcuy; 0x44uy; 0x38uy; 0xa4uy; 0xc0uy; 0x63uy; 0x01uy; 0x7euy; 0xb3uy; 0x36uy; 0xcduy; 0x95uy; 0x71uy; 0xd2uy; 0xa0uy; 0x58uy; 0x55uy; 0x22uy; 0xc5uy; 0x07uy; 0x3cuy; 0xa2uy; 0x2auy; 0x30uy; 0xcauy; 0x7buy; 0x8cuy; 0x9buy; 0xd1uy; 0x67uy; 0xd8uy; 0x9buy; 0xa1uy; 0x82uy; 0x7buy; 0xc6uy; 0xfbuy; 0x5duy; 0x6euy; 0xf6uy; 0xdcuy; 0xc5uy; 0x2euy; 0xe6uy; 0xeeuy; 0xccuy; 0x47uy; 0xe8uy; 0x4euy; 0xe0uy; 0xdduy; 0x18uy; 0xfauy; 0x3euy; 0xbbuy; 0xdbuy; 0x6euy; 0xdfuy; 0xc6uy; 0x79uy; 0xf0uy; 0x37uy; 0x16uy; 0x0duy; 0x48uy; 0xd4uy; 0x6auy; 0x0duy; 0x7euy; 0x57uy; 0x13uy; 0x35uy; 0xb2uy; 0x4auy; 0x28uy; 0xc8uy; 0xfduy; 0x29uy; 0xb7uy; 0xf4uy; 0xa9uy; 0x3duy; 0x01uy; 0x3buy; 0x74uy; 0xe5uy; 0x22uy; 0xbcuy; 0x1fuy; 0x5fuy; 0x60uy; 0x50uy; 0x96uy; 0xbbuy; 0x99uy; 0xd4uy; 0x38uy; 0x81uy; 0x4buy; 0x77uy; 0xb5uy; 0x4duy; 0x6duy; 0xdeuy; 0x60uy; 0x84uy; 0x17uy; 0xb0uy; 0xa0uy; 0xceuy; 0x9auy; 0x8cuy; 0xb5uy; 0x07uy; 0xfbuy; 0xebuy; 0x95uy; 0xe9uy; 0x92uy; 0x6buy; 0x4buy; 0xb6uy; 0xeeuy; 0xc7uy; 0x25uy; 0x59uy; 0x94uy; 0x93uy; 0xd4uy; 0xb1uy; 0x56uy; 0xefuy; 0x3auy; 0x5fuy; 0xd7uy; 0x01uy; 0x42uy; 0x64uy; 0x56uy; 0x02uy; 0x91uy; 0x11uy; 0xc2uy; 0x0fuy; 0x1duy; 0x03uy; 0xc5uy; 0xd8uy; 0x99uy; 0x9duy; 0x2cuy; 0x04uy; 0x22uy; 0x77uy; 0xefuy; 0x91uy; 0xc5uy; 0x11uy; 0x4auy; 0x6cuy; 0x06uy; 0x21uy; 0x8cuy; 0x1buy; 0xa2uy; 0x8duy; 0x41uy; 0xefuy; 0x08uy; 0xe4uy; 0x87uy; 0x0duy; 0x0cuy; 0xefuy; 0x26uy; 0x0cuy; 0xbauy; 0x9duy; 0xe1uy; 0x6duy; 0x7duy; 0x11uy; 0xeduy; 0x58uy; 0x89uy; 0xb8uy; 0x8fuy; 0xb9uy; 0x30uy; 0x73uy; 0x74uy; 0x6euy; 0xbbuy; 0x15uy; 0x8auy; 0x42uy; 0x46uy; 0xcduy; 0xb8uy; 0xa4uy; 0xceuy; 0x40uy; 0x3auy; 0x5duy; 0x1duy; 0x59uy; 0x8auy; 0x0duy; 0x11uy; 0x54uy; 0x8fuy; 0x22uy; 0x07uy; 0x0fuy; 0x83uy; 0x3cuy; 0x13uy; 0x44uy; 0xd1uy; 0x5euy; 0x7auy; 0x14uy; 0x45uy; 0xc1uy; 0x33uy; 0xd1uy; 0x9buy; 0x82uy; 0x95uy; 0xb7uy; 0xc0uy; 0x71uy; 0xbfuy; 0x22uy; 0x27uy; 0x17uy; 0x89uy; 0x38uy; 0x03uy; 0x12uy; 0x49uy; 0xd2uy; 0x2duy; 0x21uy; 0xc6uy; 0xf8uy; 0xe5uy; 0x3duy]\n" done;
  printf "Solution: %xuy\n" 258ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_OCTET_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 25 ----------\n" done;
  printf "raw: ASN.1 Write OCTET_STRING 5a633ed2cb0a2915dc4438a4c063017eb336cd9571d2a0585522c5073ca22a30ca7b8c9bd167d89ba1827bc6fb5d6ef6dcc52ee6eecc47e84ee0dd18fa3ebbdb6edfc679f037160d48d46a0d7e571335b24a28c8fd29b7f4a93d013b74e522bc1f5f605096bb99d438814b77b54d6dde608417b0a0ce9a8cb507fbeb95e9926b4bb6eec725599493d4b156ef3a5fd701426456029111c20f1d03c5d8999d2c042277ef91c5114a6c06218c1ba28d41ef08e4870d0cef260cba9de16d7d11ed5889b88fb93073746ebb158a4246cdb8a4ce403a5d1d598a0d11548f22070f833c1344d15e7a1445c133d19b8295b7c071bf2227178938031249d22d21c6f8e53d 048201005a633ed2cb0a2915dc4438a4c063017eb336cd9571d2a0585522c5073ca22a30ca7b8c9bd167d89ba1827bc6fb5d6ef6dcc52ee6eecc47e84ee0dd18fa3ebbdb6edfc679f037160d48d46a0d7e571335b24a28c8fd29b7f4a93d013b74e522bc1f5f605096bb99d438814b77b54d6dde608417b0a0ce9a8cb507fbeb95e9926b4bb6eec725599493d4b156ef3a5fd701426456029111c20f1d03c5d8999d2c042277ef91c5114a6c06218c1ba28d41ef08e4870d0cef260cba9de16d7d11ed5889b88fb93073746ebb158a4246cdb8a4ce403a5d1d598a0d11548f22070f833c1344d15e7a1445c133d19b8295b7c071bf2227178938031249d22d21c6f8e53d\n" done;
  let question = B.alloca_of_list [0x5auy; 0x63uy; 0x3euy; 0xd2uy; 0xcbuy; 0x0auy; 0x29uy; 0x15uy; 0xdcuy; 0x44uy; 0x38uy; 0xa4uy; 0xc0uy; 0x63uy; 0x01uy; 0x7euy; 0xb3uy; 0x36uy; 0xcduy; 0x95uy; 0x71uy; 0xd2uy; 0xa0uy; 0x58uy; 0x55uy; 0x22uy; 0xc5uy; 0x07uy; 0x3cuy; 0xa2uy; 0x2auy; 0x30uy; 0xcauy; 0x7buy; 0x8cuy; 0x9buy; 0xd1uy; 0x67uy; 0xd8uy; 0x9buy; 0xa1uy; 0x82uy; 0x7buy; 0xc6uy; 0xfbuy; 0x5duy; 0x6euy; 0xf6uy; 0xdcuy; 0xc5uy; 0x2euy; 0xe6uy; 0xeeuy; 0xccuy; 0x47uy; 0xe8uy; 0x4euy; 0xe0uy; 0xdduy; 0x18uy; 0xfauy; 0x3euy; 0xbbuy; 0xdbuy; 0x6euy; 0xdfuy; 0xc6uy; 0x79uy; 0xf0uy; 0x37uy; 0x16uy; 0x0duy; 0x48uy; 0xd4uy; 0x6auy; 0x0duy; 0x7euy; 0x57uy; 0x13uy; 0x35uy; 0xb2uy; 0x4auy; 0x28uy; 0xc8uy; 0xfduy; 0x29uy; 0xb7uy; 0xf4uy; 0xa9uy; 0x3duy; 0x01uy; 0x3buy; 0x74uy; 0xe5uy; 0x22uy; 0xbcuy; 0x1fuy; 0x5fuy; 0x60uy; 0x50uy; 0x96uy; 0xbbuy; 0x99uy; 0xd4uy; 0x38uy; 0x81uy; 0x4buy; 0x77uy; 0xb5uy; 0x4duy; 0x6duy; 0xdeuy; 0x60uy; 0x84uy; 0x17uy; 0xb0uy; 0xa0uy; 0xceuy; 0x9auy; 0x8cuy; 0xb5uy; 0x07uy; 0xfbuy; 0xebuy; 0x95uy; 0xe9uy; 0x92uy; 0x6buy; 0x4buy; 0xb6uy; 0xeeuy; 0xc7uy; 0x25uy; 0x59uy; 0x94uy; 0x93uy; 0xd4uy; 0xb1uy; 0x56uy; 0xefuy; 0x3auy; 0x5fuy; 0xd7uy; 0x01uy; 0x42uy; 0x64uy; 0x56uy; 0x02uy; 0x91uy; 0x11uy; 0xc2uy; 0x0fuy; 0x1duy; 0x03uy; 0xc5uy; 0xd8uy; 0x99uy; 0x9duy; 0x2cuy; 0x04uy; 0x22uy; 0x77uy; 0xefuy; 0x91uy; 0xc5uy; 0x11uy; 0x4auy; 0x6cuy; 0x06uy; 0x21uy; 0x8cuy; 0x1buy; 0xa2uy; 0x8duy; 0x41uy; 0xefuy; 0x08uy; 0xe4uy; 0x87uy; 0x0duy; 0x0cuy; 0xefuy; 0x26uy; 0x0cuy; 0xbauy; 0x9duy; 0xe1uy; 0x6duy; 0x7duy; 0x11uy; 0xeduy; 0x58uy; 0x89uy; 0xb8uy; 0x8fuy; 0xb9uy; 0x30uy; 0x73uy; 0x74uy; 0x6euy; 0xbbuy; 0x15uy; 0x8auy; 0x42uy; 0x46uy; 0xcduy; 0xb8uy; 0xa4uy; 0xceuy; 0x40uy; 0x3auy; 0x5duy; 0x1duy; 0x59uy; 0x8auy; 0x0duy; 0x11uy; 0x54uy; 0x8fuy; 0x22uy; 0x07uy; 0x0fuy; 0x83uy; 0x3cuy; 0x13uy; 0x44uy; 0xd1uy; 0x5euy; 0x7auy; 0x14uy; 0x45uy; 0xc1uy; 0x33uy; 0xd1uy; 0x9buy; 0x82uy; 0x95uy; 0xb7uy; 0xc0uy; 0x71uy; 0xbfuy; 0x22uy; 0x27uy; 0x17uy; 0x89uy; 0x38uy; 0x03uy; 0x12uy; 0x49uy; 0xd2uy; 0x2duy; 0x21uy; 0xc6uy; 0xf8uy; 0xe5uy; 0x3duy] in
  let solution_len = 260ul in
  let solution = B.alloca_of_list [0x04uy; 0x82uy; 0x01uy; 0x00uy; 0x5auy; 0x63uy; 0x3euy; 0xd2uy; 0xcbuy; 0x0auy; 0x29uy; 0x15uy; 0xdcuy; 0x44uy; 0x38uy; 0xa4uy; 0xc0uy; 0x63uy; 0x01uy; 0x7euy; 0xb3uy; 0x36uy; 0xcduy; 0x95uy; 0x71uy; 0xd2uy; 0xa0uy; 0x58uy; 0x55uy; 0x22uy; 0xc5uy; 0x07uy; 0x3cuy; 0xa2uy; 0x2auy; 0x30uy; 0xcauy; 0x7buy; 0x8cuy; 0x9buy; 0xd1uy; 0x67uy; 0xd8uy; 0x9buy; 0xa1uy; 0x82uy; 0x7buy; 0xc6uy; 0xfbuy; 0x5duy; 0x6euy; 0xf6uy; 0xdcuy; 0xc5uy; 0x2euy; 0xe6uy; 0xeeuy; 0xccuy; 0x47uy; 0xe8uy; 0x4euy; 0xe0uy; 0xdduy; 0x18uy; 0xfauy; 0x3euy; 0xbbuy; 0xdbuy; 0x6euy; 0xdfuy; 0xc6uy; 0x79uy; 0xf0uy; 0x37uy; 0x16uy; 0x0duy; 0x48uy; 0xd4uy; 0x6auy; 0x0duy; 0x7euy; 0x57uy; 0x13uy; 0x35uy; 0xb2uy; 0x4auy; 0x28uy; 0xc8uy; 0xfduy; 0x29uy; 0xb7uy; 0xf4uy; 0xa9uy; 0x3duy; 0x01uy; 0x3buy; 0x74uy; 0xe5uy; 0x22uy; 0xbcuy; 0x1fuy; 0x5fuy; 0x60uy; 0x50uy; 0x96uy; 0xbbuy; 0x99uy; 0xd4uy; 0x38uy; 0x81uy; 0x4buy; 0x77uy; 0xb5uy; 0x4duy; 0x6duy; 0xdeuy; 0x60uy; 0x84uy; 0x17uy; 0xb0uy; 0xa0uy; 0xceuy; 0x9auy; 0x8cuy; 0xb5uy; 0x07uy; 0xfbuy; 0xebuy; 0x95uy; 0xe9uy; 0x92uy; 0x6buy; 0x4buy; 0xb6uy; 0xeeuy; 0xc7uy; 0x25uy; 0x59uy; 0x94uy; 0x93uy; 0xd4uy; 0xb1uy; 0x56uy; 0xefuy; 0x3auy; 0x5fuy; 0xd7uy; 0x01uy; 0x42uy; 0x64uy; 0x56uy; 0x02uy; 0x91uy; 0x11uy; 0xc2uy; 0x0fuy; 0x1duy; 0x03uy; 0xc5uy; 0xd8uy; 0x99uy; 0x9duy; 0x2cuy; 0x04uy; 0x22uy; 0x77uy; 0xefuy; 0x91uy; 0xc5uy; 0x11uy; 0x4auy; 0x6cuy; 0x06uy; 0x21uy; 0x8cuy; 0x1buy; 0xa2uy; 0x8duy; 0x41uy; 0xefuy; 0x08uy; 0xe4uy; 0x87uy; 0x0duy; 0x0cuy; 0xefuy; 0x26uy; 0x0cuy; 0xbauy; 0x9duy; 0xe1uy; 0x6duy; 0x7duy; 0x11uy; 0xeduy; 0x58uy; 0x89uy; 0xb8uy; 0x8fuy; 0xb9uy; 0x30uy; 0x73uy; 0x74uy; 0x6euy; 0xbbuy; 0x15uy; 0x8auy; 0x42uy; 0x46uy; 0xcduy; 0xb8uy; 0xa4uy; 0xceuy; 0x40uy; 0x3auy; 0x5duy; 0x1duy; 0x59uy; 0x8auy; 0x0duy; 0x11uy; 0x54uy; 0x8fuy; 0x22uy; 0x07uy; 0x0fuy; 0x83uy; 0x3cuy; 0x13uy; 0x44uy; 0xd1uy; 0x5euy; 0x7auy; 0x14uy; 0x45uy; 0xc1uy; 0x33uy; 0xd1uy; 0x9buy; 0x82uy; 0x95uy; 0xb7uy; 0xc0uy; 0x71uy; 0xbfuy; 0x22uy; 0x27uy; 0x17uy; 0x89uy; 0x38uy; 0x03uy; 0x12uy; 0x49uy; 0xd2uy; 0x2duy; 0x21uy; 0xc6uy; 0xf8uy; 0xe5uy; 0x3duy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) OCTET_STRING
                   (* ASN1 Value*) (|256ul, B32.of_buffer 256ul question|)
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [OCTET_STRING] B.alloca_of_list [0x5auy; 0x63uy; 0x3euy; 0xd2uy; 0xcbuy; 0x0auy; 0x29uy; 0x15uy; 0xdcuy; 0x44uy; 0x38uy; 0xa4uy; 0xc0uy; 0x63uy; 0x01uy; 0x7euy; 0xb3uy; 0x36uy; 0xcduy; 0x95uy; 0x71uy; 0xd2uy; 0xa0uy; 0x58uy; 0x55uy; 0x22uy; 0xc5uy; 0x07uy; 0x3cuy; 0xa2uy; 0x2auy; 0x30uy; 0xcauy; 0x7buy; 0x8cuy; 0x9buy; 0xd1uy; 0x67uy; 0xd8uy; 0x9buy; 0xa1uy; 0x82uy; 0x7buy; 0xc6uy; 0xfbuy; 0x5duy; 0x6euy; 0xf6uy; 0xdcuy; 0xc5uy; 0x2euy; 0xe6uy; 0xeeuy; 0xccuy; 0x47uy; 0xe8uy; 0x4euy; 0xe0uy; 0xdduy; 0x18uy; 0xfauy; 0x3euy; 0xbbuy; 0xdbuy; 0x6euy; 0xdfuy; 0xc6uy; 0x79uy; 0xf0uy; 0x37uy; 0x16uy; 0x0duy; 0x48uy; 0xd4uy; 0x6auy; 0x0duy; 0x7euy; 0x57uy; 0x13uy; 0x35uy; 0xb2uy; 0x4auy; 0x28uy; 0xc8uy; 0xfduy; 0x29uy; 0xb7uy; 0xf4uy; 0xa9uy; 0x3duy; 0x01uy; 0x3buy; 0x74uy; 0xe5uy; 0x22uy; 0xbcuy; 0x1fuy; 0x5fuy; 0x60uy; 0x50uy; 0x96uy; 0xbbuy; 0x99uy; 0xd4uy; 0x38uy; 0x81uy; 0x4buy; 0x77uy; 0xb5uy; 0x4duy; 0x6duy; 0xdeuy; 0x60uy; 0x84uy; 0x17uy; 0xb0uy; 0xa0uy; 0xceuy; 0x9auy; 0x8cuy; 0xb5uy; 0x07uy; 0xfbuy; 0xebuy; 0x95uy; 0xe9uy; 0x92uy; 0x6buy; 0x4buy; 0xb6uy; 0xeeuy; 0xc7uy; 0x25uy; 0x59uy; 0x94uy; 0x93uy; 0xd4uy; 0xb1uy; 0x56uy; 0xefuy; 0x3auy; 0x5fuy; 0xd7uy; 0x01uy; 0x42uy; 0x64uy; 0x56uy; 0x02uy; 0x91uy; 0x11uy; 0xc2uy; 0x0fuy; 0x1duy; 0x03uy; 0xc5uy; 0xd8uy; 0x99uy; 0x9duy; 0x2cuy; 0x04uy; 0x22uy; 0x77uy; 0xefuy; 0x91uy; 0xc5uy; 0x11uy; 0x4auy; 0x6cuy; 0x06uy; 0x21uy; 0x8cuy; 0x1buy; 0xa2uy; 0x8duy; 0x41uy; 0xefuy; 0x08uy; 0xe4uy; 0x87uy; 0x0duy; 0x0cuy; 0xefuy; 0x26uy; 0x0cuy; 0xbauy; 0x9duy; 0xe1uy; 0x6duy; 0x7duy; 0x11uy; 0xeduy; 0x58uy; 0x89uy; 0xb8uy; 0x8fuy; 0xb9uy; 0x30uy; 0x73uy; 0x74uy; 0x6euy; 0xbbuy; 0x15uy; 0x8auy; 0x42uy; 0x46uy; 0xcduy; 0xb8uy; 0xa4uy; 0xceuy; 0x40uy; 0x3auy; 0x5duy; 0x1duy; 0x59uy; 0x8auy; 0x0duy; 0x11uy; 0x54uy; 0x8fuy; 0x22uy; 0x07uy; 0x0fuy; 0x83uy; 0x3cuy; 0x13uy; 0x44uy; 0xd1uy; 0x5euy; 0x7auy; 0x14uy; 0x45uy; 0xc1uy; 0x33uy; 0xd1uy; 0x9buy; 0x82uy; 0x95uy; 0xb7uy; 0xc0uy; 0x71uy; 0xbfuy; 0x22uy; 0x27uy; 0x17uy; 0x89uy; 0x38uy; 0x03uy; 0x12uy; 0x49uy; 0xd2uy; 0x2duy; 0x21uy; 0xc6uy; 0xf8uy; 0xe5uy; 0x3duy]\n" done;
  printf "Solution: %xuy\n" 260ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_OCTET_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 26 ----------\n" done;
  printf "raw: ASN.1 Write BIT_STRING 0 FF 030200FF\n" done;
  let question = B.alloca_of_list [0xFFuy] in
  let solution_len = 4ul in
  let solution = B.alloca_of_list [0x03uy; 0x02uy; 0x00uy; 0xFFuy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) BIT_STRING
                   (* ASN1 Value*) (Mkbit_string_t 2ul 0ul (B32.of_buffer 1ul question))
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [BIT_STRING] B.alloca_of_list [0xFFuy]\n" done;
  printf "Solution: %xuy\n" 4ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_BIT_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 27 ----------\n" done;
  printf "raw: ASN.1 Write BIT_STRING 1 FF 030201FE\n" done;
  let question = B.alloca_of_list [0xFFuy] in
  let solution_len = 4ul in
  let solution = B.alloca_of_list [0x03uy; 0x02uy; 0x01uy; 0xFEuy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) BIT_STRING
                   (* ASN1 Value*) (Mkbit_string_t 2ul 1ul (B32.of_buffer 1ul question))
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [BIT_STRING] B.alloca_of_list [0xFFuy]\n" done;
  printf "Solution: %xuy\n" 4ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_BIT_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 28 ----------\n" done;
  printf "raw: ASN.1 Write BIT_STRING 2 FF 030202FC\n" done;
  let question = B.alloca_of_list [0xFFuy] in
  let solution_len = 4ul in
  let solution = B.alloca_of_list [0x03uy; 0x02uy; 0x02uy; 0xFCuy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) BIT_STRING
                   (* ASN1 Value*) (Mkbit_string_t 2ul 2ul (B32.of_buffer 1ul question))
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [BIT_STRING] B.alloca_of_list [0xFFuy]\n" done;
  printf "Solution: %xuy\n" 4ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_BIT_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 29 ----------\n" done;
  printf "raw: ASN.1 Write BIT_STRING 3 FF 030203F8\n" done;
  let question = B.alloca_of_list [0xFFuy] in
  let solution_len = 4ul in
  let solution = B.alloca_of_list [0x03uy; 0x02uy; 0x03uy; 0xF8uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) BIT_STRING
                   (* ASN1 Value*) (Mkbit_string_t 2ul 3ul (B32.of_buffer 1ul question))
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [BIT_STRING] B.alloca_of_list [0xFFuy]\n" done;
  printf "Solution: %xuy\n" 4ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_BIT_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 30 ----------\n" done;
  printf "raw: ASN.1 Write BIT_STRING 4 FF 030204F0\n" done;
  let question = B.alloca_of_list [0xFFuy] in
  let solution_len = 4ul in
  let solution = B.alloca_of_list [0x03uy; 0x02uy; 0x04uy; 0xF0uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) BIT_STRING
                   (* ASN1 Value*) (Mkbit_string_t 2ul 4ul (B32.of_buffer 1ul question))
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [BIT_STRING] B.alloca_of_list [0xFFuy]\n" done;
  printf "Solution: %xuy\n" 4ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_BIT_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 31 ----------\n" done;
  printf "raw: ASN.1 Write BIT_STRING 5 FF 030205E0\n" done;
  let question = B.alloca_of_list [0xFFuy] in
  let solution_len = 4ul in
  let solution = B.alloca_of_list [0x03uy; 0x02uy; 0x05uy; 0xE0uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) BIT_STRING
                   (* ASN1 Value*) (Mkbit_string_t 2ul 5ul (B32.of_buffer 1ul question))
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [BIT_STRING] B.alloca_of_list [0xFFuy]\n" done;
  printf "Solution: %xuy\n" 4ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_BIT_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 32 ----------\n" done;
  printf "raw: ASN.1 Write BIT_STRING 6 FF 030206C0\n" done;
  let question = B.alloca_of_list [0xFFuy] in
  let solution_len = 4ul in
  let solution = B.alloca_of_list [0x03uy; 0x02uy; 0x06uy; 0xC0uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) BIT_STRING
                   (* ASN1 Value*) (Mkbit_string_t 2ul 6ul (B32.of_buffer 1ul question))
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [BIT_STRING] B.alloca_of_list [0xFFuy]\n" done;
  printf "Solution: %xuy\n" 4ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_BIT_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 33 ----------\n" done;
  printf "raw: ASN.1 Write BIT_STRING 7 FF 03020780\n" done;
  let question = B.alloca_of_list [0xFFuy] in
  let solution_len = 4ul in
  let solution = B.alloca_of_list [0x03uy; 0x02uy; 0x07uy; 0x80uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) BIT_STRING
                   (* ASN1 Value*) (Mkbit_string_t 2ul 7ul (B32.of_buffer 1ul question))
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [BIT_STRING] B.alloca_of_list [0xFFuy]\n" done;
  printf "Solution: %xuy\n" 4ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_BIT_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 34 ----------\n" done;
  printf "raw: ASN.1 Write BIT_STRING 1 0003 0303010002\n" done;
  let question = B.alloca_of_list [0x00uy; 0x03uy] in
  let solution_len = 5ul in
  let solution = B.alloca_of_list [0x03uy; 0x03uy; 0x01uy; 0x00uy; 0x02uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) BIT_STRING
                   (* ASN1 Value*) (Mkbit_string_t 3ul 1ul (B32.of_buffer 2ul question))
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [BIT_STRING] B.alloca_of_list [0x00uy; 0x03uy]\n" done;
  printf "Solution: %xuy\n" 5ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_BIT_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 35 ----------\n" done;
  printf "raw: ASN.1 Write BIT_STRING 0  030100\n" done;
  let question = B.alloca_of_list [] in
  let solution_len = 3ul in
  let solution = B.alloca_of_list [0x03uy; 0x01uy; 0x00uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) BIT_STRING
                   (* ASN1 Value*) (Mkbit_string_t 1ul 0ul (B32.of_buffer 0ul question))
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [BIT_STRING] B.alloca_of_list []\n" done;
  printf "Solution: %xuy\n" 3ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_BIT_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 36 ----------\n" done;
  printf "raw: ASN.1 Write BIT_STRING 1 000000000007 030703000000000000\n" done;
  let question = B.alloca_of_list [0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x07uy] in
  let solution_len = 9ul in
  let solution = B.alloca_of_list [0x03uy; 0x07uy; 0x03uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) BIT_STRING
                   (* ASN1 Value*) (Mkbit_string_t 7ul 1ul (B32.of_buffer 6ul question))
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [BIT_STRING] B.alloca_of_list [0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x07uy]\n" done;
  printf "Solution: %xuy\n" 9ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_BIT_STRING dst dst_size (dst_size - answer_len);

  printf "----------- Test 37 ----------\n" done;
  printf "raw: ASN.1 Write OID OID_BASIC_CONSTRAINTS 0603551D13\n" done;
  let question = OID_BASIC_CONSTRAINTS in
  let solution_len = 5ul in
  let solution = B.alloca_of_list [0x06uy; 0x03uy; 0x55uy; 0x1Duy; 0x13uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) OID
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [OID] OID_BASIC_CONSTRAINTS\n" done;
  printf "Solution: %xuy\n" 5ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_OID dst dst_size (dst_size - answer_len);

  printf "----------- Test 38 ----------\n" done;
  printf "raw: ASN.1 Write OID OID_EXTENDED_KEY_USAGE 0603551D25\n" done;
  let question = OID_EXTENDED_KEY_USAGE in
  let solution_len = 5ul in
  let solution = B.alloca_of_list [0x06uy; 0x03uy; 0x55uy; 0x1Duy; 0x25uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) OID
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [OID] OID_EXTENDED_KEY_USAGE\n" done;
  printf "Solution: %xuy\n" 5ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_OID dst dst_size (dst_size - answer_len);

  printf "----------- Test 39 ----------\n" done;
  printf "raw: ASN.1 Write OID OID_KEY_USAGE 0603551D0F\n" done;
  let question = OID_KEY_USAGE in
  let solution_len = 5ul in
  let solution = B.alloca_of_list [0x06uy; 0x03uy; 0x55uy; 0x1Duy; 0x0Fuy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) OID
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [OID] OID_KEY_USAGE\n" done;
  printf "Solution: %xuy\n" 5ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_OID dst dst_size (dst_size - answer_len);

  printf "----------- Test 40 ----------\n" done;
  printf "raw: ASN.1 Write OID OID_DIGEST_SHA256 0609608648016503040201\n" done;
  let question = OID_DIGEST_SHA256 in
  let solution_len = 11ul in
  let solution = B.alloca_of_list [0x06uy; 0x09uy; 0x60uy; 0x86uy; 0x48uy; 0x01uy; 0x65uy; 0x03uy; 0x04uy; 0x02uy; 0x01uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) OID
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [OID] OID_DIGEST_SHA256\n" done;
  printf "Solution: %xuy\n" 11ul solution done;
  printf "Answer  : %xuy\n" answer_len answer   done;

  mbedtls_parse_OID dst dst_size (dst_size - answer_len);

  HST.pop_frame ();
  printf "End Test\n" done;
  C.EXIT_SUCCESS
#pop-options
