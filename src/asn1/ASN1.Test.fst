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

open FStar.Integers

open ASN1.Test.Helpers

let main ()
: HST.St (C.exit_code)
= HST.push_frame ();
  printf "Start Test\n" done;

  let dst_size = 100ul in
  let dst = B.alloca 0x00uy dst_size in

  printf "----------- Test 1 ----------\n" done;
  printf "raw: ASN.1 Write NULL () 0500\n" done;
  let question = () in
  let solution_len = 2ul in
  let solution = B.alloca_of_list [0x05uy; 0x00uy] in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) NULL
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [NULL] ()\n" done;
  printf "Solution: %xuy\n" 2ul solution done;
  printf "Answer  : %xuy\n" 2ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 2 ----------\n" done;
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
  printf "Answer  : %xuy\n" 3ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 3 ----------\n" done;
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
  printf "Answer  : %xuy\n" 3ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 4 ----------\n" done;
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
  printf "Answer  : %xuy\n" 3ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 5 ----------\n" done;
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
  printf "Answer  : %xuy\n" 3ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 6 ----------\n" done;
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
  printf "Answer  : %xuy\n" 3ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 7 ----------\n" done;
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
  printf "Answer  : %xuy\n" 4ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 8 ----------\n" done;
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
  printf "Answer  : %xuy\n" 4ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 9 ----------\n" done;
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
  printf "Answer  : %xuy\n" 4ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 10 ----------\n" done;
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
  printf "Answer  : %xuy\n" 4ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 11 ----------\n" done;
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
  printf "Answer  : %xuy\n" 5ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 12 ----------\n" done;
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
  printf "Answer  : %xuy\n" 5ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 13 ----------\n" done;
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
  printf "Answer  : %xuy\n" 5ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 14 ----------\n" done;
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
  printf "Answer  : %xuy\n" 5ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 15 ----------\n" done;
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
  printf "Answer  : %xuy\n" 6ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 16 ----------\n" done;
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
  printf "Answer  : %xuy\n" 6ul answer   done;
  printf "-----------------------------\n" done;

  printf "----------- Test 17 ----------\n" done;
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
  printf "Answer  : %xuy\n" 6ul answer   done;
  printf "-----------------------------\n" done;

  HST.pop_frame ();
  printf "End Test\n" done;
  C.EXIT_SUCCESS
