#!/usr/bin/python3
import argparse

head_template ='''module ASN1.Test

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
  printf "Start Test\\n" done;

  let dst_size = 500ul in
  let dst = B.alloca 0x00uy dst_size in
'''

test_template ='''
  printf "----------- Test {no} ----------\\n" done;
  printf "raw: {raw}\\n" done;
  let question = {question} in
  let solution_len = {solution_len} in
  let solution = B.alloca_of_list {solution} in
  let answer_len = serialize32_asn1_TLV_backwards_of_type
                   (* ASN1 Type *) {asn1_type}
                   (* ASN1 Value*) {question_to_write}
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [{asn1_type}] {question}\\n" done;
  printf "Solution: %xuy\\n" {solution_len} solution done;
  printf "Answer  : %xuy\\n" answer_len answer   done;

  mbedtls_parse_{asn1_type} dst dst_size (dst_size - answer_len);
'''

tail_template ='''
  HST.pop_frame ();
  printf "End Test\\n" done;
  C.EXIT_SUCCESS
#pop-options
'''

def to_byte_list (octets):
    assert (octets[0] == '"' and octets[-0] == '"')
    octets = octets[1:-1]
    byte_list = "["
    i = 0
    while (i < len(octets)):
        octet = octets[i:i+2]
        byte_list += ("0x{}uy; ".format(octet))
        i = i + 2
    if i == 0:
        byte_list = byte_list + "]"
    else:
        byte_list = byte_list[:-2] + "]"
    return (byte_list)

def byte_list_len (byte_list):
    if byte_list == "[]":
        return "0ul"
    else:
        return "{}ul".format(len(byte_list[1:-1].split(";")))


parser = argparse.ArgumentParser(description='ASN.1 Test Script Generator')
parser.add_argument("--target",type=str,help="Test target",default="asn1")
parser.add_argument("--tests",type=str,help="Test suites",default="ASN1.test_suites.data")
parser.add_argument("--output",type=str,help="Generated test script",default="ASN1.Test.fst")

def generate_asn1_test(test_suites, test_script):
    no = 0
    with open (test_script, "w+") as out:
        out.write (head_template)

        with open (test_suites, "r") as f:
            for line in f:
                if line == "\n":
                    continue

                no = no + 1

                line = line
                tokens = line.split("\n")[0].split(" ")

                if tokens[2] == "OCTET_STRING":
                    solution = to_byte_list(tokens[4])
                    solution_len = byte_list_len(solution)
                    question = to_byte_list(tokens[3])
                    question_len = byte_list_len(question)

                    out.write (test_template.format(
                        no        = no,
                        raw       = line.replace('"',"").replace("\n",""),
                        asn1_type = tokens[2],
                        question  = "B.alloca_of_list {}".format(question),
                        question_to_write = "(|{len}, B32.of_buffer {len} question|)".format(len = question_len),
                        solution_len = solution_len,
                        solution  = solution))

                elif tokens[2] == "BIT_STRING":
                        solution = to_byte_list(tokens[5])
                        solution_len = byte_list_len(solution)
                        question = to_byte_list(tokens[4])
                        question_len = byte_list_len(question)
                        out.write (test_template.format(
                        no        = no,
                        raw       = line.replace('"',"").replace("\n",""),
                        asn1_type = tokens[2],
                        question  = "B.alloca_of_list {}".format(question),
                        question_to_write = "(Mkbit_string_t {len} {unused_bits} (B32.of_buffer {octets_len} question))".format(len = str(int(question_len.replace("ul", "")) + 1) + "ul",
                                                                                                                               unused_bits = tokens[3] + "ul",
                                                                                                                               octets_len = question_len),
                        solution_len = solution_len,
                        solution  = solution))

                elif tokens[2] == "OID":
                    solution = to_byte_list(tokens[4])
                    solution_len = byte_list_len(solution)
                    out.write (test_template.format(
                        no        = no,
                        raw       = line.replace('"',"").replace("\n",""),
                        asn1_type = tokens[2],
                        question  = tokens[3],
                        question_to_write = "question",
                        solution_len = solution_len,
                        solution  = solution))

                else:
                    solution = to_byte_list(tokens[4])
                    solution_len = byte_list_len(solution)
                    out.write (test_template.format(
                        no        = no,
                        raw       = line.replace('"',"").replace("\n",""),
                        asn1_type = tokens[2],
                        question  = tokens[3],
                        question_to_write = "question",
                        solution_len = solution_len,
                        solution  = solution))

        out.write (tail_template)

def generate_riot_test(test_suites, test_script):
    with open (test_script, "w+") as out:
        with open (test_suites, "r") as f:
            out.write (f.read())

if __name__ == "__main__":
    args = parser.parse_args()

    if (args.target == "asn1"):
        generate_asn1_test("ASN1.test_suites.data", "ASN1.Test.fst")
    elif(args.target == "riot"):
        generate_riot_test("RIoT.test_suites.data", "RIoT.Test.fst")
    else:
        print("No tests for target {}".format(args.target))
