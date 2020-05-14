
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

open FStar.Integers

open ASN1.Test.Helpers

let main ()
: HST.St (C.exit_code)
= HST.push_frame ();
  printf "Start Test\\n" done;

  let dst_size = 100ul in
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
                   (* ASN1 Value*) question
                   (*    dst    *) dst
                   (*    pos    *) dst_size in
  let answer = B.sub dst (dst_size - answer_len) answer_len in
  printf "Question: [{asn1_type}] {question}\\n" done;
  printf "Solution: %xuy\\n" {solution_len} solution done;
  printf "Answer  : %xuy\\n" {solution_len} answer   done;
  printf "-----------------------------\\n" done;
'''

tail_template ='''
  HST.pop_frame ();
  printf "End Test\\n" done;
  C.EXIT_SUCCESS
'''

def to_byte_list (octets):
    byte_list = "["
    i = 0
    while (i < len(tokens[4])):
        octet = tokens[4][i:i+2]
        byte_list += ("0x{}uy; ".format(octet))
        i = i + 2
    byte_list = byte_list[:-2] + "]"
    return (byte_list)

def byte_list_len (byte_list):
    return "{}ul".format(len(byte_list.split(";")))

if __name__ == "__main__":
    test_suites = "ASN1.test_suites.data"
    test_script = "ASN1.Test.fst"
    no = 0
    with open (test_script, "w+") as out:
        out.write (head_template)

        with open (test_suites, "r") as f:
            for line in f:
                if line == "\n":
                    continue

                no = no + 1
                
                line = line.replace("\"", "")
                tokens = line.replace("\"", "").split("\n")[0].split(" ")

                solution = to_byte_list(tokens[4])
                solution_len = byte_list_len(solution)

                out.write (test_template.format(
                    no        = no,
                    raw       = line.strip("\n"),
                    asn1_type = tokens[2],
                    question  = tokens[3],
                    solution_len = solution_len,
                    solution  = solution))
        
        out.write (tail_template)