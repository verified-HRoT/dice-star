module HaclExample

let hash_example
  (hash: FStar.Buffer.buffer FStar.UInt32.t {FStar.Buffer.length hash = 64})
  (input:FStar.Buffer.buffer FStar.UInt32.t {FStar.Buffer.length input < pow2 125})
  (len  :FStar.UInt32.t{FStar.UInt32.v len = FStar.Buffer.length input})
: FStar.HyperStack.ST.St unit
=
  FStar.HyperStack.ST.push_frame ();
  Hacl.SHA2_512.hash
    hash
    input
    len;
  FStar.HyperStack.ST.pop_frame ();
  ()
