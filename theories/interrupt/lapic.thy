(*

Copyright (c) 2017, 2018, ETH Zurich
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this
   list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright notice,
   this list of conditions and the following disclaimer in the documentation
   and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

(*<*)
theory lapic
  imports interrupt x86int "HOL-Word.Word" "HOL-Word.WordBitwise"
begin
(*>*)

datatype DFR = DFRFLAT | DFRCLUSTER

type_synonym word8 = "8 word"

record LAPIC =
  id :: nat (* Hardware given, physical APIC ID *)
  ldr :: word8 (* Logical destination register *)
  dfr :: DFR (* Destination Format Register *)

(* Local vector table entry *)
record LVT =
  delivery :: DLM
  mask :: bool

(* In LVT entries, lowprio is DLM is not allowed *)
definition lapic_lvt_well_formed :: "LVT \<Rightarrow> bool"
  where "lapic_lvt_well_formed x \<longleftrightarrow> (delivery x) \<noteq> DLMLOWPRIO"
