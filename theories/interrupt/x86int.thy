(*

Copyright (c) 2018, ETH Zurich
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

(*
 Contains definitions that are common to multiple controllers on the 
 x86 platform, for instance the I/OAPIC and IOMMU have a the same
 destination mode/format fields.

 Based on intel programmers manual and 
 "Intel \<registered> Virtualization Technology for Directed I/O", October 2014
*)

theory x86int
imports
  interrupt Main "HOL-Word.Word" "HOL-Word.WordBitwise"
begin

(* Delivery Mode *)
datatype DLM = DLMFIXED  | DLMLOWPRIO | DLMSMI | DLMNMI | DLMINIT | DLMEXTINT

(* Destination Mode *)
datatype DM = DMPHYS | DMLOGICAL

(* Trigger Mode *)
datatype TRIGGERM = TRIGGERMEDGE | TRIGGERMLEVEL

type_synonym word8 = "8 word"
type_synonym word4 = "4 word"

(* Encode Destination mode and the dest field (the dest field interpretation
   depends on the destination mode *)
datatype DMDEST = DMPHYS word4 | DMLOGICAL word8

(* IOAPIC Redirection table entry, see 82093AA Datasheet *)
record IOREDTBL_ENTRY =
  dest :: DMDEST
  mask :: bool
  trigger :: TRIGGERM
  delmode :: DLM
  remote_irr :: bool (* Read only *)
  intpol_high :: bool (* true=active high *)
  delivs :: bool (* Read only *)
  vector :: nat

(* This is for the original IOAPIC that has an 8 bit destination *)
definition ioredtbl_entry_well_formed :: "IOREDTBL_ENTRY \<Rightarrow> bool"
  where "ioredtbl_entry_well_formed iot \<longleftrightarrow> (vector iot) < 256"

definition tset :: "nat set"
  where "tset = {}"

definition to_indexset :: "word8 \<Rightarrow> nat set"
  where "to_indexset w = {x. (w !! x) }"

lemma "to_indexset 255 = {7,6,5,4,3,2,1,0}"
  using bin_nth_Bit0 bin_nth_Bit1 by (simp add:to_indexset_def, auto)

lemma bit_set_bound: "w !! n \<longrightarrow> n < 8"
  for w :: "8 word"
proof -
  have L1: "size w \<le> 8"
    by(simp only:word_size, auto)

  have L2: "w !! n \<longrightarrow> n < size w"
    by(simp add:test_bit_size)

  show ?thesis
    using L1 L2 less_trans by auto
qed

lemma to_indexset_bound: "\<forall> inp. to_indexset inp \<subseteq> {x. x < 8}"
  using bit_set_bound by (simp add: to_indexset_def, auto)
  
(* Turns a IOREDTBL_ENTRY at index i to a IRQ, Source: Intel 10.6.2.1 *)
definition ioredtbl_entry_to_irq_dest :: "IOREDTBL_ENTRY \<Rightarrow> IRQ set"
  where "ioredtbl_entry_to_irq_dest iot = (case (dest iot) of
    DMPHYS x \<Rightarrow> { \<lparr>format = FVECTOR (vector iot), port = unat x\<rparr> } |
    DMLOGICAL ldest \<Rightarrow> {x.\<exists>y \<in> (to_indexset ldest). x = \<lparr> format = FVECTOR (vector iot), port = y \<rparr>})"

(* In physical destination mode, the IOAPIC can address a 4 bit destination *)  
lemma "\<forall>outi \<in> (ioredtbl_entry_to_irq_dest y). (port outi) < 16"
  apply(case_tac "dest y")
   apply(simp add:ioredtbl_entry_to_irq_dest_def, unat_arith, auto)
  apply(simp add:ioredtbl_entry_to_irq_dest_def)
  apply(auto)
  using bit_set_bound to_indexset_def by fastforce
    
end
