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
theory ioapic
  imports x86int interrupt Main Set  "../model/Model" 
begin
(*>*)

(* Source: 82093AA Datasheet *)

(* ------------------------------------------------------------------------- *)  
subsection "Register level representation of IOAPIC"
(* ------------------------------------------------------------------------- *)   
record IOAPIC =
  max_red_entries :: nat (* The maximum number of supported redirection entries *)
  arb :: nat
  ioredtbl :: "nat \<Rightarrow> IOREDTBL_ENTRY"
   

definition ioapic_well_formed :: "IOAPIC \<Rightarrow> bool" where
  "ioapic_well_formed io \<longleftrightarrow>
    (arb io) < 16 \<and>
    (\<forall>x. x < (max_red_entries io) \<longrightarrow> ioredtbl_entry_well_formed ((ioredtbl io) x)    )"

(* Given a register state of IOAPIC, describe the interrupt mapping *)
definition ioapic_to_map :: "IOAPIC \<Rightarrow> (IRQ \<Rightarrow> IRQ set)"
  where "ioapic_to_map io = (\<lambda>i. 
      if irq_is_empty i \<and> port i < 24  then ioredtbl_entry_to_irq_dest ((ioredtbl io) (port i)) else {})"


(* ------------------------------------------------------------------------- *)  
subsection "Intuitive definitions of IOAPIC"
(* ------------------------------------------------------------------------- *)   
definition ioapic_mapvalid_indiv_dom_valid :: "IRQ set \<Rightarrow> bool"
  where "ioapic_mapvalid_indiv_dom_valid xs  \<longleftrightarrow>  (\<forall>x \<in> xs. format x = FEMPTY)"
    
definition ioapic_mapvalid_indiv_res_valid_one :: "IRQ \<Rightarrow> bool"
  where "ioapic_mapvalid_indiv_res_valid_one outi =  (case format outi of FVECTOR a \<Rightarrow> a \<ge> 32 \<and> a < 23)"
    
definition ioapic_mapvalid_indiv_res_valid :: "IRQ set \<Rightarrow> bool"
  where "ioapic_mapvalid_indiv_res_valid xs =  (if is_singleton xs then ioapic_mapvalid_indiv_res_valid_one (the_elem xs) else False)"
      
definition ioapic_mapvalid_pred :: "(IRQ \<Rightarrow> IRQ set) \<Rightarrow> bool"
  where "ioapic_mapvalid_pred x = (ioapic_mapvalid_indiv_dom_valid (doms x) \<and> (\<forall>xs. xs \<in> (doms x) \<longleftrightarrow> ioapic_mapvalid_indiv_res_valid (x xs)))"    
    

definition ioapic_mapvalid :: "(IRQ \<Rightarrow> IRQ set) set"
  where "ioapic_mapvalid = {x. ioapic_mapvalid_pred x}"
    
definition ioapic :: "CONTROLLER_CLASS"
  where "ioapic = \<lparr>in_port_num = 24, out_port_num = 8, map_valid = ioapic_mapvalid \<rparr>"
    
end