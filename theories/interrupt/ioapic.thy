(*

Copyright (c) 2017, ETH Zurich
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
  imports interrupt Main Set  "../model/Model" "../model/Syntax"
begin
(*>*)
    
definition ioapic_mapvalid_indiv_dom_valid :: "IRQ set \<Rightarrow> bool"
  where "ioapic_mapvalid_indiv_dom_valid xs  \<longleftrightarrow>  (\<forall>x \<in> xs. format x = FEMPTY)"
    
definition ioapic_mapvalid_indiv_res_valid_one :: "IRQ \<Rightarrow> bool"
  where "ioapic_mapvalid_indiv_res_valid_one outi =  (((format outi) = FVECTOR)  \<and> (snd (irq outi)) \<ge> 32 \<and> (snd (irq outi)) < 235 )"
    
definition ioapic_mapvalid_indiv_res_valid :: "IRQ set \<Rightarrow> bool"
  where "ioapic_mapvalid_indiv_res_valid xs =  (if is_singleton xs then ioapic_mapvalid_indiv_res_valid_one (the_elem xs) else False)"
      
definition ioapic_mapvalid_pred :: "(IRQ \<Rightarrow> IRQ set) \<Rightarrow> bool"
  where "ioapic_mapvalid_pred x = (ioapic_mapvalid_indiv_dom_valid (doms x) \<and> (\<forall>xs. xs \<in> (doms x) \<longleftrightarrow> ioapic_mapvalid_indiv_res_valid (x xs)))"    
    

definition ioapic_mapvalid :: "(IRQ \<Rightarrow> IRQ set) set"
  where "ioapic_mapvalid = {x. ioapic_mapvalid_pred x}"
    
definition ioapic :: "CONTROLLER_CLASS"
  where "ioapic = \<lparr>in_port_num = 24, out_port_num = 8, map_valid = ioapic_mapvalid \<rparr>"
    
end