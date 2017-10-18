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
  imports Main Set  "../model/Model" "../model/Syntax"
begin
(*>*)
   
type_synonym PORT = nat
  
type_synonym VECTOR = nat
 
type_synonym CONTROLLER_NAME = nat
  
datatype FORMAT = FINVALID | FEMPTY | FVECTOR | FMEMWRITE
  
record IRQ = 
  format :: FORMAT
  irq :: "PORT \<times> VECTOR"
    
definition NULL_IRQ :: IRQ
  where "NULL_IRQ = \<lparr>format = FINVALID, irq=(0, 0) \<rparr>"  
  
record CONTROLLER_CLASS =
  in_port_num :: nat
  out_port_num :: nat
  mapValid :: "(IRQ \<Rightarrow> IRQ set) set"

(* Configuration of a controller *)  
record CONTROLLER =
  map      :: "IRQ \<Rightarrow> IRQ set"
 
(* Interconnect of the system + each controller with a class *)
record SYSTEM =
  controller :: "CONTROLLER_NAME \<Rightarrow> (CONTROLLER \<times> CONTROLLER_CLASS) set"
  net :: "CONTROLLER_NAME \<Rightarrow> nat \<Rightarrow> (CONTROLLER_NAME \<Rightarrow> nat) set"
  
(* valid system = all ports wired, all controller in valid state + ...*)
(* lift to decoding net, assuming valid *)
(* look at decoding net to verify *)
(* assuming system is valid, configuration update \<Rightarrow> system valid *)  
  
(* Arguments that do not produce an empty set, see dom *)
definition
  doms :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set" where
  "doms m = {a. m a \<noteq> {}}"

definition ioapic_mapvalid_indiv :: "IRQ \<Rightarrow> IRQ set"
  where "ioapic_mapvalid_indiv x = {}"
    
definition ioapic_mapvalid_indiv_test :: "(IRQ \<Rightarrow> IRQ set) \<Rightarrow> bool"
  where "ioapic_mapvalid_indiv_test x = True"    

definition ioapic_mapvalid_indiv_dom_valid :: "IRQ set \<Rightarrow> bool"
    where "ioapic_mapvalid_indiv_dom_valid xs  \<longleftrightarrow>  (\<forall>x \<in> xs. format x = FEMPTY)"

definition ioapic_mapvalid_indiv_test_2 :: "(IRQ \<Rightarrow> IRQ set) \<Rightarrow> bool"
  where "ioapic_mapvalid_indiv_test_2 x = ioapic_mapvalid_indiv_dom_valid (doms x)"    
    
definition ioapic_mapvalid :: "(IRQ \<Rightarrow> IRQ set) set"
  where "ioapic_mapvalid = {x. ioapic_mapvalid_indiv_test x}"
    
 (* ( ((format ini)   = FEMPTY   \<and> (fst (irq ini)) < 24) \<and> 
                                      ((format outi) = FVECTOR)  \<and> (snd (irq outi)) \<ge> 32 \<and> (snd (irq outi)) < 235 )" *)
                               