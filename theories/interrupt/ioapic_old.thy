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
                               
                              
definition ioapic :: "CONTROLLER_CLASS"
  where "ioapic  = \<lparr> in_port_num = 24, out_port_num = 4, mapValid = ioapic_mapvalid  \<rparr>"
    
 
definition ioapic_add_map :: "IRQ \<Rightarrow> IRQ \<Rightarrow> CONTROLLER \<Rightarrow> CONTROLLER set"
  where "ioapic_add_map iirq oirq c = 
    (if (mapValid c iirq oirq) then
       { \<lparr> inPorts = (inPorts c), outPorts = (outPorts c), mapValid = (mapValid c), 
           map = (map c)(iirq := oirq) \<rparr>  } else UNIV)"
 
lemma "(mapValid c) a b \<Longrightarrow> (\<forall>c' \<in> (ioapic_add_map a b c). (map c' a) = b)"
  by(simp add:ioapic_add_map_def)

lemma "\<not>(mapValid c) a b \<Longrightarrow> ((ioapic_add_map a b c) = UNIV)"
  by(simp add:ioapic_add_map_def)

    
definition irq_to_addr :: "IRQ \<Rightarrow> addr"
  where "irq_to_addr i = ((snd (irq i)) * 1024 + (fst (irq i)))"
    
    
definition irq_to_map :: "SYSTEM \<Rightarrow> IRQ \<Rightarrow> IRQ \<Rightarrow> nat \<Rightarrow> (nat \<times> nat ) set"
  where "irq_to_map s i i2 a = (if \<lparr>format = FEMPTY, irq=(a, 0) \<rparr> = i  then 
                              { (controllers s (fst (irq i2)), irq_to_addr i2) } else {})"
    

definition ioapic_to_node :: "SYSTEM \<Rightarrow> CONTROLLER  \<Rightarrow> node" where
  "ioapic_to_node s c =
    \<lparr> accept = {},
      translate = (\<lambda> a. if a < 24 then irq_to_map s \<lparr>format = FEMPTY, irq=(a, 0) \<rparr> 
                                        (map c \<lparr>format = FEMPTY, irq=(a, 0) \<rparr>) a else {}) \<rparr>" 
    
  
definition replace_entry :: "SYSTEM \<Rightarrow> IRQ \<Rightarrow> IRQ \<Rightarrow>  IRQ  \<Rightarrow> node \<Rightarrow> node"
  where
    "replace_entry s i i2 i3 n = n  \<lparr>
      accept := accept n,
      translate := (\<lambda>va. (if \<lparr>format = FEMPTY, irq=(va, 0) \<rparr> = i then (irq_to_map s i i3 va)  else  (translate n va))) \<rparr>"
    
(* value "ioapic_mapvalid ( out *)
definition test_i :: IRQ
  where  "test_i = \<lparr>format = FEMPTY, irq = (3,2)\<rparr>"
    
definition test_j :: IRQ
  where  "test_j = \<lparr>format = FVECTOR, irq = (4,33)\<rparr>"
    
definition "an_ioapic" :: CONTROLLER
  where "an_ioapic = ioapic {1,2,3} {4,5,6}"
     
value "ioapic_mapvalid test_i test_i"
  
value "mapValid an_ioapic test_i test_i"
  
value "(map an_ioapic)(test_i := test_j)"
    
lemma "(mapValid an_ioapic x y) = False \<Longrightarrow> 
        ioapic_add_map x y an_ioapic = UNIV "
  by(simp add:ioapic_add_map_def)
    
lemma xy: "mapValid an_ioapic test_i test_i = False"    
  by(auto simp :ioapic_def ioapic_mapvalid_def an_ioapic_def test_i_def)
  
    
lemma "ioapic_add_map test_i test_i an_ioapic = UNIV"
  by(simp add:ioapic_add_map_def xy)
    
  
  
    
lemma assumes valid: "(mapValid c) a b"
  shows "ioapic_to_node s ` ioapic_add_map a b c = {replace_entry s a (map c a) b (ioapic_to_node s c)}"
  apply(auto)
  sorry

  
  
  
end