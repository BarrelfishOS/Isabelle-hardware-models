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
theory interrupt
  imports Main Set "HOL-Library.Nat_Bijection"  "../model/Model" "../model/Syntax" 
begin
(*>*)
  
type_synonym PORT = nat
type_synonym VECTOR = nat
type_synonym DATA = nat
type_synonym CONTROLLER_NAME = nat
  
datatype FORMAT = FINVALID | FEMPTY | FVECTOR "nat" | FMEMWRITE "nat" "nat"
  
record IRQ = 
  format :: FORMAT
  port :: PORT
    
definition NULL_IRQ :: IRQ
  where "NULL_IRQ = \<lparr>format = FINVALID, port=0\<rparr>"  
  
record CONTROLLER_CLASS =
  in_port_num :: nat
  out_port_num :: nat
  map_valid :: "(IRQ \<Rightarrow> IRQ set) set"




(*
definition extend_map "IRQ \<Rightarrow> (IRQ, IRQ set) \<Rightarrow> (IRQ \<Rightarrow> IRQ set)"
  where "extend_map A B = {\<lambda> x.  *)

(* Configuration of a controller *)  
record CONTROLLER =
  map      :: "IRQ \<Rightarrow> IRQ set"

definition replace_map :: "CONTROLLER \<Rightarrow> IRQ \<Rightarrow> IRQ set \<Rightarrow> CONTROLLER"
  where "replace_map orig new_inp new_out = orig \<lparr> map := (\<lambda>i. (if i = new_inp then new_out else (map orig) i)) \<rparr>"  

definition replace_map_ctrl :: "(CONTROLLER \<times> CONTROLLER_CLASS) \<Rightarrow> IRQ \<Rightarrow> IRQ set \<Rightarrow> (CONTROLLER \<times> CONTROLLER_CLASS)"
  where "replace_map_ctrl orig new_inp new_out = (replace_map (fst orig) new_inp new_out, snd orig)"  
 
(* Interconnect of the system + each controller with a class *)
record SYSTEM =
  controller :: "CONTROLLER_NAME \<Rightarrow> (CONTROLLER \<times> CONTROLLER_CLASS)"
  net :: "CONTROLLER_NAME \<Rightarrow> nat \<Rightarrow> (CONTROLLER_NAME \<times> nat) set"

(* An identity mapped no broadcasting net *)
definition ident_net :: "CONTROLLER_NAME \<Rightarrow> nat \<Rightarrow> (CONTROLLER_NAME \<times> nat) set"
  where "ident_net cn inp = {(cn, inp)}"

(* In system at controller name, replace its mapping from new_inp to new_outp *)
definition replace_system :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> IRQ \<Rightarrow> IRQ set \<Rightarrow> SYSTEM"
  where "replace_system orig name new_inp new_out = orig \<lparr>
      controller := (controller orig)(name := replace_map_ctrl ((controller orig)name) new_inp new_out)
    \<rparr>"
  
(* look at decoding net to verify *)
(* assuming system is valid, configuration update \<Rightarrow> system valid *)  

(* IRQ is of format FMEMWRITE *)
definition irq_is_memwrite :: "IRQ \<Rightarrow> bool"
  where "irq_is_memwrite x = (case format x of FMEMWRITE a b \<Rightarrow> True | _ \<Rightarrow> False)"
(* IRQ valid *)
definition irq_is_valid :: "IRQ \<Rightarrow> bool"
  where "irq_is_memwrite x = (case format x of FINVALID a b \<Rightarrow> False | _ \<Rightarrow> True)"


(* Arguments that do not produce an empty set, see dom *)
definition doms :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set" where
  "doms m = {a. m a \<noteq> {}}"
  
(* Get  the actual configuration of a controller name *)   
definition sys_ctrl_act_conf :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> (IRQ \<Rightarrow> IRQ set)"
  where "sys_ctrl_act_conf s cn = map (fst ((controller s) cn))"
   
(* Get the set valid configuration of a controller name *)    
definition sys_ctrl_valid_conf :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> ((IRQ \<Rightarrow> IRQ set) set)"
  where "sys_ctrl_valid_conf s cn = (map_valid (snd ((controller s) cn)))"
    
(* Check if c has a valid config in s *)
definition sys_ctrl_valid :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> bool"
  where "sys_ctrl_valid s cn = ((sys_ctrl_act_conf s cn) \<in> (sys_ctrl_valid_conf s cn))"
 
(* Check if a system is in a valid state *)
definition sys_valid :: "SYSTEM \<Rightarrow> bool"
  where "sys_valid s = (\<forall> c. sys_ctrl_valid s c)" 


(* lift to decoding net, assuming valid *)
    
(* this does the port+vector/memaddr to natural magic *)
definition irq_format_nat_encode :: "FORMAT \<Rightarrow> nat" where
  "irq_format_nat_encode x = (case x of FINVALID \<Rightarrow> prod_encode (0,0) | FEMPTY \<Rightarrow> prod_encode (1,0)
 | FVECTOR a  \<Rightarrow> prod_encode (2,a) | FMEMWRITE a b \<Rightarrow> prod_encode (3, prod_encode (a,b) ))"

(* If it can't be mapped, it will return FINVALID *)
definition irq_format_nat_decode :: "nat \<Rightarrow> FORMAT" where
  "irq_format_nat_decode x = ( if 
   fst (prod_decode x) = 1 then FEMPTY else if fst (prod_decode x) = 2 then (FVECTOR (snd (prod_decode x))) else if
   fst (prod_decode x) = 3 then (FMEMWRITE (fst (prod_decode (snd (prod_decode x)))) (snd (prod_decode (snd (prod_decode x))))) else FINVALID)"

lemma format_enc_inv: "irq_format_nat_decode(irq_format_nat_encode x) = x"
  apply(simp add:irq_format_nat_encode_def add:irq_format_nat_decode_def)
  by (smt FORMAT.exhaust FORMAT.simps(15) FORMAT.simps(16) FORMAT.simps(17) FORMAT.simps(18) fst_conv numeral_1_eq_Suc_0 numeral_One numeral_eq_iff prod_encode_inverse semiring_norm(83) semiring_norm(86) semiring_norm(89) snd_conv zero_neq_numeral)
  
definition irq_nat_encode :: "IRQ \<Rightarrow> nat" where
  "irq_nat_encode i = prod_encode ((irq_format_nat_encode (format i)), port i)"

definition irq_nat_decode :: "nat \<Rightarrow> IRQ" where
  "irq_nat_decode n = \<lparr>format = irq_format_nat_decode (fst (prod_decode n)), port = (snd (prod_decode n)) \<rparr>"

lemma irq_enc_inv: "irq_nat_decode(irq_nat_encode x) = x"
  by(simp add:irq_nat_encode_def add:irq_nat_decode_def add:format_enc_inv)


(* iis is an output set at c,  perform net lookup to give back input interrupts at controllers (as set)*)
definition net_set_translate :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> IRQ set \<Rightarrow> (CONTROLLER_NAME \<times> IRQ) set"
  where "net_set_translate s c iis = \<Union> { {(fst y, \<lparr> format = (format x), port = (snd y)\<rparr>) | y. y \<in> ((net s) c (port x))} | x. x \<in> iis }"

(* A set of input interrupts translated to a a name set *)
definition irq_set_to_name_set :: "(CONTROLLER_NAME \<times> IRQ) set \<Rightarrow> name set"
  where "irq_set_to_name_set is = { (fst a, irq_nat_encode (snd a)) | a. a \<in> is}"

(* Apply net translation, then translate to names *)
definition conf_to_translate_mod_conf :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> (IRQ \<Rightarrow> IRQ set) \<Rightarrow> IRQ \<Rightarrow> name set"
  where "conf_to_translate_mod_conf s cn conf i = irq_set_to_name_set (net_set_translate s cn (conf i))"

definition conf_to_translate_mod :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> IRQ \<Rightarrow> name set"
  where "conf_to_translate_mod s cn ini = 
            irq_set_to_name_set (net_set_translate s cn ((sys_ctrl_act_conf s cn) ini))"

definition conf_to_translate :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> (addr \<Rightarrow> name set)"
  where "conf_to_translate s cn = 
            (\<lambda>addr. conf_to_translate_mod s cn (irq_nat_decode addr))
         "
    
definition mk_node :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> node"
  where "mk_node s cn = \<lparr>accept = {}, translate = conf_to_translate s cn \<rparr>"

(* ------------------------------------------------------------------------- *)  
subsection "Lifting Result"
(* ------------------------------------------------------------------------- *)   
(* definition config_change :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> SYSTEM"
  where "config_change sys ctrl = replace_system sys ctrl \<lparr>format = FEMPTY, port = 0 \<rparr>" *)



(*  definition config_change_node :: "" *)

(* assume change is in set of mapvalid *)
(* lemma blu : "mk_node S (config_change Ctrl) = config_change_node (mk_node S Ctrl)" *)

(* lemma blu: "mk_net  *)
    
definition mk_net :: "SYSTEM \<Rightarrow> net"
  where "mk_net s = (\<lambda>nodeid. mk_node s nodeid)"

(* modify node such that addr will now map to name set *)
definition replace_node :: "node \<Rightarrow> addr \<Rightarrow> name set \<Rightarrow> node" where
  "replace_node n inp out = n \<lparr> translate := (\<lambda> a. if a=inp then out else translate n a) \<rparr>"

(* assume: inirq \<rightarrow> has no mapping at ctrl
   ctrl is a nat, that represents the controller id in the interrupt net and in the decoding net  *)
lemma lifts: 
  (* ctrl exists *)
  assumes ctrl_exists: "((controller sys) ctrl) = ctrlx" 
  (* No mapping for inirq at ctrl exists *)
  and no_init_mapping: "(map (fst ctrlx)) inirq = {}"         
  (* Assume an identity net function *)
  and ident_net: "net sys = ident_net" 
  (* and sutppo_net: "net sys = (\<lambda> _. \<lambda> _. {})"  *)
  (* Assume the interrupt to be replaced not to be valid *)
  and inirq_valid: "irq_is_valid inirq"
  (* Assume that inirq \<rightarrow> outirq is in mapvalid? *)
  shows "mk_node (replace_system sys ctrl inirq {\<lparr>format = outformat, port = outport\<rparr>}) ctrl =
         replace_node (mk_node sys ctrl) (irq_nat_encode inirq) {(outport, irq_format_nat_encode outformat)}"
proof -
  have "mk_node (replace_system sys ctrl inirq {\<lparr>format = outformat, port = outport\<rparr>}) ctrl =
 \<lparr>accept = {}, translate = conf_to_translate (replace_system sys ctrl inirq {\<lparr>format = outformat, port = outport\<rparr>}) ctrl\<rparr> "
    by(simp add:mk_node_def)

  have "conf_to_translate (replace_system sys ctrl inirq {\<lparr>format = outformat, port = outport\<rparr>}) ctrl =
        (\<lambda>addr. conf_to_translate_mod (replace_system sys ctrl inirq {\<lparr>format = outformat, port = outport\<rparr>}) ctrl (irq_nat_decode addr))"
    by(simp add:conf_to_translate_def)

  have "(\<lambda>addr. conf_to_translate_mod (replace_system sys ctrl inirq {\<lparr>format = outformat, port = outport\<rparr>}) ctrl (irq_nat_decode addr)) =
    X"
    apply(simp add:conf_to_translate_mod_def)
    apply(simp add:irq_set_to_name_set_def)
    apply(simp add:sys_ctrl_act_conf_def)
    apply(simp add:replace_system_def)
    apply(simp add:replace_map_ctrl_def)
    apply(simp add:replace_map_def)
    apply(simp add:net_set_translate_def)
    apply(simp add:ident_net add:ident_net_def)
    

 


  show ?thesis
    apply(simp_all add:ctrl_exists add:no_init_mapping add:ident_net add:inirq_valid
     add:replace_system_def
     add:replace_node_def add:mk_node_def add:replace_map_def  add:sys_ctrl_act_conf_def
     add:conf_to_translate_def add:conf_to_translate_mod_def add: net_set_translate_def
     add:replace_map_ctrl_def
     (* add:irq_nat_encode_def add:irq_nat_decode_def add:irq_format_nat_encode_def add:irq_format_nat_decode_def*)
     add:irq_set_to_name_set_def add:irq_enc_inv)
    
    
  
qed
  
  
  
 
  
  
  


    
  
end