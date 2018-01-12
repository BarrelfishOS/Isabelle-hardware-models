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
 
(* Interconnect of the system + each controller with a class *)
record SYSTEM =
  controller :: "CONTROLLER_NAME \<Rightarrow> (CONTROLLER \<times> CONTROLLER_CLASS) option"
  net :: "CONTROLLER_NAME \<Rightarrow> nat \<Rightarrow> (CONTROLLER_NAME \<times> nat) set"

(* In system at controller name, replace its mapping from new_inp to new_outp *)
definition replace_system :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> IRQ \<Rightarrow> IRQ set \<Rightarrow> SYSTEM"
  where "replace_system orig name new_inp new_out = orig \<lparr>
    net := (net orig),
    controller := (\<lambda>c. (if c = name then (
                   (case ((controller orig) c) of Some cr \<Rightarrow> Some (replace_map (fst cr) new_inp new_out, snd cr) | _ \<Rightarrow> None)
                ) else (controller orig) c))\<rparr>"
  
(* look at decoding net to verify *)
(* assuming system is valid, configuration update \<Rightarrow> system valid *)  

(* IRQ is of format FMEMWRITE *)
definition irq_is_memwrite :: "IRQ \<Rightarrow> bool"
  where "irq_is_memwrite x = (case format x of FMEMWRITE a b \<Rightarrow> True | _ \<Rightarrow> False)"


(* Arguments that do not produce an empty set, see dom *)
definition doms :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set" where
  "doms m = {a. m a \<noteq> {}}"
  
(* Get  the actual configuration of a controller name *)   
definition sys_ctrl_act_conf :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> (IRQ \<Rightarrow> IRQ set) option"
  where "sys_ctrl_act_conf s c = (case controller s c of None \<Rightarrow> None |
         Some the_c \<Rightarrow> Some (map (fst the_c)))"
   
(* Get the set valid configuration of a controller name *)    
definition sys_ctrl_valid_conf :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> ((IRQ \<Rightarrow> IRQ set) set) option"
  where "sys_ctrl_valid_conf s c = (case controller s c of None \<Rightarrow> None | 
         Some the_c \<Rightarrow> Some (map_valid (snd the_c)))"
    
(* Check if c has a valid config in s *)
definition sys_ctrl_valid :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> bool"
  where "sys_ctrl_valid s c = (case (sys_ctrl_act_conf s c) of None \<Rightarrow> True | Some conf \<Rightarrow> 
    case (sys_ctrl_valid_conf s c) of Some valid_confs \<Rightarrow> conf \<in> valid_confs | False)"
 
(* Check if a system is in a valid state *)
(* valid system = all ports wired, all controller in valid state + ...*)
definition sys_valid :: "SYSTEM \<Rightarrow> bool"
  where "sys_valid s = (\<forall> c. c \<in> (dom (controller s)) \<longrightarrow> sys_ctrl_valid s c)"


(* lift to decoding net, assuming valid *)
    
(* this does the port+vector/memaddr to natural magic *)
definition irq_format_nat_encode :: "FORMAT \<Rightarrow> nat" where
  "irq_format_nat_encode x = (case x of FINVALID \<Rightarrow> prod_encode (0,0) | FEMPTY \<Rightarrow> prod_encode (1,0)
 | FVECTOR a  \<Rightarrow> prod_encode (2,a) | FMEMWRITE a b \<Rightarrow> prod_encode (3, prod_encode (a,b) ))"

definition irq_format_nat_decode :: "nat \<Rightarrow> FORMAT option" where
  "irq_format_nat_decode x = (if fst (prod_decode x) = 0 then Some FINVALID else if 
   fst (prod_decode x) = 1 then Some FEMPTY else if fst (prod_decode x) = 2 then Some (FVECTOR (snd (prod_decode x))) else if
   fst (prod_decode x) = 3 then Some (FMEMWRITE (fst (prod_decode (snd (prod_decode x)))) (snd (prod_decode (snd (prod_decode x))))) else None)"

lemma format_enc_inv: "irq_format_nat_decode(irq_format_nat_encode x) = Some x"
  apply(simp add:irq_format_nat_encode_def add:irq_format_nat_decode_def)
  by (smt FORMAT.exhaust FORMAT.simps(15) FORMAT.simps(16) FORMAT.simps(17) FORMAT.simps(18) fst_conv numeral_1_eq_Suc_0 numeral_One numeral_eq_iff prod_encode_inverse semiring_norm(83) semiring_norm(86) semiring_norm(89) snd_conv zero_neq_numeral)

definition irq_nat_encode :: "IRQ \<Rightarrow> nat" where
  "irq_nat_encode i = prod_encode ((irq_format_nat_encode (format i)), port i)"

definition irq_nat_decode :: "nat \<Rightarrow> IRQ option" where
  "irq_nat_decode n = (case (irq_format_nat_decode (fst (prod_decode n))) of (Some fmt) \<Rightarrow> (Some \<lparr>format = fmt,
   port = (snd (prod_decode n)) \<rparr> ) | None \<Rightarrow> None)"

lemma "irq_nat_decode(irq_nat_encode x) = Some x"
  by(simp add:irq_nat_encode_def add:irq_nat_decode_def add:format_enc_inv)


(* iis is an output set at c,  perform net lookup to give back input interrupts at controllers (as set)*)
definition net_set_translate :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> IRQ set \<Rightarrow> (CONTROLLER_NAME \<times> IRQ) set"
  where "net_set_translate s c iis = \<Union> { {(fst y, \<lparr> format = (format x), port = (snd y)\<rparr>) | y. y \<in> ((net s) c (port x))} | x. x \<in> iis }"

(* A set of input interrupts translated to a a name set *)
definition irq_set_to_name_set :: "(CONTROLLER_NAME \<times> IRQ) set \<Rightarrow> name set"
  where "irq_set_to_name_set is = { (fst a, irq_nat_encode (snd a)) | a. a \<in> is}"

(* Apply net translation, then translate to names *)
definition conf_to_translate_mod_conf :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> (IRQ \<Rightarrow> IRQ set) \<Rightarrow> IRQ \<Rightarrow> name set"
  where "conf_to_translate_mod_conf s c conf i = irq_set_to_name_set (net_set_translate s c (conf i))"

(* get rid of option *)
definition conf_to_translate_mod_c :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> IRQ \<Rightarrow> name set"
  where "conf_to_translate_mod_c s c i = (case ((controller s) c) of Some ctrl \<Rightarrow> conf_to_translate_mod_conf s c (map (fst ctrl)) i |
    None \<Rightarrow> {})"

(* get rid of option *)
definition conf_to_translate_mod :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> IRQ option \<Rightarrow> name set"
  where "conf_to_translate_mod s c ini = (case ini of Some i \<Rightarrow>
            conf_to_translate_mod_c s c i
         | None \<Rightarrow> {})"

definition conf_to_translate :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> (addr \<Rightarrow> name set)"
  where "conf_to_translate s c = (case ((controller s) c) of Some ctrl \<Rightarrow>
            (\<lambda>addr. conf_to_translate_mod s c (irq_nat_decode addr))
         | None \<Rightarrow> (\<lambda>_. {}))"
    
definition mk_node :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> node"
  where "mk_node s c = (case (sys_ctrl_act_conf s c) of None \<Rightarrow> empty_node |
         Some conf \<Rightarrow> \<lparr>accept = {}, translate = conf_to_translate s c \<rparr>)"

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
    
  
end