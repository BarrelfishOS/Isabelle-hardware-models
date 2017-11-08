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

(* Configuration of a controller *)  
record CONTROLLER =
  map      :: "IRQ \<Rightarrow> IRQ set"
 
(* Interconnect of the system + each controller with a class *)
record SYSTEM =
  controller :: "CONTROLLER_NAME \<Rightarrow> (CONTROLLER \<times> CONTROLLER_CLASS) option"
  net :: "CONTROLLER_NAME \<Rightarrow> nat \<Rightarrow> (CONTROLLER_NAME \<times> nat) set"
  
(* look at decoding net to verify *)
(* assuming system is valid, configuration update \<Rightarrow> system valid *)  

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

(* This maps an outgoing IRQ to a node by applying the net function *)
definition out_irq_to_name :: "SYSTEM \<Rightarrow> IRQ \<Rightarrow> name set" where
  "out_irq_to_name s i = List.map_project (\<lambda>p. (Some (irq_nat_encode(snd p)))) ((net s) i)"

(*
definition conf_to_translate :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> (addr \<Rightarrow> name set)"
  where "conf_to_translate s c = (\<lambda>addr. { List.map_project ( ((fst (controller s)) c)) (irq_nat_decode addr)})"
*)

definition conf_to_translate_p1 :: "SYSTEM \<Rightarrow> (IRQ \<Rightarrow> IRQ set) \<Rightarrow> IRQ option \<Rightarrow> name set" 
  where "conf_to_translate_p1 s conf i = {}"

definition conf_to_translate :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> (addr \<Rightarrow> name set)"
  where "conf_to_translate s c = (case ((controller s) c) of Some ctrl \<Rightarrow> (\<lambda>addr. conf_to_translate_p1 s (map (fst ctrl)) (irq_nat_decode addr)) | None \<Rightarrow> (\<lambda>_. {}))"
    
definition mk_node :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> node"
  where "mk_node s c = (case (sys_ctrl_act_conf s c) of None \<Rightarrow> empty_node |
         Some conf \<Rightarrow> \<lparr>accept = {}, translate = conf_to_translate conf \<rparr>)"
    
definition mk_net :: "SYSTEM \<Rightarrow> net"
  where "mk_net s = empty_net"
    
  
end