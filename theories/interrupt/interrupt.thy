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

(* ------------------------------------------------------------------------- *)  
subsection "Datatype definitions"
(* ------------------------------------------------------------------------- *)   

type_synonym PORT = nat
type_synonym VECTOR = nat
type_synonym DATA = nat
type_synonym CONTROLLER_NAME = nat
  
datatype FORMAT = FINVALID | FEMPTY | FVECTOR "nat" | FMEMWRITE "nat" "nat"
  
record IRQ = 
  format :: FORMAT
  port :: PORT
  
record CONTROLLER_CLASS =
  in_port_num :: nat
  out_port_num :: nat
  map_valid :: "(IRQ \<Rightarrow> IRQ set) set"

(* Configuration of a controller *)  
record CONTROLLER =
  map      :: "IRQ \<Rightarrow> IRQ set"

(* Interconnect of the system + each controller with a class *)
record SYSTEM =
  controller :: "CONTROLLER_NAME \<Rightarrow> (CONTROLLER \<times> CONTROLLER_CLASS)"
  net :: "CONTROLLER_NAME \<Rightarrow> nat \<Rightarrow> (CONTROLLER_NAME \<times> nat) set"


(* ------------------------------------------------------------------------- *)  
subsection "IRQ / IRQ Format definitions"
(* ------------------------------------------------------------------------- *)   
definition irq_is_empty :: "IRQ \<Rightarrow> bool"
  where "irq_is_empty x = (case format x of FEMPTY \<Rightarrow> True | _ \<Rightarrow> False)"

definition irq_is_vector :: "IRQ \<Rightarrow> bool"
  where "irq_is_vector x = (case format x of FVECTOR _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition irq_is_memwrite :: "IRQ \<Rightarrow> bool"
  where "irq_is_memwrite x = (case format x of FMEMWRITE a b \<Rightarrow> True | _ \<Rightarrow> False)"

definition irq_format_valid :: "FORMAT \<Rightarrow> bool"
  where "irq_format_valid x = (case x of FINVALID \<Rightarrow> False | _ \<Rightarrow> True)"

definition NULL_IRQ :: IRQ
  where "NULL_IRQ = \<lparr>format = FINVALID, port=0\<rparr>"  

(* IRQ valid *)
definition irq_valid :: "IRQ \<Rightarrow> bool"
  where "irq_valid x = irq_format_valid (format x)"

(* ------------------------------------------------------------------------- *)  
subsection "IRQ / IRQ Format nat encoding and proof of bijection"
(* ------------------------------------------------------------------------- *)   
(* define port+formatr to natural bijection *)
definition irq_format_nat_encode :: "FORMAT \<Rightarrow> nat" where
  "irq_format_nat_encode x = (case x of 
    FINVALID \<Rightarrow> 0 |
    FEMPTY \<Rightarrow> 1 |
    FVECTOR a  \<Rightarrow> 2 + prod_encode (0,a) |
    FMEMWRITE a b \<Rightarrow> 2 + prod_encode (1+a, b)
    )"

definition irq_format_nat_decode :: "nat \<Rightarrow> FORMAT" where
  "irq_format_nat_decode x = (
        if x = 0 then FINVALID
   else if x = 1 then FEMPTY
   else if fst (prod_decode (x-2)) = 0 then (FVECTOR (snd (prod_decode (x-2))))
   else FMEMWRITE ((fst (prod_decode (x-2)))-1) (snd (prod_decode (x-2)))
   )"

definition irq_nat_encode :: "IRQ \<Rightarrow> nat" where
  "irq_nat_encode i = prod_encode ((irq_format_nat_encode (format i)), port i)"

definition irq_nat_decode :: "nat \<Rightarrow> IRQ" where
  "irq_nat_decode n = \<lparr>format = irq_format_nat_decode (fst (prod_decode n)),
     port = (snd (prod_decode n)) \<rparr>"

lemma format_enc_inv[simp]: "irq_format_nat_decode(irq_format_nat_encode x) = x"
  by(case_tac x, simp_all add:irq_format_nat_encode_def irq_format_nat_decode_def)  

lemma format_dec_inv_0:
  assumes e1: "x=0"
  shows "irq_format_nat_encode(irq_format_nat_decode x) = x"
  by(simp add:e1 irq_format_nat_encode_def irq_format_nat_decode_def)

lemma format_dec_inv_1:
  assumes e1: "x=1"
  shows "irq_format_nat_encode(irq_format_nat_decode x) = x"
  by(simp add:e1 irq_format_nat_encode_def irq_format_nat_decode_def)

lemma format_dec_inv_2:
  assumes e1: "x=2"
  shows "irq_format_nat_encode(irq_format_nat_decode x) = x"
    apply(simp add:irq_format_nat_encode_def irq_format_nat_decode_def e1)
    by(metis prod.collapse prod_decode_inverse)

lemma format_dec_inv_rest:
  assumes e1: "(x :: nat) > 2"
  shows "irq_format_nat_encode(irq_format_nat_decode x) = x"
  
proof -
  from e1 have "Suc (Suc (x - 2)) = x"
    by(simp)

  thus ?thesis
    apply(simp add:irq_format_nat_encode_def irq_format_nat_decode_def)
    by(metis prod.collapse prod_decode_inverse)
qed
    

lemma format_dec_inv[simp]:
  shows "irq_format_nat_encode(irq_format_nat_decode x) = x"
proof cases
  assume "x=0"
  thus ?thesis
    by(simp add:format_dec_inv_0)
next
  assume nc0: "(x :: nat) \<noteq>0"
  thus ?thesis
  proof cases
    assume "(x :: nat) =1"
    thus ?thesis by(simp add:nc0 format_dec_inv_1)
  next
    assume nc1: "(x :: nat) \<noteq>1"
    thus ?thesis
    proof cases
      assume "(x :: nat) =2"
      thus ?thesis by(simp add:format_dec_inv_2)
    next
      assume nc2: "(x :: nat) \<noteq>2"
      thus ?thesis
      proof -
        have R1: "(x :: nat) > 2"
          using nc0 nc1 nc2 by linarith
        thus ?thesis by(simp add:format_dec_inv_rest)
      qed
    qed
  qed
qed

lemma irq_enc_inv[simp]: "irq_nat_decode(irq_nat_encode x) = x"
  by(simp add:irq_nat_encode_def irq_nat_decode_def)

lemma irq_dec_inv[simp]: "irq_nat_encode(irq_nat_decode x) = x"
  by(simp add:irq_nat_encode_def irq_nat_decode_def)

lemma inj_irq_nat_encode: "inj_on irq_nat_encode A"
  by (rule inj_on_inverseI) (rule irq_enc_inv)

lemma inj_irq_nat_decode: "inj_on irq_nat_decode A"
  by (rule inj_on_inverseI) (rule irq_dec_inv)

lemma surj_irq_nat_encode: "surj irq_nat_encode"
  by (rule surjI) (rule irq_dec_inv)

lemma surj_irq_nat_decode: "surj irq_nat_decode"
  by (rule surjI) (rule irq_enc_inv)

lemma bij_irq_nat_encode: "bij irq_nat_encode"
  by (rule bijI [OF inj_irq_nat_encode surj_irq_nat_encode])

lemma bij_irq_nat_decode: "bij irq_nat_decode"
  by (rule bijI [OF inj_irq_nat_decode surj_irq_nat_decode])

lemma irq_nat_encode_eq: "irq_nat_encode x = irq_nat_encode y \<longleftrightarrow> x = y"
  by (rule inj_irq_nat_encode [THEN inj_eq])

lemma irq_nat_decode_eq: "irq_nat_decode x = irq_nat_decode y \<longleftrightarrow> x = y"
  by (rule inj_irq_nat_decode [THEN inj_eq])

(* ------------------------------------------------------------------------- *)  
subsection "Incremental configuration change of controllers"
(* ------------------------------------------------------------------------- *)   

definition replace_map :: "CONTROLLER \<Rightarrow> IRQ \<Rightarrow> IRQ set \<Rightarrow> CONTROLLER"
  where "replace_map orig new_inp new_out = orig \<lparr> map :=
    (\<lambda>i. (if i = new_inp then new_out else (map orig) i))
   \<rparr>"  

definition replace_map_ctrl :: "(CONTROLLER \<times> CONTROLLER_CLASS) \<Rightarrow> IRQ \<Rightarrow> IRQ set \<Rightarrow>
          (CONTROLLER \<times> CONTROLLER_CLASS)"
  where "replace_map_ctrl orig new_inp new_out = (replace_map (fst orig) new_inp new_out, snd orig)"  
 
(* An identity mapped no broadcasting net *)
definition ident_net :: "CONTROLLER_NAME \<Rightarrow> nat \<Rightarrow> (CONTROLLER_NAME \<times> nat) set"
  where "ident_net cn inp = {(cn, inp)}"

(* In system at controller name, replace its mapping from new_inp to new_outp *)
definition replace_system :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> IRQ \<Rightarrow> IRQ set \<Rightarrow> SYSTEM"
  where "replace_system orig name new_inp new_out = orig \<lparr>
      controller := (controller orig)(name := replace_map_ctrl ((controller orig)name) new_inp new_out)
    \<rparr>"
  

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

   
(* ------------------------------------------------------------------------- *)  
subsection "From IRQ system to decoding net definitions"
(* ------------------------------------------------------------------------- *)   
(* iis is an output set at c,  perform net lookup to give back input interrupts at controllers (as set)*)
definition net_set_translate :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> IRQ set \<Rightarrow> (CONTROLLER_NAME \<times> IRQ) set"
  where "net_set_translate s c iis = \<Union> { {(fst y, \<lparr> format = (format x), port = (snd y)\<rparr>) |
     y. y \<in> ((net s) c (port x))} | x. x \<in> iis }"

(* A set of input interrupts translated to a a name set *)
definition irq_set_to_name_set :: "(CONTROLLER_NAME \<times> IRQ) set \<Rightarrow> name set"
  where "irq_set_to_name_set is = { (fst a, (irq_nat_encode (snd a), {})) | a. a \<in> is}"

(* Apply net translation, then translate to names *)
definition conf_to_translate_mod_conf :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> (IRQ \<Rightarrow> IRQ set) \<Rightarrow> IRQ \<Rightarrow> name set"
  where "conf_to_translate_mod_conf s cn conf i = irq_set_to_name_set (net_set_translate s cn (conf i))"

definition conf_to_translate_mod :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> IRQ \<Rightarrow> name set"
  where "conf_to_translate_mod s cn ini = 
            irq_set_to_name_set (net_set_translate s cn ((sys_ctrl_act_conf s cn) ini))"

definition conf_to_translate :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> (addr \<Rightarrow> name set)"
  where "conf_to_translate s cn = 
            (\<lambda>addr. conf_to_translate_mod s cn (irq_nat_decode (fst addr)))
         "
    
definition mk_node :: "SYSTEM \<Rightarrow> CONTROLLER_NAME \<Rightarrow> node"
  where "mk_node s cn = \<lparr>accept = {}, translate = conf_to_translate s cn \<rparr>"

definition mk_net :: "SYSTEM \<Rightarrow> net"
  where "mk_net s = (\<lambda>nodeid. mk_node s nodeid)"

(* modify node such that addr will now map to name set *)
definition replace_node :: "node \<Rightarrow> nat \<Rightarrow> name set \<Rightarrow> node" where
  "replace_node n inp out = n \<lparr> translate := (\<lambda> a. if (fst a)=inp then out else translate n a) \<rparr>"

(* ------------------------------------------------------------------------- *)  
subsection "Lifting Result"
(* ------------------------------------------------------------------------- *)   


(* TODO: move this into the proof of the lifting lemma *)
lemma lifts_inner : "({(a, (irq_nat_encode b, {})) |a b.
              \<exists>x. (
                \<exists>xa. x = {(ctrl, \<lparr>format = format xa, port = port xa\<rparr>)} \<and>
                xa \<in> (if irq_nat_decode (fst addr) = inirq then {outirq}
                      else CONTROLLER.map (fst (controller sys ctrl)) (irq_nat_decode (fst addr))))
                      \<and> (a, b) \<in> x}) =
    (if (fst addr) = irq_nat_encode inirq then {(ctrl, (irq_nat_encode outirq, {}))}
          else {(aa, (irq_nat_encode b, {})) |aa b. \<exists>x.
          (\<exists>xa. x = {(ctrl, \<lparr>format = format xa, port = port xa\<rparr>)} \<and>
          xa \<in> CONTROLLER.map (fst (controller sys ctrl)) (irq_nat_decode (fst addr)))
          \<and> (aa, b) \<in> x})"
  by(auto, simp add:irq_nat_encode_def)


lemma lifts: 
  (* Assume an identity net function *)
  assumes ident_net: "net sys = ident_net" 
  (* Assume that inirq \<rightarrow> outirq is in mapvalid? *)
  shows "mk_node (replace_system sys ctrl inirq {outirq}) ctrl =
       replace_node (mk_node sys ctrl) (irq_nat_encode inirq) {(ctrl, (irq_nat_encode outirq, {}))}"
proof -
  (* Simplify both side until we apply lemma lifts_inner *)

  (* left side *)
  have L1: "mk_node (replace_system sys ctrl inirq {outirq}) ctrl =
 \<lparr>accept = {}, translate = conf_to_translate (replace_system sys ctrl inirq {outirq}) ctrl\<rparr> "
    by(simp add:mk_node_def)

  have L2: "conf_to_translate (replace_system sys ctrl inirq {outirq}) ctrl =
        (\<lambda>addr. conf_to_translate_mod (replace_system sys ctrl inirq {outirq}) ctrl (irq_nat_decode (fst addr)))"
    by(simp add:conf_to_translate_def)

  (* continue only with translate function *)
  have L3: "(\<lambda>addr. conf_to_translate_mod (replace_system sys ctrl inirq {outirq}) ctrl (irq_nat_decode (fst addr))) =
    (\<lambda>addr. {(a, (irq_nat_encode b, {})) |a b.
              \<exists>x. (\<exists>xa. x = {(ctrl, \<lparr>format = format xa, port = port xa\<rparr>)} \<and> xa \<in>
              (if irq_nat_decode (fst addr) = inirq then {outirq} else
              CONTROLLER.map (fst (controller sys ctrl)) (irq_nat_decode (fst addr)))) \<and> (a, b) \<in> x})"
    apply(simp add:conf_to_translate_mod_def)
    apply(simp add:irq_set_to_name_set_def)
    apply(simp add:sys_ctrl_act_conf_def)
    apply(simp add:replace_system_def)
    apply(simp add:replace_map_ctrl_def)
    apply(simp add:replace_map_def)
    apply(simp add:net_set_translate_def)
    apply(simp add:ident_net add:ident_net_def)
    done

  (* right side *)
  have R1: "replace_node (interrupt.mk_node sys ctrl) (irq_nat_encode inirq)
            {(ctrl, (irq_nat_encode outirq, {}))} = \<lparr>accept = {}, translate =
            \<lambda>a. if (fst a) = irq_nat_encode inirq then {(ctrl, (irq_nat_encode outirq, {}))}
             else translate \<lparr>accept = {}, translate = conf_to_translate sys ctrl\<rparr> a\<rparr>"
    by(simp add:replace_node_def mk_node_def)

  have R21: "translate \<lparr>accept = {}, translate = conf_to_translate sys ctrl\<rparr> =
      (\<lambda>addr. {(a, (irq_nat_encode b, {}))
         |a b. \<exists>x. (\<exists>xa. x = {(ctrl, \<lparr>format = format xa, port = port xa\<rparr>)} \<and>
         xa \<in> CONTROLLER.map (fst (controller sys ctrl)) (irq_nat_decode (fst addr))) \<and> (a, b) \<in> x})"
    by(simp add:conf_to_translate_def conf_to_translate_mod_def irq_set_to_name_set_def 
                  net_set_translate_def ident_net ident_net_def sys_ctrl_act_conf_def)

  show ?thesis 
    by(simp only:R1, simp only:R21, simp add:L1 L2 L3 lifts_inner)
qed
  
end