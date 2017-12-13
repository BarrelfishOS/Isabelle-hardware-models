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
theory Syntax
  imports Equivalence Resolution Model
begin
(*>*)
  
subsection {* Abstract Syntax for Nets *}
text_raw {* \label{sec:isasyntax} *}

text {* This is the abstract syntax, corresponding to the concrete sytax 
        introduced in \autoref{sec:model}.  We do not yet have a parser, and 
        thus models are constructed by hand. *}

text {* A contiguous block of addresses, expressed as a base-limit pair: *}

record block_spec = 
  base    :: genaddr
  limit   :: genaddr
  require :: "property set"
  forbid  :: "property set"


text {* For each syntax item (nonterminal), we have a translation function into
        the abstract semantic model.  Together these define the parse() function 
        of \autoref{sec:reductions}. *}


definition mk_block :: "block_spec \<Rightarrow> addr set"
  where "mk_block s = {(a, p) | a p. (base s) \<le> a \<and> a \<le> (limit s) 
                                \<and> (\<forall>p'\<in> p. p'\<notin> (forbid s))
                                \<and> (\<forall>p'\<in> (require s). p' \<in> p) }"


text {* A single block mapping that maps the specified source block to the given 
        destination node, beginning at the given base address: *}


record map_spec =
  src_block :: block_spec
  dest_node :: nodeid
  dest_base :: genaddr
  propadd   :: "property set"
  propstrip :: "property set"


text {* Map a block without changing its base address: *}

definition block_map :: "block_spec \<Rightarrow> nodeid \<Rightarrow> genaddr \<Rightarrow> map_spec"
  where "block_map blk nd ba = \<lparr> src_block = blk, dest_node = nd, dest_base = ba,
                                 propadd = {}, propstrip = {} \<rparr>"

definition block_map_p :: "block_spec \<Rightarrow> nodeid \<Rightarrow> genaddr \<Rightarrow> property list 
                                        \<Rightarrow> property list \<Rightarrow> map_spec"
  where "block_map_p blk nd ba pa ps  = \<lparr> src_block = blk, dest_node = nd, 
                                          dest_base = ba, propadd = set pa,
                                          propstrip = set ps \<rparr>"


definition direct_map :: "block_spec \<Rightarrow> nodeid \<Rightarrow> map_spec"
  where "direct_map blk nd = \<lparr> src_block = blk, dest_node = nd, 
                              dest_base = (base blk),
                              propadd = {}, propstrip = {} \<rparr>"

definition direct_map_p :: "block_spec \<Rightarrow> nodeid \<Rightarrow> property list 
                                       \<Rightarrow> property list \<Rightarrow> map_spec"
  where "direct_map_p blk nd pa ps = \<lparr> src_block = blk, dest_node = nd, 
                                      dest_base = (base blk),
                                      propadd = set pa, propstrip = set ps \<rparr>"


definition one_map :: "addr \<Rightarrow> nodeid \<Rightarrow> genaddr \<Rightarrow> map_spec"
  where "one_map src nd ba =  \<lparr> src_block = \<lparr> base = (fst src), limit = (fst src), 
                                             require = (snd src), forbid = {} \<rparr>,
                               dest_node = nd, dest_base = ba,
                               propadd = {},propstrip = {} \<rparr>"

definition one_map_p :: "addr \<Rightarrow> nodeid \<Rightarrow> genaddr \<Rightarrow> property list
                              \<Rightarrow> property list \<Rightarrow> map_spec"
  where "one_map_p src nd ba pa ps =  \<lparr> src_block = \<lparr> base = (fst src), 
                                                     limit = (fst src), 
                                                     require = (snd src), 
                                                     forbid = {} \<rparr>,
                                       dest_node = nd, dest_base = ba,
                                       propadd = set pa,propstrip = set ps \<rparr>"


definition mk_map :: "map_spec \<Rightarrow> addr \<Rightarrow> name set"
  where "mk_map s =
    (\<lambda>a. if a \<in> mk_block (src_block s)
      then {
        (dest_node s, (dest_base s + (fst a - base (src_block s))), 
                         (snd a) \<union> (propadd s) - (propstrip s)) }
      else {})"


text {* A finitely-specified decoding node, with a list of blocks to accept 
        locally, and a list of those to translate: *}

record node_spec =
  acc_blocks :: "block_spec list"
  map_blocks :: "map_spec list"
  overlay    :: "nodeid option"


definition empty_spec :: "node_spec"
  where "empty_spec = \<lparr> acc_blocks = [], map_blocks = [], overlay = None \<rparr>"

(*<*)
lemma acc_blocks_empty:
  "acc_blocks empty_spec = []"
  by(simp add:empty_spec_def)
(*>*)

text {* If an overlay node is specified, initialise the map by forwarding all
        addresses to that  node: *}

definition mk_overlay :: "nodeid option \<Rightarrow> node"
  where "mk_overlay ov = \<lparr>
          accept = {},
          translate = (case ov of None \<Rightarrow> \<lambda>_. {} | Some n \<Rightarrow> (\<lambda>a. {(n,a)})) \<rparr>"

(*<*)
lemma accept_mk_overlay:
  "accept (mk_overlay ov) = {}"
  by(simp add:mk_overlay_def)
(*>*)

primrec add_blocks :: "block_spec list \<Rightarrow> node \<Rightarrow> node"
  where "add_blocks [] node = node" |
        "add_blocks (s#ss) node = accept_update (op \<union> (mk_block s)) 
                                                (add_blocks ss node)"

(*<*)
lemma translate_add_blocks:
  "translate (add_blocks bs node) = translate node"
  by(induct bs, simp_all)

lemma add_blocks_overlay:
  "accept (add_blocks bs (mk_overlay ov)) =
   accept (add_blocks bs empty_node)"
  by(induct bs, simp_all add:empty_node_def accept_mk_overlay)
(*>*)

definition add_maps :: "map_spec list \<Rightarrow> node \<Rightarrow> node"
  where "add_maps ss node = translate_update 
                                (\<lambda>t a. \<Union>{mk_map s a |s. s\<in>(set ss) } \<union> t a) 
                                node"
    
primrec add_maps_rec :: "map_spec list \<Rightarrow> node \<Rightarrow> node"
  where "add_maps_rec [] node = node" |
        "add_maps_rec (s#ss) node = translate_update 
                                      (\<lambda>t a. mk_map s a \<union> t a) 
                                      (add_maps_rec ss node)"    


definition remove_maps :: "map_spec list \<Rightarrow> node \<Rightarrow> node"
  where "remove_maps ss node = translate_update 
                                   (\<lambda>t a. t a - \<Union>{mk_map s a |s. s\<in>(set ss) }) 
                                    node"

lemma remove_maps_set_diff: 
  "A - \<Union>{mk_map s a |s. s \<in> set ms \<or> s \<in> set ns} 
    = A - \<Union>{mk_map s a |s. s \<in> set ns} - \<Union>{mk_map s a |s. s \<in> set ms}"
  by(auto)      


lemma remove_maps_append :
  "remove_maps (ms @ ns) node = remove_maps ms (remove_maps ns node)"
  by(auto simp add:remove_maps_def o_def remove_maps_set_diff)    
    
        
definition add_one_map :: "map_spec \<Rightarrow> node \<Rightarrow> node"
  where "add_one_map m n = translate_update (\<lambda>t a. mk_map m a \<union> t a) n"

definition remove_one_map :: "map_spec \<Rightarrow> node \<Rightarrow> node"
  where "remove_one_map m n = n \<lparr> translate := (\<lambda>a. translate n a - mk_map m a) \<rparr>"
    
definition update_one_map :: "map_spec \<Rightarrow> map_spec \<Rightarrow> node \<Rightarrow> node"
  where "update_one_map m m' n = add_one_map m' (remove_one_map m n)"        


lemma update_commute:
  assumes m_distinct: "\<And>a. translate node a \<inter> mk_map m a = {}"
      and n_contained: "\<And>a. mk_map n a \<subseteq> translate node a"
  shows "update_one_map m n (update_one_map n m node) = node"
proof -
  have "\<And>a. translate node a - mk_map n a \<subseteq> translate node a" by(auto)
  hence "\<And>a. (translate node a - mk_map n a) \<inter> mk_map m a 
                    \<subseteq> translate node a \<inter> mk_map m a"
    by(auto)
  also note m_distinct
  finally have "\<And>a.(translate node a - mk_map n a) \<inter> mk_map m a = {}" by(auto)
  with m_distinct
  have "\<And>a. translate node a - mk_map n a - mk_map m a =
             translate node a - mk_map n a"
    by(simp add:Diff_triv)
  with n_contained show ?thesis
    by(simp add:update_one_map_def add_one_map_def remove_one_map_def o_def 
                Un_Diff Un_absorb1)
qed    
    
lemma mk_map_set_append : 
  "mk_map a aa \<union> \<Union>{mk_map s aa |s. s \<in> set ss} 
     = \<Union>{mk_map s aa |s. s \<in> set (a # ss)}"
  by(auto)

lemma mk_map_set_commute : 
  "mk_map a aa \<union> (\<Union>{mk_map s aa |s. s \<in> set ss}\<union> t aa)
     = \<Union>{mk_map s aa |s. s \<in> set (a # ss)} \<union> t aa"
  by(auto)
    
lemma translate_update_append: 
  "translate_update (\<lambda>t aa. \<Union>{mk_map s aa |s. s \<in> set (a # ss)} \<union> t aa) node = 
  translate_update (\<lambda>t aa. mk_map a aa \<union> (\<Union>{mk_map s aa |s. s \<in> set (ss)}) \<union> t aa) node"
  by(simp add:mk_map_set_append)

lemma translate_update_commute:  
  "translate_update (\<lambda>t aa. \<Union>{mk_map s aa |s. s \<in> set (a # ss)} \<union> t aa) node = 
  translate_update (\<lambda>t aa. mk_map a aa \<union> ((\<Union>{mk_map s aa |s. s \<in> set (ss)}) \<union> t aa)) node"
  by(subst mk_map_set_commute, auto)
    
                                                           
lemma add_maps_recursive:
  "add_maps_rec ss node = add_maps ss node"
  apply(induct ss)
  apply(simp_all add:add_maps_def add_maps_rec_def o_def)
  apply(simp add:translate_update_commute[symmetric])
  done


(*<*)
lemma accept_add_maps:
  "accept (add_maps ms node) = accept node"
  by(simp add:add_maps_def)

    
lemma translate_update_chain :
  "translate_update (\<lambda>t a. A \<union> t a) (translate_update (\<lambda>t a. B \<union> t a) node) = 
   translate_update (\<lambda>t a. A \<union> B \<union> t a) node"
  by(simp add:o_def Un_assoc)

lemma add_maps_set_union: 
     "\<Union>{mk_map s a |s. s \<in> set ms \<or> s \<in> set ns} = 
      \<Union>{mk_map s a |s. s \<in> set ms} \<union> \<Union>{mk_map s a |s. s \<in> set ns}"      
  by(auto)    
    
lemma add_maps_set_append :
      "\<Union>{mk_map s a |s. s \<in> set (ms @ ns)} = 
       \<Union>{mk_map s a |s. s \<in> set ms} \<union> \<Union>{mk_map s a |s. s \<in> set ns}"    
  by(auto)
  
lemma add_maps_append_direct:
   "add_maps ms (add_maps ns node) = 
    translate_update (\<lambda>t a. \<Union>{mk_map s a |s. s\<in>(set (ms @ ns)) } \<union> t a) node" 
  by(simp add:add_maps_def o_def Un_assoc[symmetric] add_maps_set_union)
    
lemma add_maps_append:
  "add_maps (ms @ ns) node = add_maps ms (add_maps ns node)"
  by(simp add:add_maps_def o_def  Un_assoc[symmetric] add_maps_set_union)

lemma add_maps_append2 :
  "add_maps (a' @ b' @ c' @ d') node = add_maps (a' @ b') (add_maps (c' @ d') node)"
  by(simp add:add_maps_append)
    
lemma set_commute: "set [a, b] = set [b, a]"
  by(auto)
    
lemma add_maps_list_commute :
  shows   "add_maps [a, b] node = add_maps [b, a] node"
  by(simp only:add_maps_def set_commute)
   
lemma add_maps_commute:
  "add_maps (a @ b) node = add_maps (b @ a) node"   
  by(simp only:add_maps_def add_maps_set_append Un_commute)

lemma add_maps_commute3:
  "add_maps (a @ b @ c) node = add_maps (b @ a @ c) node"   
  apply(simp only:add_maps_def add_maps_set_append)
  apply(simp only:Un_assoc[symmetric])
  apply(simp only: Un_commute)
  done
          
lemma add_maps_append_commute:
   "add_maps a (add_maps b node) = add_maps b (add_maps a node)"
  by(simp add:add_maps_append[symmetric] add_maps_commute)
  
(*>*)


definition mk_node :: "node_spec \<Rightarrow> node"
  where "mk_node s = add_maps (map_blocks s) 
                              (add_blocks (acc_blocks s) 
                              (mk_overlay (overlay s)))"

(*<*)
lemma accept_mk_node:
  "accept (mk_node s) = accept (add_blocks (acc_blocks s) empty_node)"
  by(simp add:mk_node_def accept_add_maps add_blocks_overlay)

lemma maps_blocks_comm:
  "add_maps ms (add_blocks bs node) = add_blocks bs (add_maps ms node)"
proof(simp only: add_maps_recursive[symmetric], induct ms, simp_all)
  fix m ms
  assume IH: "add_maps_rec ms (add_blocks bs node) 
                  = add_blocks bs (add_maps_rec ms node)"

  have tu_au_comm:
    "\<And>f g node. translate_update f (accept_update g node) =
                accept_update g (translate_update f node)"
    by(simp)

  show "translate_update (\<lambda>t a. mk_map m a \<union> t a) 
                         (add_blocks bs (add_maps_rec ms node)) =
        add_blocks bs (translate_update (\<lambda>t a. mk_map m a \<union> t a) 
                                        (add_maps_rec ms node))"
    by(induct bs, simp_all add:tu_au_comm)
qed

lemma translate_mk_node:
  "translate (mk_node s) = translate (add_maps (map_blocks s) 
                                     (mk_overlay (overlay s)))"
  by(simp add:mk_node_def maps_blocks_comm translate_add_blocks)
(*>*)

type_synonym net_spec = "(nodeid \<times> node_spec) list"

definition "empty_net = (\<lambda>_. empty_node)"

primrec repeat_node :: "node_spec \<Rightarrow> nodeid \<Rightarrow> nat \<Rightarrow> net_spec"
  where "repeat_node node ba 0 = []" |
        "repeat_node node ba (Suc n) = (ba, node) # repeat_node node (Suc ba) n"

primrec mk_net :: "net_spec \<Rightarrow> net"
  where "mk_net [] = empty_net" |
        "mk_net (s#ss) = (mk_net ss)(fst s := mk_node (snd s))"

(*<*)
lemma map_blocks_empty_spec:
  "map_blocks empty_spec = []"
  by(simp add:mk_overlay_def empty_spec_def)

subsubsection {* Correctness by Construction *}

definition wf_node :: "node \<Rightarrow> bool"
  where "wf_node node \<longleftrightarrow> finite (accept node) \<and> (\<forall>a. finite (translate node a))"

lemma wf_nodeI:
  "finite (accept node) \<Longrightarrow> (\<And>a. finite (translate node a)) \<Longrightarrow> wf_node node"
  by(simp add:wf_node_def)

lemma wf_node_wf_net:
  "(\<And>nd. wf_node (net nd)) \<Longrightarrow> wf_net net"
  unfolding wf_node_def wf_net_def 
  by(auto simp:Image_def decodes_to_def decode_step_def)

lemma wf_empty_node:
  "wf_node empty_node"
  unfolding empty_node_def by(auto intro:wf_nodeI)

lemma wf_overlay:
  "wf_node (mk_overlay s)"
  unfolding mk_overlay_def by(cases s, simp_all add:wf_node_def)


lemma finite_mk_block:
"finite (mk_block s)"
proof -
  have sep: "\<And>s. mk_block s = ({a . base s \<le> a 
                      \<and> a \<le> limit s}) \<times> {p | p . (\<forall>p'\<in> p. p'\<notin> (forbid s))
                                \<and> (\<forall>p'\<in> (require s). p' \<in> p)}"
    by(auto simp:mk_block_def)

  have finProps : "finite  {p | p . (\<forall>p'\<in> p. p'\<notin> (forbid s))
                                \<and> (\<forall>p'\<in> (require s). p' \<in> p)}"
    by(auto)
  have finAddrs : "finite ({a . base s \<le> a \<and> a \<le> limit s})"
    by(auto)
  from sep finProps finAddrs show ?thesis
    by(auto)
qed

lemma wf_add_blocks:
  assumes wf_base: "wf_node node"
  shows "wf_node (add_blocks ss node)"
proof(induct ss, simp_all add:wf_base)
  fix s ss
  assume IH: "wf_node (add_blocks ss node)"
  hence "finite (accept (add_blocks ss node))" "\<And>s. finite (translate (add_blocks ss node) s)"
    by(auto simp:wf_node_def)
  moreover have "finite (mk_block s)"
    by(simp add: finite_mk_block)
  ultimately show "wf_node (accept_update (op \<union> (mk_block s)) (add_blocks ss node))"
    by(auto intro:wf_nodeI)
qed

  
lemma wf_add_maps:
  assumes wf_base: "wf_node node"
  shows "wf_node (add_maps ss node)"    
proof(simp only: add_maps_recursive[symmetric],induct ss, simp_all add:wf_base)
  fix s ss
  assume IH: "wf_node (add_maps_rec ss node)"
  hence "finite (accept (add_maps_rec ss node))" "\<And>a. finite (translate (add_maps_rec ss node) a)"
    by(auto simp:wf_node_def)
  moreover have "\<And>a. finite (mk_map s a)"
    unfolding mk_map_def by(simp)
  ultimately show "wf_node (translate_update (\<lambda>t a. mk_map s a \<union> t a) (add_maps_rec ss node))"
    by(auto intro:wf_nodeI)
qed

lemma wf_mk_node:
  "wf_node (mk_node s)"
  unfolding mk_node_def by(auto intro:wf_add_maps wf_add_blocks wf_overlay)

lemma wf_empty_net:
  "wf_net empty_net"
  unfolding empty_net_def by(auto intro:wf_node_wf_net wf_empty_node)
(*>*)

text {* Nets built from abstract syntax are correct by construction: *}
lemma wf_mk_net:
  "wf_net (mk_net ss)"
(*<*)
  by(rule wf_node_wf_net, induct ss, simp_all add:empty_net_def wf_empty_node wf_mk_node)
(*>*)
subsubsection {* Finding Fresh Nodes *}

text {* These functions are guaranteed to return a node that's unused in the supplied
  specification. *}
definition ff_overlay :: "nodeid option \<Rightarrow> nodeid"
  where "ff_overlay s = (case s of Some nd \<Rightarrow> Suc nd | None \<Rightarrow> 0)"

(*<*)
lemma ff_overlay_ub:
  assumes "(nd',a') \<in> translate (mk_overlay ov) a"
  shows "nd' < ff_overlay ov"
  using assms by(cases ov, simp_all add:mk_overlay_def ff_overlay_def)
(*>*)

primrec ff_map :: "map_spec list \<Rightarrow> nodeid"
  where "ff_map [] = 0" |
        "ff_map (s#ss) = max (Suc (dest_node s)) (ff_map ss)"

(*<*)
lemma ff_add_blocks_ub:
  assumes "\<And>nd' a' a. (nd',a') \<in> translate node a \<Longrightarrow> nd' < x"
      and "(nd',a') \<in> translate (add_blocks bs node) a"
    shows "nd' < x"
  using assms by(simp add:translate_add_blocks)
 

lemma ff_add_maps_ub:
  assumes ff_node: "\<And>nd' a' a. (nd',a') \<in> translate node a \<Longrightarrow> nd' < x"
      and nda': "(nd',a') \<in> translate (add_maps ms node) a"
    shows "nd' < max x (ff_map ms)"
  using nda'
proof(induct ms, simp add:ff_node add_maps_recursive[symmetric])
  fix m ms
  assume IH: "(nd', a') \<in> translate (add_maps ms node) a \<Longrightarrow> nd' < max x (ff_map ms)"
     and step: "(nd', a') \<in> translate (add_maps (m # ms) node) a"
     
  from step have "(nd',a') \<in> mk_map m a \<or> (nd',a') \<in> translate (add_maps ms node) a"
    by(simp add:add_maps_recursive[symmetric])
  thus "nd' < max x (ff_map (m # ms))"
  proof
    assume "(nd', a') \<in> mk_map m a"
    hence "nd' < Suc (dest_node m)"
      by(cases "a \<in> mk_block (src_block m)", simp_all add:mk_map_def)
    thus ?thesis by(simp)
  next
    assume "(nd', a') \<in> translate (add_maps ms node) a"
    thus ?thesis by(simp only:add_maps_recursive[symmetric], auto dest:IH)      
  qed
qed  
(*>*)

definition ff_node :: "node_spec \<Rightarrow> nodeid"
  where "ff_node s = max (ff_overlay (overlay s)) (ff_map (map_blocks s))"

(*<*)
lemma ff_node_ub:
  assumes step: "(nd',a') \<in> translate (mk_node s) a"
  shows "nd' < ff_node s"
  unfolding ff_node_def using ff_overlay_ub    
  by(auto simp:translate_add_blocks intro:ff_add_maps_ub[OF _ step[unfolded mk_node_def]])
(*>*)

primrec ff_net :: "net_spec \<Rightarrow> nodeid"
  where "ff_net [] = 0" |
        "ff_net (s#ss) = Max {ff_node (snd s), ff_net ss, Suc (fst s)}"

(*<*)
lemma ff_net_empty:
  "ff_net s \<le> nd \<Longrightarrow> mk_net s nd = empty_node"
  by(induct s, simp_all add:empty_net_def)

lemma decodes_to_empty_net:
  "decodes_to empty_net = {}"
  by(simp add:decodes_to_def decode_step_def empty_net_def empty_node_def)

lemma ff_net_ub:
  "(x,y) \<in> decodes_to (mk_net s) \<Longrightarrow> fst x < ff_net s"
proof(induct s, simp add:decodes_to_empty_net)
  fix s ss
  assume IH: "(x, y) \<in> decodes_to (mk_net ss) \<Longrightarrow> fst x < ff_net ss"
     and dec: "(x, y) \<in> decodes_to (mk_net (s # ss))"
     
  show "fst x < ff_net (s # ss)"
  proof(cases)
    assume "fst y = fst s"
    with dec have "x \<in> translate (mk_node (snd s)) (snd y)"
      by(cases x, cases y, simp add:decodes_to_def decode_step_def)
    hence "fst x < ff_node (snd s)"
      by(cases x, auto intro:ff_node_ub)
    thus ?thesis by(simp)
  next
    assume "fst y \<noteq> fst s"
    with dec have "(x, y) \<in> decodes_to (mk_net ss)"
      by(cases y, simp add:decodes_to_def decode_step_def)
    with IH show ?thesis by(simp)
  qed
qed

lemma ff_net_fresh:
  assumes ff: "ff_net s \<le> nd"
  shows "fresh_node (mk_net s) nd"
  unfolding fresh_node_def
proof(intro conjI allI impI)
  fix a
  from ff have "mk_net s nd = empty_node" by(rule ff_net_empty)
  thus "accept (mk_net s nd) = {}" "translate (mk_net s nd) a = {}"
    by(simp_all add:empty_node_def)
next
  fix x y
  assume "(x, y) \<in> decodes_to (mk_net s)"
  hence "fst x < ff_net s" by(rule ff_net_ub)
  also note ff
  finally show "fst x \<noteq> nd" by(simp)
qed

lemma ff_net_idbound:
  "nd \<in> set (map fst s) \<Longrightarrow> nd < ff_net s"
proof(induct s, simp_all)
  fix s::"(nodeid \<times> node_spec)" and ss
  assume IH: "nd \<in> fst ` set ss \<Longrightarrow> nd < ff_net ss"
  assume "nd = fst s \<or> nd \<in> fst ` set ss"
  thus "nd < max (ff_node (snd s)) (max (ff_net ss) (Suc (fst s)))"
  proof
    assume "nd = fst s" thus ?thesis by(auto)
  next
    assume "nd \<in> fst ` set ss"
    with IH have "nd < ff_net ss" by(blast)
    thus ?thesis by(auto)
  qed
qed
(*>*)

(*<*)
end
(*>*)