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
theory ConcreteOps
  imports AbstractOps Syntax
begin
(*>*)

subsection {* Transformations on Abstract Syntax *}
text_raw {* \label{sec:isasplitC} *}

(*<*)
subsubsection {* Node Splitting *}
(*>*)
  
text {* These are the equivalents, in abstract syntax, of the abstract acceptor
        and translator nodes.  Somewhat confusingly, we will now refer to the
        \emph{abstract} syntax as the \emph{concrete} model (relative to the
        abstract directed graph model).  *}
primrec remap_all :: "nodeid \<Rightarrow> block_spec list \<Rightarrow> map_spec list"
  where "remap_all _ [] = []" |
        "remap_all nd (b#bs) = direct_map b nd # remap_all nd bs"

definition redirector_node_C :: "nodeid \<Rightarrow> node_spec \<Rightarrow> node_spec"
  where "redirector_node_C nd' ns =
          empty_spec \<lparr> map_blocks := remap_all nd' (acc_blocks ns) @ map_blocks ns,
                       overlay := overlay ns \<rparr>"

definition acceptor_node_C :: "node_spec \<Rightarrow> node_spec"
  where "acceptor_node_C ns = empty_spec \<lparr> acc_blocks := acc_blocks ns \<rparr>"

(*<*)
lemma translate_nomap:
  "a \<notin> accept (add_blocks bs empty_node) \<Longrightarrow>
   translate (add_maps (remap_all nd' bs) node) a = translate node a"
  by(simp add:add_maps_recursive[symmetric], induct bs, simp_all add:mk_map_def direct_map_def)

lemma translate_map:
  "a \<in> accept (add_blocks bs empty_node) \<Longrightarrow>
   translate (add_maps (remap_all nd' bs) node) a = insert (nd', a) (translate node a)"
proof(induct bs, simp add:accept_empty_node)
  fix b bs
  assume IH: "a \<in> accept (add_blocks bs empty_node) \<Longrightarrow>
              translate (add_maps (remap_all nd' bs) node) a = insert (nd', a) (translate node a)"
    
  assume "a \<in> accept (add_blocks (b # bs) empty_node)"
  hence either: "a \<in> mk_block b \<or> a \<in> accept (add_blocks bs empty_node)" by(simp)
      
  show "translate (add_maps (remap_all nd' (b # bs)) node) a = insert (nd', a) (translate node a)"
  proof(cases)
    assume "a \<in> accept (add_blocks bs empty_node)"
    thus ?thesis 
      apply(simp add:add_maps_recursive[symmetric])
      apply(simp add: IH mk_map_def direct_map_def mk_block_def add_maps_recursive)
      apply(auto)
      done
  next
    assume notin: "a \<notin> accept (add_blocks bs empty_node)"
    with either have "a \<in> mk_block b" by(blast)
    thus ?thesis 
      apply(simp add:add_maps_recursive[symmetric])
      apply(simp add:translate_nomap notin mk_map_def direct_map_def mk_block_def add_maps_recursive)
      apply(auto)
      done
  qed
qed
           
lemma translate_redirect:
  "a \<in> accept (mk_node ns) \<Longrightarrow>
   translate (mk_node (redirector_node_C nd' ns)) a = {(nd',a)} \<union> translate (mk_node ns) a"
  by(simp add:translate_mk_node redirector_node_C_def add_maps_append accept_mk_node translate_map)

lemma translate_noredirect:
  "a \<notin> accept (mk_node ns) \<Longrightarrow> translate (mk_node (redirector_node_C nd' ns)) a =
                               translate (mk_node ns) a"
  by(simp add:translate_mk_node redirector_node_C_def accept_mk_node add_maps_append translate_nomap)
(*>*)
text {* The concrete redirector node refines the abstract: *}
lemma redirector_rel:
  "mk_node (redirector_node_C nd' ns) = redirector_node nd' (mk_node ns)"
(*<*)
  (is "?X = ?Y")
proof -
  have "accept ?X = accept ?Y"
    by(simp add:mk_node_def redirector_node_def redirector_node_C_def acc_blocks_empty
                accept_add_maps accept_mk_overlay)
  moreover have "translate ?X = translate ?Y"
  proof(rule ext)
    fix a
    show "translate ?X a = translate ?Y a"
      by(cases "a \<in> accept (mk_node ns)",
         simp_all add:redirector_node_def translate_redirect translate_noredirect)
  qed
  ultimately show ?thesis by(simp)
qed
(*>*)
text {* The concrete acceptor node refines the abstract: *}
lemma acceptor_rel:
  "mk_node (acceptor_node_C ns) = acceptor_node (mk_node ns)"
(*<*)
proof -
  have "translate (mk_node (acceptor_node_C ns)) = translate (acceptor_node (mk_node ns))"
    by(simp add:acceptor_node_C_def acceptor_node_def translate_mk_node empty_spec_def
                mk_overlay_def add_maps_recursive[symmetric])
  moreover have "accept (mk_node (acceptor_node_C ns)) = accept (acceptor_node (mk_node ns))"
    by(simp add:acceptor_node_C_def acceptor_node_def accept_mk_node)
  ultimately show ?thesis by(simp)
qed
(*>*)
primrec split_all_C :: "nodeid \<Rightarrow> net_spec \<Rightarrow> net_spec"
  where "split_all_C _ [] = []" |
        "split_all_C off (s#ss) =
          [(off + fst s, acceptor_node_C (snd s)),
           (fst s, redirector_node_C (off + fst s) (snd s))] @ split_all_C off ss"

text {* Thus (by induction), splitting all nodes in the concrete spec is equivalent to doing so
  in the abstract (\autoref{eq:splitrefine}): *}
lemma split_all_rel:
  assumes "distinct (map fst ss)"
      and  "\<And>nd. nd \<in> set (map fst ss) \<Longrightarrow> nd < off"
    shows "mk_net (split_all_C off ss) = split_all (map fst ss) (op + off) (mk_net ss)"
(*<*)
      (is "?X ss = ?Y ss")
  using assms
proof(induct ss, simp)
  fix s ss
  assume distinct: "distinct (map fst (s # ss))"
     and bound: "\<And>nd. nd \<in> set (map fst (s # ss)) \<Longrightarrow> nd < off"
     and IH: "distinct (map fst ss) \<Longrightarrow>
             (\<And>nd. nd \<in> set (map fst ss) \<Longrightarrow> nd < off) \<Longrightarrow>
             ?X ss = ?Y ss"
    
  have "mk_net (split_all_C off (s # ss)) =
        (mk_net (split_all_C off ss))
          (fst s := redirector_node (off + fst s) (mk_node (snd s)),
           off + fst s := acceptor_node (mk_node (snd s)))"
    by(simp add:redirector_rel acceptor_rel)
  also from distinct bound IH
  have "... =
        (?Y ss)
          (fst s := redirector_node (off + fst s) (mk_node (snd s)),
           off + fst s := acceptor_node (mk_node (snd s)))"
    by(simp)
  also have "... = split_node (fst s) (off + fst s) ((?Y ss)(fst s := mk_node (snd s)))"
    by(simp add:split_node_def)
  also {
    let ?prev = "..."
    from distinct bound have "fst s \<notin> set (map fst ss)" "\<And>nd'. off + nd' \<noteq> fst s" by(auto)
    hence "?prev =
      split_node (fst s) (off + fst s) (split_all (map fst ss) (op + off) (mk_net (s#ss)))"
      by(simp add:split_all_upd_comm)
  }
  also have "split_node (fst s) (off + fst s) (split_all (map fst ss) (op + off) (mk_net (s#ss))) =
             split_all (map fst (s # ss)) (op + off) (mk_net (s # ss))"
    by(simp)
  finally show "mk_net (split_all_C off (s # ss)) =
                split_all (map fst (s # ss)) (op + off) (mk_net (s # ss))" .
qed
(*>*)

text {* Finally, we have refinement between the concrete and abstract split operations on whole
  nets (\autoref{eq:fulleq}): *}
definition split_net_C :: "net_spec \<Rightarrow> net_spec"
  where "split_net_C s = split_all_C (ff_net s) s"

lemma split_net_equiv:
  assumes distinct: "distinct (map fst s)"
  shows "view_eq_on {0..<ff_net s} (rename_list (op + (ff_net s)) (map fst s), mk_net s) (id, mk_net (split_net_C s))"
proof -
  text {* The abstract split preserves view equivalence for any node that was defined in the
    original spec: *}
  have "view_eq_on {0..<ff_net s} (rename_list (op + (ff_net s)) (map fst s), mk_net s)
                                  (id, split_all (map fst s) (op + (ff_net s)) (mk_net s))"
    using ff_net_idbound distinct wf_mk_net
    by(intro view_eq_split_all, auto intro:ff_net_fresh view_eq_split_all)

  text {* The concrete split refines the abstract split: *}
  moreover have "mk_net (split_all_C (ff_net s) s) = split_all (map fst s) (op + (ff_net s)) (mk_net s)"
    by(auto intro:split_all_rel distinct ff_net_idbound)

  text {* Thus we have view equivalence for the concrete operation, too. *}
  ultimately show ?thesis by(simp add:split_net_C_def)
qed

(*<*)
end
(*>*)
