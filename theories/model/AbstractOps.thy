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
theory AbstractOps
  imports Equivalence Resolution
begin
(*>*)

subsection "Equivalence-Preserving Transformations"

subsubsection "Splitting Nodes"
text_raw {* \label{sec:isasplit} *}
    
text {* The acceptor accepts all addresses accepted by the original node, but translates none. *}
definition acceptor_node :: "node \<Rightarrow> node"
  where "acceptor_node node = node \<lparr> translate := \<lambda>_. {} \<rparr>"

text {* Forward all addresses to the acceptor node, maintaining existing translations. *}
definition redirector_node :: "nodeid \<Rightarrow> node \<Rightarrow> node"
  where "redirector_node nd' node = \<lparr> accept = {},
          translate = (\<lambda>a. if a \<in> accept node then insert (nd',a) (translate node a) else translate node a) \<rparr>"

text {* Split a node into an acceptor, that accepts all addresses accepted by the original node, and
  a redirector, which forwards all addresses that it would have accepted to the acceptor. *}
definition split_node :: "nodeid \<Rightarrow> nodeid \<Rightarrow> net \<Rightarrow> net"
  where "split_node nd nd' net =
    net(nd := redirector_node nd' (net nd), nd' := acceptor_node (net nd))"

text {* We can represent the effect of node splitting by its action on the set of accepted names,
  and on the decoding relation.  Recall from \autoref{sec:isares} that this is sufficient to
  fully define the result of resolution. *}

text {* Splitting only adds the new decode edges: *}
lemma split_decode:
  "nd \<noteq> nd' \<Longrightarrow> (\<And>a. translate (net nd') a = {}) \<Longrightarrow>
   decodes_to (split_node nd nd' net) =
   decodes_to net \<union> (\<lambda>a. (Pair nd' a, Pair nd a)) ` accept (net nd)"
(*<*)
  by(auto simp:decodes_to_def decode_step_def split_node_def acceptor_node_def redirector_node_def)
(*>*)

text {* Splitting only touches the named nodes: *}
lemma fresh_split_node:
  assumes fresh: "fresh_node net x"
      and neq: "x \<noteq> nd" "x \<noteq> nd'"
    shows "fresh_node (split_node nd nd' net) x"
(*<*)
  unfolding fresh_node_def
proof(intro conjI allI impI)
  from neq fresh_node_acceptD[OF fresh]
  show "accept (split_node nd nd' net x) = {}"
    by(simp add:split_node_def)
next
  fix a
  from neq fresh_node_translateD[OF fresh]
  show "translate (split_node nd nd' net x) a = {}"
    by(simp add:split_node_def)
next
  fix a b
  thm fresh_node_reachableD
  assume step: "(a, b) \<in> decodes_to (split_node nd nd' net)"
  show "fst a \<noteq> x"
  proof(cases)
    assume "fst b = nd'"
    with step show ?thesis
      by(simp add:split_node_def decodes_to_def decode_step_def acceptor_node_def)
  next
    assume bne: "fst b \<noteq> nd'"
    show ?thesis
    proof (cases)
      assume beq: "fst b = nd"
      show ?thesis
      proof(cases)
        assume "snd b \<in> accept (net nd)"
        with step bne neq beq
        show ?thesis
        proof(simp add:split_node_def decodes_to_def decode_step_def redirector_node_def)
          assume "a = (nd', snd b) \<or> a \<in> translate (net nd) (snd b)"
          thus "fst a \<noteq> x"
          proof
            assume "a = (nd', snd b)" with neq show ?thesis by(auto)
          next
            assume "a \<in> translate (net nd) (snd b)"
            hence "(a, (nd, snd b)) \<in> decodes_to net"
              by(simp add:decodes_to_def decode_step_def)
            with fresh show ?thesis by(blast dest:fresh_node_reachableD)
          qed
        qed
      next
        assume "snd b \<notin> accept (net nd)"
        with step bne neq beq show ?thesis
        proof(simp add:split_node_def decodes_to_def decode_step_def redirector_node_def)
          assume "a \<in> translate (net nd) (snd b)"
          hence "(a, (nd, snd b)) \<in> decodes_to net"
            by(simp add:decodes_to_def decode_step_def)
          with fresh show ?thesis by(blast dest:fresh_node_reachableD)
        qed
      qed
    next
      assume "fst b \<noteq> nd"
      with step bne neq show ?thesis
      proof(simp add:split_node_def decodes_to_def decode_step_def)
        assume "a \<in> translate (net (fst b)) (snd b)"
        hence "(a, b) \<in> decodes_to net"
          by(simp add:decodes_to_def decode_step_def)
        with fresh show ?thesis by(blast dest:fresh_node_reachableD)
      qed
    qed
  qed
qed
(*>*)
text {* Splitting neither adds nor removes accepted names, it simply renames those accepted by the
  original node: *}
lemma split_accepted:
  assumes empty: "accept (net nd') = {}"
    shows "accepted_names (split_node nd nd' net) = rename (id(nd := nd')) ` accepted_names net"
(*<*)
          (is "?X = ?Y")
proof(intro antisym subsetI)
  fix x
  assume xin: "x \<in> ?X"
  show "x \<in> ?Y"
  proof(cases)
    assume xeq: "fst x = nd'"
    with xin
    have "snd x \<in> accept (acceptor_node (net nd))"
      by(cases x, simp add:accepted_names_def split_node_def)
    hence "(nd,snd x) \<in> accepted_names net"
      by(simp add:accepted_names_def acceptor_node_def)
    moreover from xeq have "x = rename (id(nd := nd')) (nd,snd x)"
      by(cases x, simp add:rename_def)
    ultimately show "x \<in> ?Y" by(blast)
  next
    assume xne': "fst x \<noteq> nd'"
      
    have xne: "fst x \<noteq> nd"
    proof(rule ccontr, simp)
      assume "fst x = nd"
      with xne' xin show False
        by(cases x, simp add:accepted_names_def split_node_def redirector_node_def)
    qed
      
    from xne xne' xin have "x \<in> accepted_names net"
      by(cases x, simp add:accepted_names_def split_node_def)
    moreover from xne have "x = rename (id(nd := nd')) x" by(simp add:rename_def)
    ultimately show ?thesis by(blast)
  qed
next
  fix x
  assume xin: "x \<in> ?Y"
  then obtain y where yin: "y \<in> accepted_names net" and xy: "x = rename (id(nd := nd')) y" by(blast)

  show "x \<in> ?X"
  proof(cases)
    assume yeq: "fst y = nd"
    with xy have xeq: "x = (nd',snd y)" by(simp add:rename_def)
        
    from yin yeq xeq
    have "snd x \<in> accept (net nd)"
      by(cases y, simp add:accepted_names_def)
    with xeq show ?thesis
      by(cases x, simp add:accepted_names_def split_node_def acceptor_node_def)
  next
    assume yne: "fst y \<noteq> nd"
    with xy have xeq: "x = y" by(simp add:rename_def)  
    with yin have xin': "x \<in> accepted_names net" by(simp)
        
    from yin empty have yne': "fst y \<noteq> nd'"
      by(cases y, simp add:accepted_names_def, auto)
        
    from xin' yne yne' show ?thesis
      by(cases x, simp add:accepted_names_def split_node_def xeq)
  qed
qed
(*>*)
text {* Splitting a node has no effect on the termination of @{term resolve}: *}
lemma split_node_domeq:
  fixes S :: "nodeid set" and nd nd' :: nodeid and net :: net and n::name
  assumes neq: "nd \<noteq> nd'"
      and wf_net: "wf_net net"
      and fresh: "fresh_node net nd'"
    shows "resolve_dom (net,n) = resolve_dom (split_node nd nd' net,n)"
(*<*)
proof(cases n, simp, intro iffI)
  fix nd3 a
  assume dom: "resolve_dom (net, nd3, a)"

  from wf_net dom mkrank obtain f where wf: "wf_rank f (nd3,a) net" by(blast dest:wf_net_decodeD)

  let ?g = "\<lambda>n. if fst n = nd' then 0 else Suc (f n)"

  have "wf_rank ?g (nd3,a) (split_node nd nd' net)"
  proof(intro wf_rankI)
    fix x y
    assume reach: "(x, nd3, a) \<in> (decodes_to (split_node nd nd' net))\<^sup>*"
       and step: "(y, x) \<in> decodes_to (split_node nd nd' net)"
       
    have ne_nd': "fst x \<noteq> nd'"
    proof(rule ccontr, simp)
      assume "fst x = nd'"
      with step have "(y, (nd',snd x)) \<in> decodes_to (split_node nd nd' net)" by(auto)
      with neq have "y \<in> translate (net nd') (snd x)"
        by(simp add:split_node_def decodes_to_def decode_step_def redirector_node_def
                    acceptor_node_def)
      with fresh show False by(blast dest:fresh_node_translateD)
    qed
       
    show "?g y < ?g x"
    proof(cases "fst y = nd'", simp_all add:ne_nd')
      assume "fst y \<noteq> nd'"
      with step neq fresh_node_translateD[OF fresh] split_decode
      have yx: "(y,x) \<in> decodes_to net" by(auto)
          
      from reach have xn: "(x,nd3,a) \<in> (decodes_to net)\<^sup>*"
      proof(induct, simp)
        fix y z
        assume xy: "(x, y) \<in> (decodes_to net)\<^sup>*"
           and yz: "(y, z) \<in> decodes_to (split_node nd nd' net)"
        show "(x, z) \<in> (decodes_to net)\<^sup>*"
        proof(cases)
          assume "x = y"
          with yz have "(x,z) \<in> decodes_to (split_node nd nd' net)" by(simp)
          with ne_nd' neq fresh_node_translateD[OF fresh] split_decode
          show "(x,z) \<in> (decodes_to net)\<^sup>*" by(auto)
        next
          assume "x \<noteq> y"
          with xy have "(x,y) \<in> (decodes_to net)\<^sup>+"
            by(auto dest:rtranclD)
          then obtain w where "(w,y) \<in> decodes_to net"
            by(auto dest:tranclD2)
          with fresh have "fst y \<noteq> nd'"
            unfolding decodes_to_def decode_step_def by(auto dest:fresh_node_translateD)
          with yz neq fresh_node_translateD[OF fresh] split_decode
          have "(y,z) \<in> decodes_to net" by(auto)
          with xy show ?thesis by(auto)
        qed
      qed
      with yx wf show "f y < f x"
        unfolding wf_rank_def by(blast)
    qed
  qed
  thus "resolve_dom (split_node nd nd' net, nd3, a)" by(blast intro:wf_resolve_dom)
next
  fix nd3 a
    
  assume dom: "resolve_dom (split_node nd nd' net, nd3, a)"

  let ?R = "\<lambda>a b. resolve_rel (split_node nd nd' net, a) (split_node nd nd' net, b)"
  let ?S = "\<lambda>a b. resolve_rel (net,a) (net,b)"

  {
    fix n
    have "resolve_dom (split_node nd nd' net, n) \<Longrightarrow>
          fst (split_node nd nd' net, n) = split_node nd nd' net \<Longrightarrow>
          Wellfounded.accp ?R (snd (split_node nd nd' net, n))"
    proof(induct rule:accp.induct, rule accp.intros)
      fix x y
      assume "resolve_rel (split_node nd nd' net, y) (split_node nd nd' net, snd x)"
         and "fst x = split_node nd nd' net"
      hence "resolve_rel (split_node nd nd' net, y) x" by(cases x, simp)
      moreover assume "\<And>y. resolve_rel y x \<Longrightarrow>
                           fst y = split_node nd nd' net \<Longrightarrow>
        Wellfounded.accp (\<lambda>a b. resolve_rel (split_node nd nd' net, a) (split_node nd nd' net, b))
                         (snd y)"
      ultimately
      show "Wellfounded.accp (\<lambda>a b. resolve_rel (split_node nd nd' net, a)
                                                (split_node nd nd' net, b)) y"
        by(cases y, auto)
    qed
    hence "resolve_dom (split_node nd nd' net, n) \<Longrightarrow>
          Wellfounded.accp ?R (snd (split_node nd nd' net, n))"
      by(simp)
  }
  with dom have accpR: "Wellfounded.accp ?R (nd3,a)" by(simp)

  from neq fresh
  have "decodes_to (split_node nd nd' net) = 
        decodes_to net \<union> (\<lambda>a. (Pair nd' a, Pair nd a)) ` accept (net nd)"
    by(blast dest:fresh_node_translateD intro!:split_decode)  
  hence SR: "?S \<le> ?R"
    by(intro le_funI le_boolI, simp add:resolve_rel_decodes_to)

  show "resolve_dom (net, nd3, a)"
  proof(rule resolve_domI)
    fix x
    assume "(x, nd3, a) \<in> decodes_to net"
    hence "?S x (nd3,a)" by(simp add:resolve_rel_decodes_to)
    with SR have "?R x (nd3,a)" by(auto)
    with accpR have accpRx: "Wellfounded.accp ?R x" by(rule accp_downward)
    with accp_subset[OF SR] have "Wellfounded.accp ?S x" by(blast)
    thus "resolve_dom (net,x)"
    proof(induct x)
      fix z
      assume IH: "\<And>y. resolve_rel (net, y) (net, z) \<Longrightarrow> resolve_dom (net, y)"
      show "resolve_dom (net, z)"
      proof(rule resolve_domI)
        fix y
        assume "(y,z) \<in> decodes_to net"
        hence "resolve_rel (net,y) (net,z)" by(simp add:resolve_rel_decodes_to)
        thus "resolve_dom (net,y)" by(rule IH)
      qed
    qed
  qed
qed
(*>*)

text {* The effect of splitting a node is just to rename anything that was accepted by the split
  node. *}
lemma split_node_resolveeq:
  fixes S :: "nodeid set" and nd nd' :: nodeid and net :: net and n::name
  assumes neq: "nd \<noteq> nd'"
      and wf_net: "wf_net net"
      and fresh: "fresh_node net nd'"
      and dom: "resolve_dom (net,n)"
    shows "fst n \<noteq> nd' \<Longrightarrow>
           rename (id(nd := nd')) ` resolve net n =
           rename id ` resolve (split_node nd nd' net) n"
(*<*)
proof(induct rule:resolve_induct[OF dom])
  fix n
  assume dom: "resolve_dom (net,n)"
     and notnd': "fst n \<noteq> nd'"

  assume "\<And>x. (x, n) \<in> decodes_to net \<Longrightarrow>
              fst x \<noteq> nd' \<Longrightarrow>
              rename (id(nd := nd')) ` resolve net x =
              rename id ` resolve (split_node nd nd' net) x"
  hence IH: "\<And>x. (x, n) \<in> decodes_to net \<Longrightarrow>
                 rename (id(nd := nd')) ` resolve net x =
                 rename id ` resolve (split_node nd nd' net) x"
    by(blast dest:fresh_node_reachableD[OF fresh])

  from neq fresh wf_net dom
  have dom': "resolve_dom (split_node nd nd' net, n)"
    by(simp add:split_node_domeq)

  (* This is a tedious rewriting grind, and could & should be rewritten! *)
  have "rename (id(nd := nd')) ` resolve net n =
        rename (id(nd := nd')) ` ({n} \<inter> accepted_names net \<union>
                                  (\<Union>n'\<in>(decodes_to net)\<inverse> `` {n}. resolve net n'))"
    by(simp add:resolve_simp[OF dom])
  also have "... =
    rename (id(nd := nd')) ` ({n} \<inter> accepted_names net) \<union>
    (\<Union>n'\<in>(decodes_to net)\<inverse> `` {n}. rename (id(nd := nd')) ` resolve net n')"
    by(simp add:image_Un image_UN)
  also have "... =
    (rename (id(nd := nd')) ` ({n} \<inter> accepted_names net)) \<union>
    (\<Union>n'\<in>(decodes_to net)\<inverse> `` {n}. resolve (split_node nd nd' net) n')"
    by(simp add:IH rename_id)
  also {
    have "(rename (id(nd := nd')) ` ({n} \<inter> accepted_names net)) =
          (({n} \<inter> rename (id(nd := nd')) ` accepted_names net) \<union>
           {n'. n' = (nd',snd n) \<and> snd n \<in> accept (net nd) \<and> fst n = nd})"
    proof(intro antisym subsetI)
      fix x
      assume "x \<in> rename (id(nd := nd')) ` ({n} \<inter> accepted_names net)"
      hence nin: "n \<in> accepted_names net" and xn: "x = rename (id(nd := nd')) n"
        by(auto)
      show "x \<in> {n} \<inter> rename (id(nd := nd')) ` accepted_names net \<union>
            {n'. n' = (nd',snd n) \<and> snd n \<in> accept (net nd) \<and> fst n = nd}"
      proof(cases)
        assume n_nd: "fst n = nd"
        with xn have xeq: "fst x = nd'" "snd x = snd n"
          by(cases x, cases n, auto simp:rename_def)
        with nin n_nd have "x \<in> {n'. n' = (nd',snd n) \<and> snd n \<in> accept (net nd) \<and> fst n = nd}"
          unfolding accepted_names_def
          by(cases x, cases n, simp)
        thus ?thesis by(blast)
      next
        assume neq: "fst n \<noteq> nd"
        with xn have xeq: "x = n" by(simp add:rename_def)
        hence "x \<in> {n}" by(simp)
        moreover {
          from xeq nin have "x \<in> accepted_names net" by(simp)
          moreover from neq xeq have "x = rename (id(nd := nd')) x"
            by(simp add:rename_def)
          ultimately have "x \<in> rename (id(nd := nd')) ` accepted_names net" by(blast)
        }
        ultimately show ?thesis by(blast)
      qed
    next
      fix x
      assume lhs: "x \<in> {n} \<inter> rename (id(nd := nd')) ` accepted_names net \<union>
                   {n'. n' = (nd',snd n) \<and> snd n \<in> accept (net nd) \<and> fst n = nd}"
                  (is "x \<in> ?A \<union> ?B")
      show "x \<in> rename (id(nd := nd')) ` ({n} \<inter> accepted_names net)" (is "x \<in> ?C")
      proof(rule UnE[OF lhs])
        assume "x \<in> ?A"
        hence xeq: "x = n" and img: "x \<in> rename (id(nd := nd')) ` accepted_names net" by(auto)
            
        from img obtain y where yin: "y \<in> accepted_names net"
                            and xy: "x = rename (id(nd := nd')) y"
          by(auto)
            
        from xy neq have x_ne_nd: "fst x \<noteq> nd" by(auto simp:rename_def)
    
        from notnd' xeq have "fst x \<noteq> nd'" by(simp)
        with xy have y_eq_x: "y = x" by(auto simp:rename_def)
        with yin xeq have "x \<in> {n} \<inter> accepted_names net" by(simp)
        moreover from y_eq_x xy have "x = rename (id(nd := nd')) x" by(simp)
        ultimately show "x \<in> rename (id(nd := nd')) ` ({n} \<inter> accepted_names net)" by(blast)
      next
        assume "x \<in> ?B"
        hence "n \<in> {n} \<inter> accepted_names net" "x = rename (id(nd := nd')) n"
          by(auto simp:accepted_names_def rename_def)
        thus "x \<in> rename (id(nd := nd')) ` ({n} \<inter> accepted_names net)" by(blast)
      qed
    qed
    hence "(rename (id(nd := nd')) ` ({n} \<inter> accepted_names net)) \<union>
           (\<Union>n'\<in>(decodes_to net)\<inverse> `` {n}. resolve (split_node nd nd' net) n') =
           (({n} \<inter> rename (id(nd := nd')) ` accepted_names net) \<union>
            {n'. n' = (nd',snd n) \<and> snd n \<in> accept (net nd) \<and> fst n = nd}) \<union>
           (\<Union>n'\<in>(decodes_to net)\<inverse> `` {n}. resolve (split_node nd nd' net) n')"
      by(simp)
  }
  also
  have "(({n} \<inter> rename (id(nd := nd')) ` accepted_names net) \<union>
         {n'. n' = (nd',snd n) \<and> snd n \<in> accept (net nd) \<and> fst n = nd}) \<union>
        (\<Union>n'\<in>(decodes_to net)\<inverse> `` {n}. resolve (split_node nd nd' net) n') =
        ({n} \<inter> rename (id(nd := nd')) ` accepted_names net \<union>
      ((\<Union>n'\<in>(decodes_to net)\<inverse> `` {n}. resolve (split_node nd nd' net) n') \<union> 
       {n'. n' = (nd',snd n) \<and> snd n \<in> accept (net nd) \<and> fst n = nd}))"
    by(simp add:ac_simps)
  also {
  have "(\<Union>n \<in> ((\<lambda>a. (Pair nd' a, Pair nd a)) ` accept (net nd))\<inverse> `` {n}. resolve (split_node nd nd' net) n) =
        {n'. n' = (nd',snd n) \<and> snd n \<in> accept (net nd) \<and> fst n = nd}"
    (is "?A = ?B")
  proof(intro antisym subsetI)
    fix x
    assume "x \<in> ?A"
    then obtain n' where n'n: "(n', n) \<in> {((nd', a), nd, a) |a. a \<in> accept (net nd)}"
                     and xin: "x \<in> resolve (split_node nd nd' net) n'" by(blast)
    from n'n obtain a where n'eq: "n' = (nd',a)" and nsplit: "n = (nd,a)"
                        and ain: "a \<in> accept (net nd)" by(blast)

    from fresh n'eq have dom_n': "resolve_dom (split_node nd nd' net,n')"
      by(auto intro: resolve.domintros
              simp:split_node_def decodes_to_def decode_step_def acceptor_node_def)
      
    from n'eq have "(decodes_to (split_node nd nd' net))\<inverse> `` {n'} = {}"
      using fresh_node_translateD[OF fresh] fresh_node_acceptD[OF fresh]
      by(subst split_decode,
         auto simp:decodes_to_def decode_step_def neq n'eq Un_Image converse_Un split_decode)
    hence "resolve (split_node nd nd' net) n' = {n'} \<inter> accepted_names (split_node nd nd' net)"
      by(simp add:resolve_simp[OF dom_n'])
    with xin have xeq: "x = n'" by(auto)
    with n'n neq show "x \<in> {n'. n' = (nd',snd n) \<and> snd n \<in> accept (net nd) \<and> fst n = nd}" by(auto)
  next
    fix x::name
    assume xin: "x \<in> ?B"
    hence "(x, n) \<in> {((nd', a), nd, a) |a. a \<in> accept (net nd)}" by(auto)
    moreover {
      from fresh have dom_x: "resolve_dom (split_node nd nd' net, (nd',snd n))"
        by(auto intro: resolve.domintros
                simp:split_node_def decodes_to_def decode_step_def acceptor_node_def)
      
      from xin have xeq: "x = (nd',snd n)" and snd_n: "snd n \<in> accept (net nd)"
                and fst_n: "fst n = nd" by(auto)
      from fst_n snd_n have "n \<in> accepted_names net"
        by(cases n, simp add:accepted_names_def)
      with xeq fst_n have "x \<in> rename (id(nd := nd')) ` accepted_names net"
        by(auto simp:rename_def)
      with xeq have "x \<in> accepted_names (split_node nd nd' net)"
        by(simp add:split_accepted[where net=net and nd'=nd', OF fresh_node_acceptD[OF fresh]])
      with xeq
      have "x \<in> resolve (split_node nd nd' net) x"
        by(simp, subst resolve_simp[OF dom_x], blast)
    }
    ultimately show "x \<in> ?A" by(blast)
  qed
  hence
    "({n} \<inter> rename (id(nd := nd')) ` accepted_names net \<union>
      ((\<Union>n'\<in>(decodes_to net)\<inverse> `` {n}. resolve (split_node nd nd' net) n') \<union> 
       {n'. n' = (nd',snd n) \<and> snd n \<in> accept (net nd) \<and> fst n = nd})) =
     ({n} \<inter> rename (id(nd := nd')) ` accepted_names net \<union>
      ((\<Union>n'\<in>(decodes_to net)\<inverse> `` {n}. resolve (split_node nd nd' net) n') \<union> 
       (\<Union>n \<in> ((\<lambda>a. (Pair nd' a, Pair nd a)) ` accept (net nd))\<inverse> `` {n}. resolve (split_node nd nd' net) n)))"
    by(simp)
  }
  also have
    "({n} \<inter> rename (id(nd := nd')) ` accepted_names net \<union>
      ((\<Union>n'\<in>(decodes_to net)\<inverse> `` {n}. resolve (split_node nd nd' net) n') \<union> 
       (\<Union>n \<in> ((\<lambda>a. (Pair nd' a, Pair nd a)) ` accept (net nd))\<inverse> `` {n}. resolve (split_node nd nd' net) n))) =
     ({n} \<inter> rename (id(nd := nd')) ` accepted_names net \<union>
     (\<Union>n'\<in>((decodes_to net)\<inverse> `` {n} \<union> ((\<lambda>a. (Pair nd' a, Pair nd a)) ` accept (net nd))\<inverse> `` {n}).
        resolve (split_node nd nd' net) n'))"
    by(simp)
  also have "... = rename id ` resolve (split_node nd nd' net) n"
    by(simp add:resolve_simp[OF dom'] split_accepted split_decode Un_Image converse_Un rename_id
                fresh_node_acceptD[OF fresh] fresh_node_translateD[OF fresh] neq)
  finally show "rename (id(nd := nd')) ` resolve net n = rename id ` resolve (split_node nd nd' net) n" .
qed
(*>*)

text {* From these two lemmas, we have view-equivalence under splitting. *}
lemma split_node_eq:
  fixes S :: "nodeid set" and nd nd' :: nodeid and net :: net
  assumes neq: "nd \<noteq> nd'"
      and wf_net: "wf_net net"
      and fresh: "fresh_node net nd'"
      and notin: "nd' \<notin> S"
    shows "view_eq_on S (id(nd := nd'), net) (id, split_node nd nd' net)"
(*<*)
  unfolding view_eq_on_def view_eq_def
proof(simp, intro ballI conjI allI impI)
  fix nd3 a
  assume nd3in: "nd3 \<in> S"
  with notin have notnd': "nd3 \<noteq> nd'" by(blast)
 
  from neq notnd' fresh wf_net
  show "resolve_dom (net, nd3, a) =
        resolve_dom (split_node nd nd' net, nd3, a)"
    by(simp add:split_node_domeq)

  assume "resolve_dom (net, nd3, a)"
  with assms notnd'
  show "rename (id(nd := nd')) ` view_from nd3 net a =
        rename id ` view_from nd3 (split_node nd nd' net) a"
    unfolding view_from_def by(intro split_node_resolveeq, auto)
qed
(*>*)

(*<*)
text {* Splitting preserves well-formedness. *}  
lemma wf_split_node:
  assumes wf: "wf_net net"
      and neq: "nd \<noteq> nd'"
      and fresh: "fresh_node net nd'"
  shows "wf_net (split_node nd nd' net)"
proof(rule wf_netI)
  fix nd2
  from wf
  show "finite (accept (split_node nd nd' net nd2))"
    by(auto dest:wf_net_acceptD simp:split_node_def acceptor_node_def redirector_node_def)
next
  fix n
  assume "resolve_dom (split_node nd nd' net, n)"
  with wf neq fresh
  have dom: "resolve_dom (net,n)" by(simp add:split_node_domeq)
    
  show "finite ((decodes_to (split_node nd nd' net))\<inverse> `` {n})"
  proof(cases)
    assume "fst n = nd'"
    thus ?thesis
      by(simp add:split_node_def Image_def decodes_to_def decode_step_def acceptor_node_def)
  next
    assume neq: "fst n \<noteq> nd'"
    show ?thesis
    proof(cases)
      assume eq: "fst n = nd"
        
      from dom wf have "finite ((decodes_to net)\<inverse> `` {n})"
        by(auto dest:wf_net_decodeD)
      with eq neq show ?thesis
        by(simp add:split_node_def Image_def decodes_to_def decode_step_def redirector_node_def)
    next
      assume neq': "fst n \<noteq> nd"
      from dom wf have "finite ((decodes_to net)\<inverse> `` {n})"
        by(auto dest:wf_net_decodeD)
      with neq neq' show ?thesis
        by(simp add:split_node_def Image_def decodes_to_def decode_step_def redirector_node_def)
    qed
  qed
qed
(*>*)
text {* Since a single split preserves equivalence, so does splitting a finite list of nodes
  (\autoref{eq:spliteq}): *}
primrec split_all :: "nodeid list \<Rightarrow> (nodeid \<Rightarrow> nodeid) \<Rightarrow> net \<Rightarrow> net"
  where "split_all [] _ net = net" |
        "split_all (nd#nds) f net = split_node nd (f nd) (split_all nds f net)"

(*<*)
lemma split_all_upd_comm:
  "nd \<notin> set nds \<Longrightarrow> (\<And>nd'. f nd' \<noteq> nd) \<Longrightarrow>
   split_all nds f (net(nd := x)) = (split_all nds f net)(nd := x)"
  by(induct nds, auto simp:split_node_def)

lemma fresh_split_all:
  assumes fresh: "fresh_node net x"
      and notin: "x \<notin> set nds"
      and noclash: "\<And>nd. nd \<in> set nds \<Longrightarrow> f nd \<noteq> x"
    shows "fresh_node (split_all nds f net) x"
  using notin noclash by(induct nds, auto intro:fresh fresh_split_node)

lemma wf_split_all:
  "wf_net net \<Longrightarrow>
   distinct nds \<Longrightarrow>
   (\<And>nd. nd \<in> set nds \<Longrightarrow> fresh_node net (f nd)) \<Longrightarrow>
   (\<And>nd. nd \<in> set nds \<Longrightarrow> f nd \<notin> set nds) \<Longrightarrow>
   inj_on f (set nds) \<Longrightarrow>
   wf_net (split_all nds f net)"
proof(induct nds, simp_all)
  fix nd nds
  assume wf: "wf_net (split_all nds f net)"
     and distinct: "nd \<notin> set nds \<and> distinct nds"
     and IH_fresh: "(\<And>nd'. nd' = nd \<or> nd' \<in> set nds \<Longrightarrow> fresh_node net (f nd'))"
     and IH_new: "(\<And>nd'. nd' = nd \<or> nd' \<in> set nds \<Longrightarrow> f nd' \<noteq> nd \<and> f nd' \<notin> set nds)"
     and inj: "inj_on f (set nds) \<and> f nd \<notin> f ` (set nds)"

  have "nd \<noteq> f nd"
  proof(rule ccontr)
    from IH_new have "f nd \<noteq> nd" by(auto)
    moreover assume "\<not> nd \<noteq> f nd"
    ultimately show False by(simp)
  qed
  moreover have "fresh_node (split_all nds f net) (f nd)"
  proof(rule fresh_split_all)
    from IH_fresh show "fresh_node net (f nd)" by(auto)
    from IH_new show "f nd \<notin> set nds" by(auto)
    fix nd'
    assume nd'in: "nd' \<in> set nds"
    from nd'in distinct have "nd \<noteq> nd'" by(auto)
    with nd'in have "f nd' \<in> f ` set nds" by(auto)
    with inj show "f nd' \<noteq> f nd" by(auto)
  qed
  ultimately
  show "wf_net (split_node nd (f nd) (split_all nds f net))"
    by(blast intro:wf_split_node wf)
qed
(*>*)

lemma view_eq_split_all:
  assumes distinct: "distinct nds"
      and nonds: "\<And>nd. f nd \<notin> set nds"
      and fresh: "\<And>nd. fresh_node net (f nd)"
      and inj: "inj_on f (set nds)"
      and wf: "wf_net net"
      and noS: "\<And>nd. f nd \<notin> S"
  shows "view_eq_on S (rename_list f nds , net) (id, split_all nds f net)"
(*<*)
    (is "view_eq_on S (rename_list f nds, net) (?B nds)")
  using distinct nonds inj
proof(induct nds, simp add:equivp_reflp[OF equivp_view_eq_on])
  fix nd::nodeid and nds
  assume distinct: "distinct (nd # nds)"
     and nonds: "\<And>nd'. f nd' \<notin> set (nd # nds)"
     and inj: "inj_on f (set (nd # nds))"
     and "distinct nds \<Longrightarrow> (\<And>nd. f nd \<notin> set nds) \<Longrightarrow> inj_on f (set nds) \<Longrightarrow>
          view_eq_on S (rename_list f nds, net) (id, split_all nds f net)"
  hence IH: "view_eq_on S (rename_list f nds, net) (id, split_all nds f net)" by(auto)
      
  from IH have "view_eq_on S ((\<lambda>x. if x = nd then f nd else x) o rename_list f nds, net)
                             ((\<lambda>x. if x = nd then f nd else x) o id, split_all nds f net)"
    by(rule view_eq_on_comp)
  hence "view_eq_on S (rename_list f (nd#nds), net)
                      (id(nd := f nd), split_all nds f net)"
    by(simp add:o_def fun_upd_def id_def)
  also have "view_eq_on S (id(nd := f nd), split_all nds f net)
                          (id, split_all (nd#nds) f net)"
  proof(simp, rule split_node_eq)
    from nonds show "nd \<noteq> f nd"
    proof(rule contrapos_nn)
      assume "nd = f nd"
      thus "f nd \<in> set (nd # nds)" by(auto)
    qed
    from wf distinct fresh nonds inj
    show "wf_net (split_all nds f net)" by(intro wf_split_all, auto)
    show "fresh_node (split_all nds f net) (f nd)"
    proof(rule fresh_split_all)
      show "fresh_node net (f nd)" by(rule fresh)
      from nonds show "f nd \<notin> set nds" by(auto)
    next
      fix nd'
      assume "nd' \<in> set nds"
      with distinct have "nd' \<in> set (nd # nds)" "nd \<noteq> nd'" by(auto)
      moreover have "nd \<in> set (nd # nds)" by(auto)
      moreover note inj
      ultimately show "f nd' \<noteq> f nd" by(blast dest:inj_onD)
    qed
    show "f nd \<notin> S" by(rule noS)
  qed
  finally show "view_eq_on S (rename_list f (nd # nds), net) (id, split_all (nd # nds) f net)" .
qed
(*>*)

(*<*)
subsubsection "Flattening"
text_raw {* \label{sec:isaflatten} *}

definition absorb :: "net \<Rightarrow> net"
  where "absorb net =
    (\<lambda>nd'. (net nd')\<lparr> translate := 
      (\<lambda>a. translate (net nd') a \<union> (\<Union>n\<in>translate (net nd') a. translate (net (fst n)) (snd n))) \<rparr>)"

lemma decode_absorb:
  "decodes_to (absorb net) = (decodes_to net O decodes_to net) \<union> decodes_to net"
proof(intro set_eqI)
  fix x::"name \<times> name"
  obtain n n' where "x = (n,n')" by(cases x, auto)
  thus "(x \<in> decodes_to (absorb net)) = (x \<in> decodes_to net O decodes_to net \<union> decodes_to net)"
  proof(simp, intro iffI)
    assume "(n,n') \<in> decodes_to (absorb net)"
    hence "n \<in> translate (net (fst n')) (snd n') \<or>
           (\<exists>x\<in>translate (net (fst n')) (snd n'). n \<in> translate (net (fst x)) (snd x))"
      by(simp add:absorb_def decodes_to_def decode_step_def)
    thus "(n, n') \<in> decodes_to net O decodes_to net \<or> (n, n') \<in> decodes_to net"
    proof
      assume "n \<in> translate (net (fst n')) (snd n')"
      thus ?thesis by(simp add:decodes_to_def decode_step_def)
    next
      assume "\<exists>x\<in>translate (net (fst n')) (snd n'). n \<in> translate (net (fst x)) (snd x)"
      then obtain x where "x \<in> translate (net (fst n')) (snd n')"
                      and "n \<in> translate (net (fst x)) (snd x)" by(blast)
      hence "(n,x) \<in> decodes_to net" "(x,n') \<in> decodes_to net"
        by(simp_all add:decodes_to_def decode_step_def)
      thus ?thesis by(auto)
    qed
  next
    assume "(n, n') \<in> decodes_to net O decodes_to net \<or> (n, n') \<in> decodes_to net"
    thus "(n, n') \<in> decodes_to (absorb net)"
    proof
      assume "(n, n') \<in> decodes_to net O decodes_to net"
      then obtain x where "(n,x) \<in> decodes_to net" "(x,n') \<in> decodes_to net" by(auto)
      thus ?thesis by(auto simp:decodes_to_def decode_step_def absorb_def)
    next
      assume "(n, n') \<in> decodes_to net"
      thus ?thesis by(simp add:decodes_to_def decode_step_def absorb_def)
    qed
  qed
qed

lemma decode_absorb_pow:
  "decodes_to ((absorb ^^ n) net) = (\<Union>i\<in>{1..2^n}. decodes_to net ^^ i)"
proof(induct n, simp)
  fix n
  assume IH: "decodes_to ((absorb ^^ n) net) = (\<Union>i\<in>{1..2^n}. decodes_to net ^^ i)"
  have "decodes_to ((absorb ^^ Suc n) net) =
        decodes_to ((absorb ^^ n) net) O decodes_to ((absorb ^^ n) net) \<union>
        decodes_to ((absorb ^^ n) net)"
    by(simp add:decode_absorb)
  also have "... = (\<Union>i\<in>{1..2^n}. decodes_to net ^^ i) O (\<Union>i\<in>{1..2^n}. decodes_to net ^^ i) \<union>
                   (\<Union>i\<in>{1..2^n}. decodes_to net ^^ i)" by(simp add:IH)
  also have "... = (\<Union>i\<in>{1..2^Suc n}. decodes_to net ^^ i)"
  proof(intro set_eqI iffI)
    fix x
    assume "x \<in> (\<Union>i\<in>{1..2^n}. decodes_to net ^^ i) O
                (\<Union>i\<in>{1..2^n}. decodes_to net ^^ i) \<union>
                (\<Union>i\<in>{1..2^n}. decodes_to net ^^ i)"
    thus "x \<in> (\<Union>i\<in>{1..2^Suc n}. decodes_to net ^^ i)"
    proof
      assume "x \<in> (\<Union>i\<in>{1..2 ^ n}. decodes_to net ^^ i) O (\<Union>i\<in>{1..2 ^ n}. decodes_to net ^^ i)"
      thus ?thesis
      proof
        fix a b c
        assume xeq: "x = (a,c)"
            and ab: "(a,b) \<in> (\<Union>i\<in>{1..2 ^ n}. decodes_to net ^^ i)"
            and bc: "(b,c) \<in> (\<Union>i\<in>{1..2 ^ n}. decodes_to net ^^ i)"
            
        from ab obtain i where ab': "(a,b) \<in> decodes_to net ^^ i" and iin: "i\<in>{1..2^n}" by(auto)
        from bc obtain j where bc': "(b,c) \<in> decodes_to net ^^ j" and jin: "j\<in>{1..2^n}"  by(auto)
            
        from iin jin have "i + j \<in> {1..2^Suc n}" by(auto)
        moreover from ab' bc' xeq have "x \<in> decodes_to net ^^ (i+j)" by(auto simp:relpow_add)
        ultimately show ?thesis by(blast)
      qed
    next
      assume "x \<in> (\<Union>i\<in>{1..2 ^ n}. decodes_to net ^^ i)"
      thus ?thesis by(auto)
    qed
  next
    fix x
    assume "x \<in> (\<Union>i\<in>{1..2 ^ Suc n}. decodes_to net ^^ i)"
    then obtain i where iin: "i \<in> {1..2 ^ Suc n}" and xdec: "x \<in> decodes_to net ^^ i" by(blast)
    show "x \<in> (\<Union>i\<in>{1..2 ^ n}. decodes_to net ^^ i) O (\<Union>i\<in>{1..2 ^ n}. decodes_to net ^^ i) \<union>
          (\<Union>i\<in>{1..2 ^ n}. decodes_to net ^^ i)"
    proof(cases)
      assume "i \<le> 2 ^ n"
      with iin have "i \<in> {1..2 ^ n}" by(auto)
      with xdec show ?thesis by(auto)
    next
      assume gt: "\<not> i \<le> 2 ^ n"
      hence "1 \<le> i - 2 ^ n" by(auto)
      with iin have diff_in: "i - 2 ^ n \<in> {1..2 ^ n}" by(auto)
          
      from gt have "2 ^ n + (i - 2 ^ n) = i" by(auto)
      with xdec have "x \<in> decodes_to net ^^ (2 ^ n + (i - 2 ^ n))" by(simp)
      hence "x \<in> decodes_to net ^^ (2 ^ n) O decodes_to net ^^ (i - 2 ^ n)"
        by(simp add:relpow_add)
      thus ?thesis
      proof
        fix a b c
        assume xeq: "x = (a,c)"
           and ab: "(a,b) \<in> decodes_to net ^^ 2 ^ n"
           and bc: "(b,c) \<in> decodes_to net ^^ (i - 2 ^ n)"
           
        from ab have "(a,b) \<in> (\<Union>i\<in>{1..2 ^ n}. decodes_to net ^^ i)" by(auto)
        moreover from bc diff_in have "(b,c) \<in> (\<Union>i\<in>{1..2 ^ n}. decodes_to net ^^ i)" by(blast)
        ultimately show ?thesis by(auto simp:xeq)
      qed
    qed
  qed
  finally show "decodes_to ((absorb ^^ Suc n) net) = (\<Union>i\<in>{1..2 ^ Suc n}. decodes_to net ^^ i)" .
qed

lemma accept_absorb:
  "accept (absorb net nd') = accept (net nd')"
  by(simp add:absorb_def)

lemma accepted_names_absorb:
  "accepted_names (absorb net) = accepted_names net"
  by(simp add:accepted_names_def accept_absorb)

lemma decode_absorb_trancl:
  "decodes_to (absorb net) \<subseteq> (decodes_to net)\<^sup>+"
  by(auto simp:decode_absorb)

lemma decode_absorb_rtrancl:
  "(decodes_to (absorb net))\<^sup>* = (decodes_to net)\<^sup>*"
proof(intro antisym)
  from decode_absorb_trancl
  have "(decodes_to (absorb net))\<^sup>* \<subseteq> ((decodes_to net)\<^sup>+)\<^sup>*" by(rule rtrancl_mono)
  thus "(decodes_to (absorb net))\<^sup>* \<subseteq> (decodes_to net)\<^sup>*" by(simp)
  
  have "(decodes_to net)\<^sup>* \<subseteq> (decodes_to net O decodes_to net)\<^sup>* \<union> (decodes_to net)\<^sup>*" by(blast)
  also have "... \<subseteq> (decodes_to (absorb net))\<^sup>*"
    unfolding decode_absorb by(rule rtrancl_Un_subset)
  finally  show "(decodes_to net)\<^sup>* \<subseteq> (decodes_to (absorb net))\<^sup>*" .
qed

lemma absorb_domeq:
  assumes wf: "wf_net net"
  shows "resolve_dom (absorb net, a) = resolve_dom (net, a)"
proof(intro iffI)
  assume "resolve_dom (absorb net, a)"
  hence "a \<in> Wellfounded.acc (decodes_to (absorb net))"
    by(simp add:resolve_dom_decode_acc)
  also have "... \<subseteq> Wellfounded.acc (decodes_to net)"
    by(rule acc_subset, simp add:decode_absorb)
  finally show "resolve_dom (net, a)"
    by(simp add:resolve_dom_decode_acc)
next
  assume "resolve_dom (net, a)"
  with wf have "\<exists>f. wf_rank f a net"
    by(blast intro:mkrank dest:wf_net_decodeD)
  then obtain f where rank: "wf_rank f a net" by(blast)
      
  have "wf_rank f a (absorb net)"
  proof(rule wf_rankI)
    fix x y
    assume "(x, a) \<in> (decodes_to (absorb net))\<^sup>*"
    also from decode_absorb_trancl have "... \<subseteq> ((decodes_to net)\<^sup>+)\<^sup>*"
      by(rule rtrancl_mono)
    also have "... = (decodes_to net)\<^sup>*" by(simp)
    finally have "(x, a) \<in> (decodes_to net)\<^sup>*" .
    with rank have rank': "wf_rank f x net" by(rule wf_reachable)
        
    assume "(y, x) \<in> decodes_to (absorb net)"
    with decode_absorb_trancl have "(y,x) \<in> (decodes_to net)\<^sup>+" by(auto)
    with rank' show "f y < f x" by(blast dest:wf_rank_tranclD)
  qed
  thus "resolve_dom (absorb net, a)" by(rule wf_resolve_dom)
qed
  
lemma wf_absorb:
  assumes wf: "wf_net net"
  shows "wf_net (absorb net)"
proof(rule wf_netI)
  fix nd
  from wf show "finite (accept (absorb net nd))"
    by(simp add:accept_absorb wf_net_acceptD)
next
  fix n
  assume "resolve_dom (absorb net, n)"
  with wf have dom: "resolve_dom (net, n)" by(simp add:absorb_domeq)
  with wf have fin: "finite ((decodes_to net)\<inverse> `` {n})" by(blast dest:wf_net_decodeD)
  show "finite ((decodes_to (absorb net))\<inverse> `` {n})"
  proof(simp add:decode_absorb Image_def, intro conjI)
    from fin show fin': "finite {y. (y, n) \<in> decodes_to net}" by(simp add:Image_def)
        
    have "{y. (y, n) \<in> decodes_to net O decodes_to net} =
          UNION {x. (x, n) \<in> decodes_to net} (\<lambda>x. {y. (y, x) \<in> decodes_to net})"
      by(auto)
    moreover {
      fix x
      assume "(x, n) \<in> decodes_to net"
      with dom have "resolve_dom (net, x)" by(blast intro: resolve_dom_downward)
      with wf have "finite ((decodes_to net)\<inverse> `` {x})" by(blast dest:wf_net_decodeD)
      hence "finite {y. (y, x) \<in> decodes_to net}" by(simp add:Image_def)
    }
    moreover note fin'
    ultimately show "finite {y. (y, n) \<in> decodes_to net O decodes_to net}" by(simp)
  qed
qed

lemma absorb_eq:
  fixes S :: "nodeid set" and nd nd' :: nodeid and net :: net
  assumes neq: "nd \<noteq> nd'"
      and wf_net: "wf_net net"
      and fresh: "fresh_node net nd'"
      and notin: "nd' \<notin> S"
    shows "view_eq_on S (id, net) (id, absorb net)"
proof(intro view_eq_onI view_eqI, simp_all add:rename_id view_from_def)
  thm absorb_domeq
  fix nd a
  assume ndS: "nd \<in> S"
  from wf_net show domeq: "resolve_dom (net, nd, a) = resolve_dom (absorb net, nd, a)"
    by(simp add:absorb_domeq)

  assume dom: "resolve_dom (net, nd, a)"
  with domeq have dom': "resolve_dom (absorb net, nd, a)" by(simp)

  from dom have "resolve net (nd, a) = accepted_names net \<inter> ((decodes_to net)\<inverse>)\<^sup>* `` {(nd,a)}"
    by(simp add:resolve_eval)
  also have "... = accepted_names net \<inter> ((decodes_to (absorb net))\<inverse>)\<^sup>* `` {(nd,a)}"
    by(simp add:rtrancl_converse decode_absorb_rtrancl)
  also from dom' have "... = resolve (absorb net) (nd, a)"
    by(simp add:resolve_eval accepted_names_absorb)
  finally show "resolve net (nd, a) = resolve (absorb net) (nd, a)" .
qed

definition detach :: "nodeid \<Rightarrow> net \<Rightarrow> net"
  where "detach nd net =
    net(nd := (net nd)\<lparr> translate := (\<lambda>a. translate (net nd) a \<inter> accepted_names net) \<rparr>)"

definition flatten :: "nodeid \<Rightarrow> net \<Rightarrow> net"
  where "flatten nd net =
    net(nd := (net nd)\<lparr> translate :=
      (\<lambda>a. resolve net (nd,a) - {(nd,a)}) \<rparr>)"

lemma accept_flatten:
  "accept (flatten nd net nd') = accept (net nd')"
  by(simp add:flatten_def)

lemma flatten_decode:
  assumes step: "(x,y) \<in> decodes_to (flatten nd net)"
      and dom: "resolve_dom (net,y)"
    shows "(x,y) \<in> (decodes_to net)\<^sup>*"
proof(cases)
  assume "fst y = nd"
  with step show ?thesis
    by(intro resolve_reachable[OF dom], cases y,
       simp add:decodes_to_def decode_step_def flatten_def)
next
  assume "fst y \<noteq> nd"
  with step show ?thesis
    by(auto simp:decodes_to_def decode_step_def flatten_def)
qed

lemma flatten_decode_path:
  assumes path: "(x,y) \<in> (decodes_to (flatten nd net))\<^sup>*"
      and dom: "resolve_dom (net,y)"
    shows "(x,y) \<in> (decodes_to net)\<^sup>*"
  using dom
proof(induct rule:rtrancl.induct[OF path], simp)
  fix a b c
  assume domc: "resolve_dom (net, c)"
     and bc: "(b, c) \<in> decodes_to (flatten nd net)"
  hence bc': "(b, c) \<in> (decodes_to net)\<^sup>*" by(blast intro: flatten_decode)
  with domc have domb: "resolve_dom (net,b)" by(blast intro:resolve_dom_reachable)
  moreover assume "resolve_dom (net, b) \<Longrightarrow> (a, b) \<in> (decodes_to net)\<^sup>*"
  ultimately have "(a, b) \<in> (decodes_to net)\<^sup>*" by(blast)
  with bc' show "(a, c) \<in> (decodes_to net)\<^sup>*" by(auto)
qed

lemma flatten_domle:
  assumes wf:  "wf_net net"
      and dom: "resolve_dom (net, n)"
    shows "resolve_dom (flatten nd net, n)"
proof -
  from wf dom have "\<exists>f. wf_rank f n net"
    by(blast dest:wf_net_decodeD intro:mkrank)
  then obtain f where rank: "wf_rank f n net" by(blast)

  have "wf_rank f n (flatten nd net)"
  proof(rule wf_rankI)
    fix x y
    assume step: "(y, x) \<in> decodes_to (flatten nd net)"
       and path: "(x, n) \<in> (decodes_to (flatten nd net))\<^sup>*"
       
    from path dom have path': "(x,n) \<in> (decodes_to net)\<^sup>*" by(rule flatten_decode_path)
    with dom have dom': "resolve_dom (net, x)" by(blast intro:resolve_dom_reachable)
    with step have step': "(y,x) \<in> (decodes_to net)\<^sup>*" by(rule flatten_decode)
        
    from path' step' have yx: "(y, x) \<in> (decodes_to net)\<^sup>*" by(auto)

    from step have "y \<noteq> x"
    proof(cases)
      assume "fst x = nd"
      with step show ?thesis by(auto simp:decodes_to_def decode_step_def flatten_def)
    next
      assume "fst x \<noteq> nd"
      with step have "(y,x) \<in> decodes_to net"
        by(simp add:decodes_to_def decode_step_def flatten_def)
      with path' rank have "f y < f x" by(blast dest:wf_rankD)
      thus "y \<noteq> x" by(auto)
    qed
    with yx have "(y, x) \<in> (decodes_to net)\<^sup>+" by(auto dest:rtranclD)
    moreover from rank path' have "wf_rank f x net" by(blast dest:wf_reachable)
    ultimately show "f y < f x" by(blast dest:wf_rank_tranclD)
  qed
  thus ?thesis by(rule wf_resolve_dom)
qed

end
(*>*)