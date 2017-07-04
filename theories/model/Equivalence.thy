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
theory Equivalence
  imports Resolution
begin
(*>*)

subsection {* View Equivalence *}
text_raw {* \label{sec:vieweq} *}
  
text {* A view is a function that encodes the result of all address resolutions beginning at a
  given node. *}

type_synonym view = "addr \<Rightarrow> name set"

definition view_from :: "nodeid \<Rightarrow> net \<Rightarrow> view"
  where "view_from node net = (\<lambda>addr. resolve net (node, addr))"

text {* A remapping is a renaming of nodes, leaving addresses intact. *}
type_synonym remap = "nodeid \<Rightarrow> nodeid"

definition rename :: "remap \<Rightarrow> name \<Rightarrow> name"
  where "rename m n = (m (fst n), snd n)"
    (*<*)
lemma rename_id:
  "rename id ` S = S"
  unfolding rename_def id_def by(auto)
    (*>*)

primrec rename_list :: "(nodeid \<Rightarrow> nodeid) \<Rightarrow> nodeid list \<Rightarrow> (nodeid \<Rightarrow> nodeid)"
  where "rename_list f [] = id" |
        "rename_list f (nd#nds) = (\<lambda>x. if x = nd then f nd else x) o (rename_list f nds)"

text {* Two nets are view-equivalent for some node, if the two views have the same domain, and
  give the same result for all addresses, modulo a renaming of accepting nodes. *}
definition view_eq :: "nodeid \<Rightarrow> (remap \<times> net) \<Rightarrow> (remap \<times> net) \<Rightarrow> bool"
  where "view_eq nd x y \<longleftrightarrow>
          (\<forall>a. resolve_dom (snd x,(nd,a)) = resolve_dom (snd y,(nd,a))) \<and>
          (\<forall>a. resolve_dom (snd x,(nd,a)) \<longrightarrow>
            rename (fst x) ` view_from nd (snd x) a =
            rename (fst y) ` view_from nd (snd y) a)"
    (*<*)
definition view_le :: "nodeid \<Rightarrow> (remap \<times> net) \<Rightarrow> (remap \<times> net) \<Rightarrow> bool"
  where "view_le nd x y \<longleftrightarrow>
          (\<forall>a. resolve_dom (snd x,(nd,a)) \<longrightarrow> resolve_dom (snd y,(nd,a))) \<and>
          (\<forall>a. resolve_dom (snd x,(nd,a)) \<longrightarrow>
            rename (fst x) ` view_from nd (snd x) a =
            rename (fst y) ` view_from nd (snd y) a)"
    (*>*)

definition view_eq_on :: "nodeid set \<Rightarrow> (remap \<times> net) \<Rightarrow> (remap \<times> net) \<Rightarrow> bool"
  where "view_eq_on S x y \<longleftrightarrow> (\<forall>nd\<in>S. view_eq nd x y)"
    (*<*)
definition view_le_on :: "nodeid set \<Rightarrow> (remap \<times> net) \<Rightarrow> (remap \<times> net) \<Rightarrow> bool"
  where "view_le_on S x y \<longleftrightarrow> (\<forall>nd\<in>S. view_le nd x y)"
    (*>*)
text {* Two nodes are equivalent (for a given net) if they have the same view. *}
definition node_eq :: "net \<Rightarrow> nodeid \<Rightarrow> nodeid \<Rightarrow> bool"
  where "node_eq net nd nd' \<longleftrightarrow> 
          (\<forall>a. resolve_dom (net,(nd,a)) = resolve_dom (net,(nd',a))) \<and>
          (\<forall>a. resolve_dom (net,(nd,a)) \<longrightarrow> view_from nd net a = view_from nd' net a)"
    (*<*)
lemma view_eq_empty:
  "view_eq_on {} x y"
  by(simp add:view_eq_on_def)

lemma view_eq_onI:
  "(\<And>nd. nd \<in> S \<Longrightarrow> view_eq nd x y) \<Longrightarrow> view_eq_on S x y"
  by(simp add:view_eq_on_def)

lemma view_le_onI:
  "(\<And>nd. nd \<in> S \<Longrightarrow> view_le nd x y) \<Longrightarrow> view_le_on S x y"
  by(simp add:view_le_on_def)

lemma view_eqI:
  "(\<And>a. resolve_dom (snd x, (nd,a)) = resolve_dom (snd y, (nd,a))) \<Longrightarrow>
   (\<And>a. resolve_dom (snd x, (nd,a)) \<Longrightarrow>
        rename (fst x) ` view_from nd (snd x) a =
        rename (fst y) ` view_from nd (snd y) a) \<Longrightarrow> view_eq nd x y"
  by(simp add:view_eq_def)

lemma view_leI:
  "(\<And>a. resolve_dom (snd x, (nd,a)) \<Longrightarrow> resolve_dom (snd y, (nd,a))) \<Longrightarrow>
   (\<And>a. resolve_dom (snd x, (nd,a)) \<Longrightarrow>
        rename (fst x) ` view_from nd (snd x) a =
        rename (fst y) ` view_from nd (snd y) a) \<Longrightarrow> view_le nd x y"
  by(simp add:view_le_def)

lemma view_eq_domD:
  "view_eq nd x y \<Longrightarrow> resolve_dom (snd x, nd, a) = resolve_dom (snd y, nd, a)"
  by(simp add:view_eq_def)

lemma view_le_domD:
  "view_le nd x y \<Longrightarrow> resolve_dom (snd x, nd, a) \<Longrightarrow> resolve_dom (snd y, nd, a)"
  by(simp add:view_le_def)

lemma view_eq_viewD:
  "view_eq nd x y \<Longrightarrow> resolve_dom (snd x, nd, a) \<Longrightarrow>
   rename (fst x) ` view_from nd (snd x) a = rename (fst y) ` view_from nd (snd y) a"
  by(simp add:view_eq_def)

lemma view_le_viewD:
  "view_le nd x y \<Longrightarrow> resolve_dom (snd x, nd, a) \<Longrightarrow>
   rename (fst x) ` view_from nd (snd x) a = rename (fst y) ` view_from nd (snd y) a"
  by(simp add:view_le_def)
    (*>*)
text {* Both view-equivalence and node-equivalence are proper equivalence relations. *}

lemma equivp_view_eq:
  "\<And>nd. equivp (view_eq nd)"
    (*<*)
  by(intro equivpI sympI transpI reflpI, simp_all add:view_eq_def)
    (*>*)

lemma equivp_view_eq_on:
  fixes S :: "nodeid set"
  shows "equivp (view_eq_on S)"
    (*<*)
  unfolding view_eq_on_def using equivp_view_eq
  by(blast intro:equivpI reflpI sympI transpI
           dest:equivp_reflp equivp_symp equivp_transp)

lemma equivp_node_eq:
  "\<And>net. equivp (node_eq net)"
  by(intro equivpI sympI transpI reflpI, simp_all add:node_eq_def)

lemma transp_view_le:
  "\<And>nd. transp (view_le nd)"
  by(intro transpI, simp add:view_le_def)

lemma transp_view_le_on:
  "\<And>S. transp (view_le_on S)"
  unfolding view_le_on_def
  using transp_view_le by(blast dest:transpD intro:transpI)

lemma view_eq_view_le:
  "view_eq nd x y \<Longrightarrow> view_le nd x y"
  by(simp add:view_eq_def view_le_def)

lemma view_eq_on_view_le_on:
  "view_eq_on S x y \<Longrightarrow> view_le_on S x y"
  by(simp add:view_eq_on_def view_le_on_def view_eq_view_le)

lemma view_eq_antisym:
  "view_le nd x y \<Longrightarrow> view_le nd y x \<Longrightarrow> view_eq nd x y"
  unfolding view_le_def view_eq_def by(blast)

lemma view_eq_on_antisym:
  "view_le_on S x y \<Longrightarrow> view_le_on S y x \<Longrightarrow> view_eq_on S x y"
  unfolding view_le_on_def view_eq_on_def by(blast intro:view_eq_antisym)

lemmas view_eq_symp = equivp_symp[OF equivp_view_eq]
lemmas view_eq_on_symp = equivp_symp[OF equivp_view_eq_on]

text {* Declare rules for transitivity reasoning. *}
lemmas [trans] = equivp_transp[OF equivp_view_eq_on] equivp_transp[OF equivp_view_eq]
                 transpD[OF transp_view_le_on] transpD[OF transp_view_le]
                 transpD[OF transp_view_le_on, OF view_eq_on_view_le_on]
                 transpD[OF transp_view_le, OF view_eq_view_le]
                 transpD[OF transp_view_le_on, OF _ view_eq_on_view_le_on]
                 transpD[OF transp_view_le, OF _ view_eq_view_le]
    (*>*)
text {* Both equivalence relations preserve resolution. *}

lemma node_eq_resolve:
  fixes nd nd' :: nodeid and net :: net and a :: addr
  shows "node_eq net nd nd' \<Longrightarrow> resolve_dom (net,nd,a) \<Longrightarrow> resolve net (nd,a) = resolve net (nd',a)"
    (*<*)
  by(simp add:node_eq_def view_from_def)
    (*>*)

lemma view_eq_resolve:
  fixes nd :: nodeid and x y :: "remap \<times> net" and a :: addr
  shows "view_eq nd x y \<Longrightarrow> resolve_dom (snd x,nd,a) \<Longrightarrow>
         rename (fst x) ` resolve (snd x) (nd,a) = rename (fst y) ` resolve (snd y) (nd,a)"
    (*<*)
  by(simp add:view_eq_def view_from_def)

lemma view_le_resolve:
  shows "view_le nd x y \<Longrightarrow> resolve_dom (snd x,nd,a) \<Longrightarrow>
         rename (fst x) ` resolve (snd x) (nd,a) = rename (fst y) ` resolve (snd y) (nd,a)"
  by(simp add:view_le_def view_from_def)
    (*>*)
text {* View-equivalence is preserved by any further node renaming. *}
    (*<*)
lemma view_le_comp:
  assumes le_fg: "view_le nd (f,net) (g,net')"
  shows "view_le nd (h o f,net) (h o g,net')"
proof(intro view_leI, simp_all)
  fix a
  assume dom: "resolve_dom (net, nd, a)"
  with le_fg show dom': "resolve_dom (net', nd, a)"
    by(auto dest:view_le_domD)

  show "rename (h \<circ> f) ` view_from nd net a = rename (h \<circ> g) ` view_from nd net' a"
    (is "?A (h o f) = ?B (h o g)")
  proof(intro set_eqI iffI)
    fix x
    assume "x \<in> ?A (h o f)"
    then obtain y where yin: "y \<in> view_from nd net a" and xeq: "x = rename (h o f) y"
      by(blast)
        
    let ?x' = "rename f y"
    from yin have "?x' \<in> ?A f" by(auto)
    with dom have "?x' \<in> ?B g" by(simp add: view_le_viewD[OF le_fg, simplified])
    then obtain y' where y'in: "y' \<in> view_from nd net' a" and x'eq: "?x' = rename g y'"
      by(blast)

    from xeq x'eq have "x = rename (h o g) y'" by(simp add:rename_def)
    with y'in show "x \<in> ?B (h o g)" by(blast)
  next
    fix x
    assume "x \<in> ?B (h o g)"
    then obtain y where yin: "y \<in> view_from nd net' a" and xeq: "x = rename (h o g) y"
      by(blast)
        
    let ?x' = "rename g y"
    from yin have "?x' \<in> ?B g" by(auto)
    with dom have "?x' \<in> ?A f" by(simp add: view_le_viewD[OF le_fg, simplified])
    then obtain y' where y'in: "y' \<in> view_from nd net a" and x'eq: "?x' = rename f y'"
      by(blast)

    from xeq x'eq have "x = rename (h o f) y'" by(simp add:rename_def)
    with y'in show "x \<in> ?A (h o f)" by(blast)
  qed
qed
    (*>*)
lemma view_eq_comp:
  "view_eq nd (f,net) (g,net') \<Longrightarrow> view_eq nd (h o f,net) (h o g,net')"
    (*<*)
  by(blast intro:view_eq_antisym view_le_comp
     dest:view_eq_view_le view_eq_view_le[OF view_eq_symp])

lemma view_le_on_comp:
  "view_le_on S (f,net) (g,net') \<Longrightarrow> view_le_on S (h o f,net) (h o g,net')"
  by(simp add:view_le_comp view_le_on_def)

lemma view_eq_on_comp:
  "view_eq_on S (f,net) (g,net') \<Longrightarrow> view_eq_on S (h o f,net) (h o g,net')"
  by(simp add:view_eq_comp view_eq_on_def)
(*>*)
text {* For transformations that add nodes, we need to know that the new node has no descendents
  or ancestors. *}
definition fresh_node :: "net \<Rightarrow> nodeid \<Rightarrow> bool"
  where "fresh_node net nd \<longleftrightarrow>
          (\<forall>a. translate (net nd) a = {}) \<and>
          (\<forall>x y. (x,y) \<in> decodes_to net \<longrightarrow> fst x \<noteq> nd) \<and>
          accept (net nd) = {}"

(*<*)
lemma fresh_node_translateD: "\<And>net nd a. fresh_node net nd \<Longrightarrow> translate (net nd) a = {}"
  by(simp add:fresh_node_def)
lemma fresh_node_reachableD: "\<And>net nd x y. fresh_node net nd \<Longrightarrow> (x,y) \<in> decodes_to net \<Longrightarrow> fst x \<noteq> nd"
  unfolding fresh_node_def by(blast)
lemma fresh_node_acceptD: "\<And>net nd. fresh_node net nd \<Longrightarrow> accept (net nd) = {}"
  by(simp add:fresh_node_def)

end
(*>*)