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
theory Resolution
  imports Model
begin
(*>*)

subsection {* Resolution *}
text_raw {* \label{sec:isares} *}
  
(* XXX - report function package failure.  Form 1 should work. *)
(*
function (domintros) f :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "f R a = insert a (\<Union> {f R a' |a'. (a',a) \<in> R})"
  by(pat_completeness, auto)
    
thm f.domintros

function (domintros) g :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "g R a = insert a (\<Union>a'. if (a',a) \<in> R then g R a' else {})"
  by(pat_completeness, auto)

thm g.domintros
*)

text {* To resolve an input name, start with the name itself if the net accepts it, and recurse on
  all names reachable via the @{term decodes_to} relation *}
function (domintros) resolve :: "net \<Rightarrow> name \<Rightarrow> name set"
  where "resolve net n =
   ({n} \<inter> accepted_names net) \<union>
   (\<Union>n'. if (n',n) \<in> decodes_to net then resolve net n' else {})"
  by(pat_completeness, auto)
    (*<*)
text {* This is a nicer evaluation rule than what the function package gives us.  Unfortunately
  we can't specify @{term resolve} like this directly, or we get a degenerate domain introduction
  rule. *}
lemma resolve_simp:
  fixes net n
  assumes dom: "resolve_dom (net,n)"
  shows "resolve net n = ({n} \<inter> accepted_names net) \<union>
                         (\<Union>n' \<in> (decodes_to net)\<inverse> `` {n}. resolve net n')"
proof -
  have "(\<Union>n' \<in> (decodes_to net)\<inverse> `` {n}. resolve net n') =
        (\<Union>n'. if (n',n) \<in> decodes_to net then resolve net n' else {})"
    by(intro equalityI subsetI, auto)
  thus ?thesis
    by(simp add:resolve.psimps[OF dom])
qed

text {* Likewise, these are cleaner introduction and induction rules for @{term resolve_dom}, that
  avoid splitting tuples. *}
lemma resolve_domI:
  fixes y
  shows "(\<And>x. (x,y) \<in> decodes_to net \<Longrightarrow> resolve_dom (net,x)) \<Longrightarrow> resolve_dom (net,y)"
  by(cases y, auto intro:resolve.domintros)

lemma resolve_induct:
  assumes dom: "resolve_dom (net,n)"
      and IH: "(\<And>n. resolve_dom (net, n) \<Longrightarrow>
                    (\<And>x. (x, n) \<in> decodes_to net \<Longrightarrow>
                     P net x) \<Longrightarrow> P net n)"
    shows "P net n"
proof -
  have "(\<forall>n. resolve_dom (net,n) \<longrightarrow> (\<forall>x. (x,n) \<in> decodes_to net \<longrightarrow> P net x) \<longrightarrow> P net n) \<longrightarrow>
        P net n \<and> resolve_dom (net,n)"
    by(rule resolve.pinduct[OF dom], intro impI conjI, auto)
  with dom IH show "P net n" by(blast)
qed
    (*>*)
text {* The defining relation for @{term resolve} is simply @{term decodes_to}: *}
lemma resolve_rel_decodes_to:
  "resolve_rel x y \<longleftrightarrow> (fst x = fst y) \<and> (snd x, snd y) \<in> decodes_to (fst x)"
  by(cases x, cases y, auto elim:resolve_rel.cases intro:resolve_rel.intros)
    (*<*)
lemma resolve_dom_downward:
  assumes dom: "resolve_dom (net, x)"
      and step: "(y,x) \<in> decodes_to net"
    shows "resolve_dom (net, y)"
  using assms by(auto intro:accp_downward simp:resolve_rel_decodes_to)

text {* Any name in the domain of @{term resolve} is in the accessible part of the
  @{term decodes_to} relation. *}
lemma resolve_dom_decodes_to:
  assumes rd: "resolve_dom x"
  shows "snd x \<in> Wellfounded.acc (decodes_to (fst x))"
proof(rule accp.induct[OF rd])
  fix x
  assume IH: "\<And>y. resolve_rel y x \<Longrightarrow> snd y \<in> Wellfounded.acc (decodes_to (fst y))"
  show "snd x \<in> Wellfounded.acc (decodes_to (fst x))"
  proof(rule accI)
    fix y
    assume "(y, snd x) \<in> decodes_to (fst x)"
    hence "resolve_rel (fst x, y) x" by(simp add:resolve_rel_decodes_to)
    thus "y \<in> Wellfounded.acc (decodes_to (fst x))" by(auto dest:IH)
  qed
qed

lemma resolve_dom_reachable:
  assumes path: "(x,y) \<in> (decodes_to net)\<^sup>*"
      and dom: "resolve_dom (net,y)"
    shows "resolve_dom (net, x)"
proof -
  from path have "resolve_rel\<^sup>*\<^sup>* (net,x) (net,y)"
  proof(induct y, simp)
    fix y z
    assume "(y, z) \<in> decodes_to net"
    hence "resolve_rel (net,y) (net,z)" by(simp add:resolve_rel_decodes_to)
    moreover assume "resolve_rel\<^sup>*\<^sup>* (net, x) (net, y)"
    ultimately show "resolve_rel\<^sup>*\<^sup>* (net, x) (net, z)" by(auto)
  qed
  with dom show ?thesis by(rule accp_downwards)
qed

lemma resolve_rel_decodes_to2:
  "resolve_rel = (\<lambda>x y. fst x = fst y \<and> (snd x, snd y) \<in> decodes_to (fst x))"
  by(intro ext, simp add:resolve_rel_decodes_to)

lemma resolve_dom_decode_acc:
  "resolve_dom (net, a) \<longleftrightarrow> a \<in> Wellfounded.acc (decodes_to net)"
proof(simp add:acc_def, simp add:resolve_rel_decodes_to2, intro iffI)
  assume "Wellfounded.accp (\<lambda>x y. fst x = fst y \<and> (snd x, snd y) \<in> decodes_to (fst x)) (net, a)"
  thus "Wellfounded.accp (\<lambda>x xa. (x, xa) \<in> decodes_to net) a"
    by(auto intro:injI accp_image_push)
next
  assume "Wellfounded.accp (\<lambda>x xa. (x, xa) \<in> decodes_to net) a"
  thus "Wellfounded.accp (\<lambda>x y. fst x = fst y \<and> (snd x, snd y) \<in> decodes_to (fst x)) (net, a)"
    by(rule accp_image_pull, auto)
qed

lemma resolve_reachable:
  assumes dom: "resolve_dom (net,n)"
      and resolve: "n' \<in> resolve net n"
  shows "(n',n) \<in> (decodes_to net)\<^sup>*"
  using resolve
proof(induct rule:resolve_induct[OF dom])
  fix n
  assume IH: "\<And>x. (x, n) \<in> decodes_to net \<Longrightarrow> n' \<in> resolve net x \<Longrightarrow> (n', x) \<in> (decodes_to net)\<^sup>*"
     and res: "n' \<in> resolve net n"
     and dom: "resolve_dom (net, n)"
  show "(n', n) \<in> (decodes_to net)\<^sup>*"
  proof(cases "n' = n", simp)
    assume "n' \<noteq> n"
    with res dom obtain x where step: "(x,n) \<in> decodes_to net" and "n' \<in> resolve net x"
      by(auto simp:resolve_simp)
    hence "(n',x) \<in> (decodes_to net)\<^sup>*"
      by(rule IH)
    with step show "(n',n) \<in> (decodes_to net)\<^sup>*"
      by(simp)
  qed
qed
    (*>*)
text {* We can express resolution in an equivalent non-recursive fashion, as the image of the
  closure of the decoding relation: *}
lemma resolve_eval:
  assumes dom: "resolve_dom (net, n)"
  shows "resolve net n = accepted_names net \<inter> ((decodes_to net)\<inverse>)\<^sup>* `` {n}"
    (*<*)
proof(induct rule:resolve_induct[OF dom])
  fix n
  assume dom: "resolve_dom (net, n)"
     and IH: "\<And>x. (x, n) \<in> decodes_to net \<Longrightarrow>
                  resolve net x = accepted_names net \<inter> ((decodes_to net)\<inverse>)\<^sup>* `` {x}"

  from dom
  have "resolve net n =
    {n} \<inter> accepted_names net \<union> (\<Union>n'\<in>(decodes_to net)\<inverse> `` {n}. resolve net n')"
    by(simp add:resolve_simp)
  also have "... =
    {n} \<inter> accepted_names net \<union>
    (\<Union>n'\<in>(decodes_to net)\<inverse> `` {n}. accepted_names net \<inter> ((decodes_to net)\<inverse>)\<^sup>* `` {n'})"
    by(simp add:IH)
  also have "... =
    accepted_names net \<inter> ({n} \<union> (\<Union>n'\<in>(decodes_to net)\<inverse> `` {n}. ((decodes_to net)\<inverse>)\<^sup>* `` {n'}))"
    by(auto)
  also {
    have "(\<Union>n'\<in>(decodes_to net)\<inverse> `` {n}. ((decodes_to net)\<inverse>)\<^sup>* `` {n'}) = ((decodes_to net)\<inverse>)\<^sup>+ `` {n}"
      by(auto simp:Image_def trancl_converse rtrancl_converse dest:tranclD2)
    hence "accepted_names net \<inter> ({n} \<union> (\<Union>n'\<in>(decodes_to net)\<inverse> `` {n}. ((decodes_to net)\<inverse>)\<^sup>* `` {n'})) =
           accepted_names net \<inter> ({n} \<union> ((decodes_to net)\<inverse>)\<^sup>+ `` {n})"
      by(simp)
  }
  also {
    have "{n} \<union> ((decodes_to net)\<inverse>)\<^sup>+ `` {n} = ((decodes_to net)\<inverse>)\<^sup>* `` {n}"
      by(auto simp:trancl_converse rtrancl_converse rtrancl_eq_or_trancl)
    hence "accepted_names net \<inter> ({n} \<union> ((decodes_to net)\<inverse>)\<^sup>+ `` {n}) =
           accepted_names net \<inter> ((decodes_to net)\<inverse>)\<^sup>* `` {n}"
      by(simp)
  }
  finally show "resolve net n = accepted_names net \<inter> ((decodes_to net)\<inverse>)\<^sup>* `` {n}" .
qed
    (*>*)
subsection "Well-Formed Decoding Nets"
text_raw {* \label{sec:isawfnet} *}

text {* The most general condition for the decoding of a given name to be well-defined is that the
  decoding process terminates i.e. that all paths of decoding steps (elements of the decodes-to
  relation) are finite (we eventually reach a node that either accepts its input address, or
  faults).

  A well-formed rank function @{term f} assigns a natural number to every name, such that if some
  name @{term n} decodes to @{term n'}, @{term "f n' < f n"}.  From this, it is trivial to show
  that decoding terminates.  Note that it is only necessary for the ranking to be well-formed for
  the name that we're resolving: it may not be possible to assign a consistent ranking to all names,
  that is well-formed for all starting points, although in well-designed systems it probably should
  be. *}

definition wf_rank :: "(name \<Rightarrow> nat) \<Rightarrow> name \<Rightarrow> net \<Rightarrow> bool"
  where
    "wf_rank f n net \<longleftrightarrow>
      (\<forall>x y. (x,n) \<in> rtrancl (decodes_to net) \<and> (y,x) \<in> decodes_to net \<longrightarrow> f y < f x)"
    (*<*)
lemma wf_rankI:
  "(\<And>x y. (x,n) \<in> rtrancl (decodes_to net) \<Longrightarrow> (y,x) \<in> decodes_to net \<Longrightarrow> f y < f x) \<Longrightarrow>
   wf_rank f n net"
  unfolding wf_rank_def by(auto)

lemma wf_rankD:
  "wf_rank f x net \<Longrightarrow> (z,y) \<in> decodes_to net \<Longrightarrow> (y,x) \<in> (decodes_to net)\<^sup>* \<Longrightarrow> f z < f y"
  unfolding wf_rank_def by(blast)

text {* If @{term f} is well-formed at @{term x}, and @{term y} is reachable from @{term x},
  then @{term f} is well-formed at @{term y}. *}
lemma wf_reachable:
  assumes wf_x: "wf_rank f x net" and reachable: "(y,x) \<in> (decodes_to net)\<^sup>*"
  shows "wf_rank f y net"
proof(rule wf_rankI)
  fix w z
  assume "(w,y) \<in> (decodes_to net)\<^sup>*"
  with reachable have "(w,x) \<in> (decodes_to net)\<^sup>*" by(auto)
  moreover assume "(z,w) \<in> decodes_to net"
  moreover note wf_x
  ultimately show "f z < f w" unfolding wf_rank_def by(blast)
qed

lemma wf_rank_tranclD:
  assumes wf: "wf_rank f n net"
      and trancl: "(n',n) \<in> (decodes_to net)\<^sup>+"
    shows "f n' < f n"
  using wf
proof(induct rule:trancl.induct[OF trancl])
  fix a b c
  assume step: "(b, c) \<in> decodes_to net"
     and wf: "wf_rank f c net"
  thus bc: "f b < f c"
    unfolding wf_rank_def by(cases b, cases c, auto)
      
  from step wf have "wf_rank f b net" by(blast intro:wf_reachable)
  moreover assume IH: "wf_rank f b net \<Longrightarrow> f a < f b"
  ultimately show "f a < f c" using bc by(simp)
qed

text {* With this lemma, we can construct well-formed rankings recursively: if @{term f} is
  well-formed for all predecessors of @{term x}, then we need only assign a greater rank to
  @{term x} than to any of its predecessors. *}
lemma wf_rank_step:
  fixes f x net
  assumes wf_step: "\<And>y. (y,x) \<in> decodes_to net \<Longrightarrow> wf_rank f y net"
      and rank_step: "\<And>y. (y,x) \<in> decodes_to net \<Longrightarrow> f y < f x"
    shows "wf_rank f x net"
proof(rule wf_rankI)
  fix y z
  assume yx: "(y,x) \<in> (decodes_to net)\<^sup>*"
     and zy: "(z,y) \<in> decodes_to net"
  show "f z < f y"
  proof(cases)
    assume "y = x"
    with zy rank_step show ?thesis by(auto)
  next
    assume "y \<noteq> x"
    with yx have "(y,x) \<in> (decodes_to net)\<^sup>+"
      by(auto dest:rtranclD)
    then obtain w where "(y,w) \<in> (decodes_to net)\<^sup>*" and "(w,x) \<in> decodes_to net"
      by(blast dest:tranclD2)
    hence "wf_rank f y net" by(blast intro:wf_step wf_reachable)
    with zy show ?thesis unfolding wf_rank_def by(blast)
  qed
qed
    (*>*)
text {* We use our well-formedness predicate to insist that all node both accept and translate
  a finite set of addresses.  While this isn't strictly necessary for a lot of the theory, it's
  essential for termination. *}
definition wf_net :: "net \<Rightarrow> bool"
  where "wf_net net \<longleftrightarrow>
    (\<forall>nd. finite (accept (net nd))) \<and>
    (\<forall>n. resolve_dom (net,n) \<longrightarrow> finite ((decodes_to net)\<inverse> `` {n}))"
    (*<*)
lemma wf_net_acceptD: "wf_net net \<Longrightarrow> finite (accept (net nd))" by(simp add:wf_net_def)
lemma wf_net_decodeD: "wf_net net \<Longrightarrow> resolve_dom (net,n) \<Longrightarrow> finite ((decodes_to net)\<inverse> `` {n})"
  unfolding wf_net_def by(blast)

lemma wf_netI:
  "(\<And>nd. finite (accept (net nd))) \<Longrightarrow>
   (\<And>n. resolve_dom (net,n) \<Longrightarrow> finite ((decodes_to net)\<inverse> `` {n})) \<Longrightarrow>
   wf_net net"
  by(simp add:wf_net_def)
    (*>*)
subsection {* Termination *}
text_raw {* \label{sec:isaterm} *}

text {* If we can supply a ranking function that is well-formed for all names reachable from the
  name we wish to decode, then the decoding function is well-defined here (this name lies in its
  \emph{domain}). *}
lemma wf_resolve_dom:
  fixes f :: "name \<Rightarrow> nat" and n :: name and net :: net
  assumes wf_at: "wf_rank f n net"
  shows "resolve_dom (net,n)"
proof -
  {
    text {* We argue by (strong) induction on the rank of the name, but we need to carry the
      assumption of reachability into the induction hypothesis (as otherwise we can't appeal to a
      well-formed ranking.  We then trivially discard this assumption as @{term n} is reachable from
      itself, by definition. *}
    fix a
    assume "(a,n) \<in> (decodes_to net)\<^sup>*"
    hence "resolve_dom (net,a)"
    proof(induct "f a" arbitrary:a rule:nat_less_induct)
      fix b
      text {* Assume the current node is reachable, and all reachable nodes of lesser rank lie in
        the domain of @{term resolve}. *}
      assume reachable: "(b,n) \<in> (decodes_to net)\<^sup>*"
         and IH: "\<forall>m<f b. \<forall>x. m = f x \<longrightarrow> (x,n) \<in> (decodes_to net)\<^sup>* \<longrightarrow> resolve_dom (net, x)"
         
      text {* We show that the arguments of any recursive call to @{term resolve} must lie in
        the domain, as new node is both reachable, and has strictly lesser rank, thanks to well-
        formedness. *}
      show "resolve_dom (net, b)"
      proof(rule resolve_domI)
        fix a
        text {* Assume that there \emph{is} a translation/decoding step.  We don't need to show
          anything for the terminating case, as there's no recursive call. *}
        assume step: "(a,b) \<in> decodes_to net"

        text {* The two names lie in the decoding relation, and the new name is also reachable
          from @{term n}. *}
        from step reachable have reachable_yz: "(a,n) \<in> (decodes_to net)\<^sup>*" by(simp)

        text {* From the (assumed) reachability of @{term b}, we can appeal to well-formedness to
          show that the rank decreases. *}
        from wf_at reachable step have "f a < f b"
          unfolding wf_rank_def by(blast)
        text {* Thus with the reachability of the new name, we have the result by appealing to the
          induction hypothesis. *}
        with reachable_yz IH show "resolve_dom (net, a)" by(blast)
      qed
    qed
  }
  text {* Finally, we discharge the reachability assumption. *}
  thus ?thesis by(auto)
qed

text {* This is the converse of the previous lemma, for decoding nets that with finite branching:
  If a single decoding step maps a name to a finite number of new names, then there must exist a
  well-formed ranking for each resolvable name. *}
lemma mkrank:
  fixes  n :: name and net :: net
  assumes branching: "\<And>n. resolve_dom (net,n) \<Longrightarrow> finite ((decodes_to net)\<inverse> `` {n})"
  shows "resolve_dom (net,n) \<Longrightarrow> \<exists>f. wf_rank f n net"
proof(induction "(net,n)" arbitrary:n rule:accp.induct)
  fix n
  text {* Assume that there exists a well-formed ranking for every direct descendent. *}
  assume IH: "\<And>n'. resolve_rel (net, n') (net, n) \<Longrightarrow> \<exists>f. wf_rank f n' net"
     and dom: "\<And>y. resolve_rel y (net, n) \<Longrightarrow> resolve_dom y"
     
  have rd: "resolve_dom (net,n)" by(blast intro:accp.intros dom)

  text {* By appealing to the axiom of choice (although as we're finite we could do without),
    construct @{term g} which, for every ancestor @{term n'} of @{term n}, gives a ranking function
    that is well-formed at @{term n'}. *}
  from IH
  have "\<forall>n'\<in> (decodes_to net)\<inverse> `` {n}. \<exists>f. wf_rank f n' net"
    by(blast intro:resolve_rel.intros)
  hence "\<exists>g. \<forall>n'\<in> (decodes_to net)\<inverse> `` {n}. wf_rank (g n') n' net"
    by(rule bchoice)
  then obtain g where wf_g: "\<forall>n' \<in> (decodes_to net)\<inverse> `` {n}. wf_rank (g n') n' net"
    by(blast dest:bchoice)

  text {* For any node @{term n'}, this is the set of its ancestors that are direct descendents
    of @{term n} i.e. the set of nodes that any path from @{term n} to @{term n'} \emph{must}
    pass through.  This set is finite. *}
  let "?ancs n'" = "{n''. (n'',n) \<in> decodes_to net \<and> (n',n'') \<in> (decodes_to net)\<^sup>*}"
  have "\<And>x. ?ancs x \<subseteq> (decodes_to net)\<inverse> `` {n}" by(auto)
  with branching rd have finite_ancs: "\<And>x. finite (?ancs x)" by(blast dest:finite_subset)

  text {* From @{term g}, construct @{term g'}, by taking, for each @{term n'}, the least rank
    assigned it by any of the well-formed rankings associated with its ancestors.  This new
    ranking is still well-formed for all of the direct descendents of @{term n}. *}
  let ?g' = "\<lambda>n'. Min ((\<lambda>n''. g n'' n') ` ?ancs n')"
  have wf_g': "\<forall>n' \<in> (decodes_to net)\<inverse> `` {n}. wf_rank ?g' n' net"
  proof(intro ballI wf_rankI)
    fix w x y
    text {* Assume @{term y} and @{term x} are reachable, and in the decode relation.  They
      therefore have the same set of ancestors. *}
    assume "w \<in> (decodes_to net)\<inverse> `` {n}"
    hence wn: "(w,n) \<in> decodes_to net" by(simp)
    assume xw: "(x,w) \<in> (decodes_to net)\<^sup>*"
       and yx: "(y,x) \<in> decodes_to net"

    text {* We show that for any ancestor of @{term x}, the rank assigned @{term x} is greater
      than the new rank we've constructed for @{term y}, and thus so is the minimum over these
      i.e. @{term g'}.*}
    show "?g' y < ?g' x"
    proof(intro iffD2[OF Min_gr_iff])
      text {* The ancestors are finite, and there is at least one. *}
      from finite_ancs show "finite ((\<lambda>n''. g n'' x) ` ?ancs x)" by(auto)
      from wn xw show "(\<lambda>n''. g n'' x) ` ?ancs x \<noteq> {}" by(blast)

      show "\<forall>a\<in>(\<lambda>n''. g n'' x) ` ?ancs x. Min ((\<lambda>n''. g n'' y) ` ?ancs y) < a"
      proof
        fix a
        assume "a \<in> (\<lambda>n''. g n'' x) ` ?ancs x"
        then obtain n' where step: "n' \<in> (decodes_to net)\<inverse> `` {n}"
                         and anc:  "(x,n') \<in> (decodes_to net)\<^sup>*"
                         and aeq: "a = g n' x" by(blast)

        text {* As any ancestor @{term n'} of @{term x} is also an ancestor of @{term y}, we can
          appeal to well-formedness to show that @{term "g n' y < g n' x"}.  It thus follows that
          the minimum is also lower. *}
        from anc yx have "(y,n') \<in> (decodes_to net)\<^sup>*" by(auto)
        with step have "g n' y \<in> (\<lambda>n''. g n'' y) ` ?ancs y" by(blast)
        moreover from finite_ancs have "finite ((\<lambda>n''. g n'' y) ` ?ancs y)" by(auto)
        ultimately have "Min ((\<lambda>n''. g n'' y) ` ?ancs y) \<le> g n' y" by(auto)
        also {
          from step wf_g have "wf_rank (g n') n' net" by(blast)
          with yx anc have "g n' y < g n' x" unfolding wf_rank_def by(blast)
        }
        finally show "Min ((\<lambda>n''. g n'' y) ` ?ancs y) < a" by(simp add:aeq)
      qed
    qed
  qed

  text {* We will appeal to the fact that we must be in the accessible portion of the decode
    relation to show that @{term n} can never appear as a descendent of itself, and can thus be
    assigned a higher rank than all of its descendents. *}
  from rd have nacc: "n \<in> Wellfounded.acc (decodes_to net)"
    by(auto dest:resolve_dom_decodes_to)

  text {* Finally, we construct our ranking function by assigning to @{term n} a rank greater than
    any of its descendents.  Doing so relies on there being only finitely many of these. *}
  let ?max = "Max (?g' ` (decodes_to net)\<inverse> `` {n})"
  let ?h = "?g'(n := Suc ?max)"
  have "wf_rank ?h n net"
    text {* We can show this be appealing to the well-formedness for each descendents that we just
      proved, and the fact that we assigned a greater rank to @{term n}. *}
  proof(rule wf_rank_step)
    fix y
    assume yn: "(y,n) \<in> decodes_to net"
    text {* We must show that the ranking is still well-defined for all descendents, even though
      we've changed the rank assigned to @{term n}.  This is where we need to know that @{term n}
      never appears as its own descendent. *}
    show "wf_rank ?h y net"
    proof(rule wf_rankI)
      fix x z
      assume xy: "(x,y) \<in> (decodes_to net)\<^sup>*"
         and zx: "(z,x) \<in> decodes_to net"

      text {* Appeal to the absence of loops in the accessible portion. *}
      from xy yn have xreach: "(x,n) \<in> (decodes_to net)\<^sup>+" by(auto)
      with nacc have x_ne_n: "x \<noteq> n" by(auto dest:no_loops_acc)

      from zx xy yn have "(z,n) \<in> (decodes_to net)\<^sup>+" by(auto)
      with nacc have z_ne_n: "z \<noteq> n" by(auto dest:no_loops_acc)
      
      from yn have "y\<in>(decodes_to net)\<inverse> `` {n}" by(simp)
      with wf_g' have wf_g_y: "wf_rank ?g' y net" by(simp)
          
      text {* Appeal to well-formedness. *}
      from wf_g_y zx xy have "?g' z < ?g' x" unfolding wf_rank_def by(blast)
      thus "?h z < ?h x" by(simp add:x_ne_n z_ne_n)
    qed

    text {* Showing that the rank increases is now trivial. *}
    from nacc yn have y_ne_n: "y \<noteq> n" by(auto dest:no_loops_acc)
    from branching rd yn
    show "?h y < ?h n"
      by(simp add:y_ne_n, intro le_imp_less_Suc[OF Max_ge], auto)
  qed
  thus "\<exists>f. wf_rank f n net" by(blast)
qed
(*<*)
lemma resolve_rank:
  assumes rank: "wf_rank f n net"
      and resolve: "n' \<in> resolve net n"
      and neq: "n' \<noteq> n"
    shows "f n' < f n"
proof -
  from rank have dom: "resolve_dom (net, n)" by(rule wf_resolve_dom)
  with resolve have "(n',n) \<in> (decodes_to net)\<^sup>*" by(blast intro:resolve_reachable)
  with neq have "(n',n) \<in> (decodes_to net)\<^sup>+" by(auto dest:rtranclD)
  with rank show ?thesis by(blast dest:wf_rank_tranclD)
qed

end
(*>*)