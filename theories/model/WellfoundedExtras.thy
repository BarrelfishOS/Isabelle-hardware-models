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



theory WellfoundedExtras
  imports Main Wellfounded Transitive_Closure
begin

text {* The accessible part of a relation has no trivial loops. *}
lemma no_self_loops:
  assumes accp: "Wellfounded.accp R x"
  shows "\<not>R x x"
proof -
  from accp
  have "R x x \<longrightarrow> False"
  proof(rule accp.induct, intro impI)
    fix x
    assume "R x x"
       and "\<And>y. R y x \<Longrightarrow> R y y \<longrightarrow> False"
    thus False by(blast)
  qed
  thus ?thesis by(blast)
qed

lemma tranclp_rtranclp_absorb:
  "(R\<^sup>+\<^sup>+)\<^sup>*\<^sup>* = R\<^sup>*\<^sup>*"
  by(intro ext, simp add:rtranclp_rtrancl_eq tranclp_unfold)

text {* The accessible part of the transitive closure of a relation is exactly that of the
  original relation. *}
lemma accp_tranclp:
  "Wellfounded.accp R\<^sup>+\<^sup>+ = Wellfounded.accp R"
proof(rule antisym)
  show "Wellfounded.accp R \<le> Wellfounded.accp R\<^sup>+\<^sup>+"
  proof
    fix x
    assume wf: "Wellfounded.accp R x"
    have "Wellfounded.accp R x \<longrightarrow> Wellfounded.accp R\<^sup>+\<^sup>+ x"  
    proof(rule accp.induct[OF wf], intro impI)
      fix x
      assume IH1: "\<And>y. R y x \<Longrightarrow> Wellfounded.accp R y"
         and IH2: "\<And>y. R y x \<Longrightarrow> Wellfounded.accp R y \<longrightarrow> Wellfounded.accp R\<^sup>+\<^sup>+ y"
         and accpR: "Wellfounded.accp R x"
      show "Wellfounded.accp R\<^sup>+\<^sup>+ x"
      proof(rule accpI)
        fix y
        assume "R\<^sup>+\<^sup>+ y x"
        hence "tranclp (conversep R) x y" by(simp add:tranclp_converse)
        then obtain z where "(conversep R)\<^sup>*\<^sup>* z y" and "conversep R x z"
          by(blast dest:tranclpD)
        hence rest: "rtranclp R y z" and step: "R z x" by(auto dest:rtranclp_converseD)
        with IH1 IH2 have "Wellfounded.accp (tranclp R) z" by(blast)
        with rest show "Wellfounded.accp (tranclp R) y"
          by(auto intro:accp_downwards simp:tranclp_rtranclp_absorb)
      qed
    qed
    with wf show "Wellfounded.accp R\<^sup>+\<^sup>+ x" by(blast)
  qed

  from tranclp.r_into_trancl have "R \<le> R\<^sup>+\<^sup>+" by(auto)
  thus "Wellfounded.accp R\<^sup>+\<^sup>+ \<le> Wellfounded.accp R" by(rule accp_subset)
qed

text {* The accessible part of a relation contains no loops. *}
lemma no_loops:
  "Wellfounded.accp R x \<Longrightarrow> \<not>R\<^sup>+\<^sup>+ x x"
  by(rule no_self_loops[where R="R\<^sup>+\<^sup>+"], simp add:accp_tranclp)

lemmas no_loops_acc = no_loops[to_set]

lemma union_comprehension:
  "(\<Union>x\<in>{g y |y. P y}. f x) = (\<Union>{f (g y) |y. P y})"
  by(auto)

lemma compr_cong:
  assumes rw: "\<And>x. P x \<Longrightarrow> f x = g x"
  shows "{f x |x. P x} = {g x |x. P x}"
proof(intro antisym subsetI)
  fix y
  assume "y \<in> {f x |x. P x}"
  then obtain x where "P x" and "y = f x" by(auto)
  with rw show "y \<in> {g x |x. P x}" by(auto)
next
  fix y
  assume "y \<in> {g x |x. P x}"
  then obtain x where "P x" and "y = g x" by(auto)
  with rw[symmetric] show "y \<in> {f x |x. P x}" by(auto)
qed

lemma accp_image_pull:
  assumes accp: "Wellfounded.accp R x"
      and pull: "\<And>x y. S x (f y) \<Longrightarrow> \<exists>z. R z y \<and> x = f z"
    shows "Wellfounded.accp S (f x)"
  using accp
proof(induct)
  fix x
  assume accp: "Wellfounded.accp R x"
     and IH: "\<And>y. R y x \<Longrightarrow> Wellfounded.accp S (f y)"
     
  show "Wellfounded.accp S (f x)"
  proof
    fix y
    assume "S y (f x)"
    then obtain z where "R z x" "y = f z" by(blast dest:pull)
    thus "Wellfounded.accp S y" by(simp add:IH)
  qed
qed

lemma accp_image_push:
  assumes accp_f: "Wellfounded.accp S (f x)"
      and inj: "inj f"
      and homo: "\<And>x y. R x y \<Longrightarrow> S (f x) (f y)"
    shows "Wellfounded.accp R x"
proof -
  from accp_f have "f x \<in> range f \<Longrightarrow> Wellfounded.accp R (inv f (f x))"
  proof(induct)
    fix x
    assume accp_x: "Wellfounded.accp S x"
       and IH: "\<And>y. S y x \<Longrightarrow> y \<in> range f \<Longrightarrow> Wellfounded.accp R (inv f y)"
       and range: "x \<in> range f"

    show "Wellfounded.accp R (inv f x)"
    proof
      fix y
      assume "R y (inv f x)"
      hence "S (f y) (f (inv f x))" by(rule homo)
      with inj range have "S (f y) x" by(auto)
      hence "Wellfounded.accp R (inv f (f y))" by(blast intro:IH)
      with inj show "Wellfounded.accp R y" by(simp)
    qed
  qed
  with inj show ?thesis by(simp)
qed

end
