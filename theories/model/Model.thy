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
theory Model
  imports Main Set Transitive_Closure WellfoundedExtras
begin
(*>*)
  
text_raw {* \label{sec:isamodel} *}


text "First, we nail down some types.  For ease in getting started, we're using natural numbers for
  addresses and node identifiers.  It should be possible to use the same definitions to handle 
  finite-length words without much modification. Furthermore each address is accompained by a 
  set of properties e.g. whether or not the address is or supports a write. The address is then 
  a tuple of a natural number with a property set."

type_synonym nodeid = nat
type_synonym genaddr = nat

datatype property = PREAD | PWRITE
definition "ALLPROPERTIES = {PREAD, PWRITE}"

(* type_synonym property = nat *)


type_synonym addr = "genaddr \<times> property set"




text "A name is a qualified address: which is defined with respect to some context, in this
  case the node at which decoding begins."
  
type_synonym name = "nodeid \<times> addr"


text "A node can accept an input address, in which case resolution terminates here, or it can
  translate it into an input address for another node, or both.  We allow the sets of accepted
  and translated addresses to overlap to model nondeterministic behaviour e.g. a cache, which has a
  well-defined translation for every input address, but could potentially respond to any request
  with a locally-cached value.  In general, we're interested in the set of (node, address) pairs
  at which a given input address might be accepted."

record node =
  accept    :: "addr set"
  translate :: "addr \<Rightarrow> name set"



  (*<*)
text {* An empty node accepts nothing, and translates nothing. *}
definition empty_node :: node
  where
    "empty_node = \<lparr> accept = {}, translate = (\<lambda>_. {}) \<rparr>"

lemma accept_empty_node:
  "accept empty_node = {}"
  by(simp add:empty_node_def)
  (*>*)

subsection {* Address Decoding Nets. *}

text_raw {* \label{sec:nets} *}

text "A decode net is an assignment of nodes to identifiers."
  
type_synonym net = "nodeid \<Rightarrow> node"
    
text "One step of address decoding, mapping an input name (node, address) to an output name (or
  nothing)."
definition decode_step :: "net \<Rightarrow> name \<Rightarrow> name set"
  where
    "decode_step net name = translate (net (fst name)) (snd name)"

text "The decode relation is, in general, a directed graph.  If it's actually a DAG, then all
  addresses can be decoded in a well-defined manner."
definition decodes_to :: "net \<Rightarrow> name rel"
  where
    "decodes_to net = { (n', n). n' \<in> decode_step net n }"

text {* The set of names that can be accepted anywhere in this decoding net i.e. the union of
  the accept sets of all nodes. *}
definition accepted_names :: "net \<Rightarrow> name set"
  where "accepted_names net = {(nd,a). a \<in> accept (net nd)}"

(*<*)
end
(*>*)