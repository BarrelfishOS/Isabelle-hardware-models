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
theory MipsTLBEquivalence
  imports Main Set MipsTLB MipsTLBPageTable MipsTLBReplacementHandler MipsTLBLarge
begin
(*>*)
    
  
(* ========================================================================= *)  
section "Equivalence to Large TLB"
(* ========================================================================= *)  

text "Next we show that for all " 

    
  
lemma TLBEquivalence :
    assumes inrange: "vpn < MIPSPT_EntriesMax"
        and inrange2: "as < ASIDMax"
        and cap: "capacity (tlb mpt) > 0"
        and valid: "MipsTLBPT_valid mpt"
  shows "MipsTLBPT_translate mpt as vpn = 
         MIPSTLB_translate (MipsTLBLarge_create (pte mpt)) as vpn"
proof -
  from valid have ptvalid: "MIPSPT_valid (pte mpt)"
    by(simp add:MipsTLBPT_valid_def)
  
  from ptvalid inrange inrange2 have X0:
    " MIPSTLB_translate (MipsTLBLarge_create (pte mpt)) as vpn =  
     (if (v ((entry (pte mpt)) vpn as)) then {(pfn ((entry (pte mpt)) vpn as))} else {})"
    by(simp add:MipsTLBLarge_translate_is)
    
  from valid inrange inrange2 cap have X1:
    "MipsTLBPT_translate mpt as vpn =  (if (v ((entry (pte mpt)) vpn as)) then {(pfn ((entry  (pte mpt)) vpn as))} else {})"
    by(simp add:MipsTLBPT_translate_is)
  
  from X0 X1 show ?thesis by(auto)
qed

definition addr2vpn :: "addr \<Rightarrow> VPN"
  where "addr2vpn a = ((fst a) mod VASize) div 4096"

definition addr2asid :: "addr \<Rightarrow> ASID"
  where "addr2asid a = (fst a) div VASize"

definition pfn2addr :: "PFN \<Rightarrow> addr"
  where "pfn2addr p = (p * 4096, {})"

definition AddrValid :: "addr \<Rightarrow> bool"
  where "AddrValid a = ((fst a) < VASize * ASIDMax)"


lemma AddrValid_implies_inrange :
  "AddrValid a \<Longrightarrow> addr2vpn a < MIPSPT_EntriesMax"
  by(auto simp:addr2vpn_def AddrValid_def VASize_def ASIDMax_def MIPSPT_EntriesMax_def)

lemma AddrValid_implies_inrange2 :
  "AddrValid a \<Longrightarrow> addr2asid a < ASIDMax"
  by(auto simp:addr2asid_def AddrValid_def VASize_def ASIDMax_def MIPSPT_EntriesMax_def)


definition MipsTLBPT_to_node :: "nodeid \<Rightarrow> MipsTLBPT \<Rightarrow> node"
  where "MipsTLBPT_to_node nid mpt =  \<lparr> accept = {},
         translate = (\<lambda>a. (if AddrValid a then 
         (\<Union>x\<in> (MipsTLBPT_translate mpt (addr2asid a) (addr2vpn a)). {(nid, pfn2addr x)} )  else {} ))  \<rparr>"


definition MIPSLARGE_to_node :: "nodeid \<Rightarrow> MIPSTLB \<Rightarrow> node"
  where "MIPSLARGE_to_node nid t =  \<lparr> accept = {},
        translate = (\<lambda>a.  (if AddrValid a then 
        (\<Union>x\<in> (MIPSTLB_translate t (addr2asid a) (addr2vpn a)). {(nid, pfn2addr x)} ) else {} ))  \<rparr>"



lemma Equiv :
  assumes cap: "capacity (tlb mpt) > 0"
      and valid: "MipsTLBPT_valid mpt"
      and avalid: "AddrValid a"
    shows "(\<Union>x\<in>MipsTLBPT_translate mpt (addr2asid a) (addr2vpn a). {(nid, pfn2addr x)})  = 
           ( \<Union>x\<in>MIPSTLB_translate (MipsTLBLarge_create (pte mpt)) (addr2asid a) (addr2vpn a). {(nid, pfn2addr x)})"
proof -
  from avalid have X0: "addr2asid a < ASIDMax"
    by(auto simp:AddrValid_implies_inrange2)

  from avalid have X1 : "addr2vpn a < MIPSPT_EntriesMax"
    by(auto simp:AddrValid_implies_inrange)

  from X0 X1 cap valid show ?thesis
    by(auto simp: TLBEquivalence)
qed


lemma 
  assumes cap: "capacity (tlb mpt) > 0"
      and valid: "MipsTLBPT_valid mpt"
  shows "MipsTLBPT_to_node nid mpt = 
         MIPSLARGE_to_node nid (MipsTLBLarge_create (pte mpt))"
proof -
  have X0:  "MipsTLBPT_to_node nid mpt =  \<lparr>accept = {}, translate = \<lambda>a. if AddrValid a then \<Union>x\<in>MipsTLBPT_translate mpt (addr2asid a) (addr2vpn a). {(nid, pfn2addr x)} else {}\<rparr>"
    by(simp add:MipsTLBPT_to_node_def)

  have X1: " MIPSLARGE_to_node nid (MipsTLBLarge_create (pte mpt)) =  \<lparr>accept = {}, translate = \<lambda>a. if AddrValid a then \<Union>x\<in>MIPSTLB_translate (MipsTLBLarge_create (pte mpt)) (addr2asid a) (addr2vpn a). {(nid, pfn2addr x)} else {}\<rparr>"
    by(simp add:MIPSLARGE_to_node_def)

  from cap valid have X2: "\<And>a. (if AddrValid a then \<Union>x\<in>MipsTLBPT_translate mpt (addr2asid a) (addr2vpn a). {(nid, pfn2addr x)} else {}) = 
             (if AddrValid a then \<Union>x\<in>MIPSTLB_translate (MipsTLBLarge_create (pte mpt)) (addr2asid a) (addr2vpn a). {(nid, pfn2addr x)} else {})"
    by(auto simp:Equiv)


  from X0 cap valid have X3 :  " \<lparr>accept = {}, translate = \<lambda>a. if AddrValid a then \<Union>x\<in>MipsTLBPT_translate mpt (addr2asid a) (addr2vpn a). {(nid, pfn2addr x)} else {}\<rparr> = 
                  \<lparr>accept = {}, translate = \<lambda>a. if AddrValid a then \<Union>x\<in>MIPSTLB_translate (MipsTLBLarge_create (pte mpt)) (addr2asid a) (addr2vpn a). {(nid, pfn2addr x)} else {}\<rparr>"
    by(simp only:X2)

  from X0 X1 X2 show ?thesis by(auto)
qed




end  
