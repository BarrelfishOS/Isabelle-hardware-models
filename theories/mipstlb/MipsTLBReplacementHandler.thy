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
theory MipsTLBReplacementHandler
  imports MipsTLB MipsTLBPageTable
begin
(*>*)


(* ========================================================================= *)  
section "MIPS TLB + MIPS PageTables"
(* ========================================================================= *)    
  
text "We now define the combination of a MIPS TLB and a MIPS PageTable. Note
      that the MIPSPT stores the ASID."
  
record MipsTLBPT = 
  tlb :: MIPSTLB
  pte :: MIPSPT

  
  
(* ========================================================================= *)  
section "Exception Handler"
(* ========================================================================= *)
  
text "The MIPS TLB exception handler randomly replaces an entry of the TLB with 
      the contents of the page table. We use the random replacement operation
      of the TLB for this purpose and return a set of MipsTLBPT."  
                                   
definition MipsTLBPT_handle_exn :: "MipsTLBPT \<Rightarrow> nat \<Rightarrow> MipsTLBPT set"
  where "MipsTLBPT_handle_exn mpt vpn = 
          {\<lparr>tlb = t, pte = (pte mpt)\<rparr> | 
            t. t\<in> tlbwr (MIPSPT_mk_tlbentry (pte mpt) vpn) (tlb mpt)}"

text "We can formulate a deterministic replacement policy where we always
      replace the entry based on its VPN2 modulo the TLB capacity."

(*
    
definition MipsTLBPT_handle_exn_det :: "MipsTLBPT \<Rightarrow> nat \<Rightarrow> MipsTLBPT set"
  where "MipsTLBPT_handle_exn_det mpt vpn = 
         { \<lparr>tlb = t, pte = (pte mpt)\<rparr> | 
            t. t\<in> tlbwi ((vpn2 (hi (MIPSPT_mk_tlbentry (pte mpt) vpn))) mod TLBCapacity) (MIPSPT_mk_tlbentry (pte mpt) vpn) (tlb mpt)}"    

lemma "\<And>mpt vpn. MipsTLBPT_handle_exn_det mpt vpn = { 
      \<lparr>tlb = (\<lparr>wired = wired (tlb mpt), entries = (entries (tlb mpt))((vpn2 (hi (MIPSPT_mk_tlbentry (pte mpt) vpn)) mod TLBCapacity) := (MIPSPT_mk_tlbentry (pte mpt) vpn))\<rparr>),
       pte = (pte mpt)\<rparr> }"
  by(simp add:MipsTLBPT_handle_exn_det_def tlbwi_def TLBCapacity_def)
  

(* ========================================================================= *)  
section "Translate Function"
(* ========================================================================= *)    

text "The Translate function checks whether the VPN can be translated using the
      TLB, if not the exception handler is invoked and the tried again."  
       
definition MipsTLBPT_translate :: "MipsTLBPT \<Rightarrow> VPN \<Rightarrow> PFN set"
  where "MipsTLBPT_translate  mtlb vpn = 
      (if MIPSTLB_translate (tlb mtlb) vpn (asid (pte mtlb)) = {} then 
           \<Union>{ MIPSTLB_translate (tlb m) vpn  (asid (pte mtlb)) | m. m\<in> (MipsTLBPT_handle_exn mtlb vpn) }
       else MIPSTLB_translate (tlb mtlb) vpn  (asid (pte mtlb)))"
  
    
definition MipsTLBPT_valid :: "MipsTLBPT \<Rightarrow> bool"
  where "MipsTLBPT_valid mpt = (\<forall>vpn. MIPSTLB_translate (tlb mpt) vpn  (asid (pte mpt)) \<subseteq>
                                      MIPSPT_translate (pte mpt) vpn)"



    
end 