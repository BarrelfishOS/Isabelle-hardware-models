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
  
text "We say that the combination is valid, if both the TLB and the page table
     are valid. In addition, the TLB is an instance of the page table if there
     is a corresponding entry in the page table for all entries in the TLB with
     a matching ASID."  
  

definition MipsTLBPT_EntryMatch :: "TLBENTRY \<Rightarrow> MIPSPT \<Rightarrow> bool"
  where "MipsTLBPT_EntryMatch e pt = ((lo0 e) = (entry pt) (vpn2 (hi e)) 
                                     \<and> (lo1 e) = (entry pt) (vpn2 (hi e) + 1))"

  
definition MipsTLBPT_is_instance :: "MipsTLBPT \<Rightarrow> bool"
  where "MipsTLBPT_is_instance mt = (\<forall>i<TLBCapacity. 
      (\<not>(EntryASIDMatchA (asid (pte mt)) ((entries (tlb mt)) i)) ) 
      \<or> (MipsTLBPT_EntryMatch (entries (tlb mt) i) (pte mt)))"  
  
definition MipsTLBPT_valid :: "MipsTLBPT \<Rightarrow> bool"
  where "MipsTLBPT_valid mt = ((MIPSPT_valid (pte mt)) \<and> (TLBValid (tlb mt)) 
                              \<and> (MipsTLBPT_is_instance mt) )"

definition MipsTLBPT_valid2 :: "MipsTLBPT \<Rightarrow> bool"
  where "MipsTLBPT_valid2 mpt = (\<forall>vpn. MIPSTLB_translate (tlb mpt) vpn  (asid (pte mpt)) \<subseteq>
                                      MIPSPT_translate (pte mpt) vpn)"


    
  
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


definition MIPSTLBIndex :: "TLBENTRY \<Rightarrow> nat"
  where "MIPSTLBIndex e = ((vpn2 (hi (e))) mod TLBCapacity)"

    
definition MipsTLBPT_handle_exn_det :: "MipsTLBPT \<Rightarrow> nat \<Rightarrow> MipsTLBPT"
  where "MipsTLBPT_handle_exn_det mpt vpn = 
         \<lparr>tlb = (\<lparr> wired = (wired (tlb mpt)), 
                  entries = (entries (tlb mpt))((MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) ) :=  MIPSPT_mk_tlbentry (pte mpt) vpn) \<rparr> ), 
         pte = (pte mpt)\<rparr>"  

lemma assumes ptvalid: "\<And>mpt. MIPSPT_valid (pte mpt)"   
         and  tlbvalid: "\<And>mpt. TLBValid (tlb mpt)"
         and notin: "\<And>mpt vpn .MIPSTLB_translate (tlb mpt) vpn (asid (pte mpt)) = {}"
         and inrange: "\<And>vpn. vpn < MIPSPT_EntriesMax"
         shows "\<And>mpt vpn. TLBValid (tlb (MipsTLBPT_handle_exn_det mpt vpn))"
 oops
    
(* ========================================================================= *)  
section "Fault Function"
(* ========================================================================= *)                                     

text ""  
  
definition MipsTLBPT_fault :: "MipsTLBPT \<Rightarrow> VPN \<Rightarrow> MipsTLBPT"
  where "MipsTLBPT_fault  mtlb vpn = 
      (if MIPSTLB_translate (tlb mtlb) vpn (asid (pte mtlb)) = {} then 
          MipsTLBPT_handle_exn_det mtlb vpn
      else mtlb)"  
  



    
    

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
  
    



    
end 