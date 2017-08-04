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

text "This is the NON-deterministic version of the MIPS TLB + Replacement handler"

  
(* ========================================================================= *)  
section "MIPS TLB + MIPS PageTables"
(* ========================================================================= *)    
  
text "We now define the combination of a MIPS TLB and a MIPS PageTable. Note
      that the MIPSPT stores the ASID."
  
record MipsTLBPT = 
  tlb :: MIPSTLB
  pte :: MIPSPT

    
  
(* ========================================================================= *)  
section "Non-deterministic Exception Handler"
(* ========================================================================= *)
  
text "The MIPS TLB exception handler replaces an entry of the TLB with 
      the contents of the page table."  
            
  
definition MipsTLBPT_update_tlb :: "MipsTLBPT \<Rightarrow> ASID \<Rightarrow> VPN \<Rightarrow> MipsTLBPT set"
  where "MipsTLBPT_update_tlb mpt as vpn = 
          {\<lparr>tlb = t, pte = (pte mpt)\<rparr> | 
            t. t\<in> tlbwr (MIPSPT_mk_tlbentry (pte mpt) as vpn) (tlb mpt)}"

    
(* ========================================================================= *)  
section "Valid TLB+PageTables"
(* ========================================================================= *) 

  
text "We say that the combination is valid, if both the TLB and the page table
     are valid. In addition, the TLB is an instance of the page table if there
     is a corresponding entry in the page table for all entries in the TLB with
     a matching ASID. In addition, the deterministic replacement handler
     ensures a particular location for the entry."  
  
    
definition MipsTLBPT_is_instance :: "MipsTLBPT \<Rightarrow> bool"
  where "MipsTLBPT_is_instance mt = (\<forall>i <  (capacity (tlb mt)). 
        MIPSPT_read (TLBENTRYHI.asid (hi (entries (tlb mt) i))) 
                    (vpn2 (hi (entries (tlb mt) i)))
                    (pte mt)       = (lo0(entries (tlb mt) i)) \<and> 
        MIPSPT_read (TLBENTRYHI.asid (hi (entries (tlb mt) i)))
                    (vpn2 (hi (entries (tlb mt) i)) + 1) 
                    (pte mt) = (lo1(entries (tlb mt) i)))"


  
text "We therefore can define the validity of a MIPS TLB + PageTable combination
      as the page tables and the TLB are valid and the TLB is an instance of
      the page tables."
  
definition MipsTLBPT_valid :: "MipsTLBPT \<Rightarrow> bool"
  where "MipsTLBPT_valid mt = ((MIPSPT_valid (pte mt)) \<and> (TLBValid (tlb mt)) 
                              \<and> (MipsTLBPT_is_instance mt) )"   

 
(* ========================================================================= *)  
section "Fault Function"
(* ========================================================================= *)                                     

text "The fault function ensures that an entry is only updatd if there was no
      translating function"  
  
definition MipsTLBPT_fault :: "MipsTLBPT \<Rightarrow> ASID \<Rightarrow> VPN \<Rightarrow> MipsTLBPT set"
  where "MipsTLBPT_fault  mtlb as vpn = 
      (if MIPSTLB_translate (tlb mtlb) vpn as  = {} then 
          MipsTLBPT_update_tlb mtlb as vpn
      else {mtlb})"      
    


    
    

(* ========================================================================= *)  
section "Translate Function"
(* ========================================================================= *)    

text "The Translate function checks whether the VPN can be translated using the
      TLB, if not the exception handler is invoked and the tried again."  
       
  
definition MipsTLBPT_translate :: "MipsTLBPT \<Rightarrow> ASID \<Rightarrow> VPN \<Rightarrow> PFN set"
  where "MipsTLBPT_translate  mtlb as vpn = 
      \<Union>{ MIPSTLB_translate (tlb m) as vpn | m . m \<in> MipsTLBPT_fault mtlb as vpn}"

  
(* ========================================================================= *)  
section "Proofs"
(* ========================================================================= *)    

text "Next we proof that if the state of the MIPSTLB and page tables is valid
      then handling an exception will always results in a valid state again."  

lemma MipsTLBT_keeps_instance: 
  "\<And>vpn mpt as. MipsTLBPT_valid mpt \<Longrightarrow> vpn < MIPSPT_EntriesMax 
       \<Longrightarrow> \<forall>m \<in> (MipsTLBPT_fault mpt as vpn).  MipsTLBPT_is_instance m"       
  apply(simp add:MipsTLBPT_valid_def)
  apply(simp add:MipsTLBPT_is_instance_def MIPSPT_read_def)
  apply(simp add:MipsTLBPT_update_tlb_def MipsTLBPT_fault_def)
  apply(simp add:tlbwr_def RandomIndexRange_def)
  apply(simp add:MIPSPT_mk_tlbentry_def)
  apply(simp add:TLBENTRY.make_def)
  apply(auto)
  done     


lemma MipsTLBT_keeps_ptvalid:
  "\<And>vpn mpt as. MipsTLBPT_valid mpt \<Longrightarrow> vpn < MIPSPT_EntriesMax 
           \<Longrightarrow> \<forall>m \<in> MipsTLBPT_fault mpt as vpn .  MIPSPT_valid (pte m)"       
  by(simp add:MipsTLBPT_valid_def MipsTLBPT_update_tlb_def MipsTLBPT_fault_def, auto)

    
lemma MipsTLBT_keeps_TLBValid :
  assumes valid: "MipsTLBPT_valid mpt "
    and inrange: "\<And>vpn. vpn < MIPSPT_EntriesMax"
    and inrange2: "\<And>as. ASIDValid as"
      shows "\<And>vpn as.  \<forall>m \<in> MipsTLBPT_fault mpt as vpn .  TLBValid (tlb m)"
proof -
  from valid have X0: "TLBValid (tlb mpt)" 
    by(auto simp add:MipsTLBPT_valid_def)
  
  from X0 have alleven: "\<forall>i < (capacity (tlb mpt)). even (vpn2 (hi (entries (tlb mpt) i)))"
    by(simp add:TLBValid_def TLBEntryWellFormed_def TLBENTRYWellFormed_def TLBENTRYHIWellFormed_def 
                VPN2Valid_def)
  
  also have X1: "\<And>vpn as.  \<forall>m \<in> MipsTLBPT_update_tlb mpt as vpn . (wired (tlb m)) =  (wired (tlb mpt)) "
    by(simp add:MipsTLBPT_update_tlb_def tlbwr_def, auto)

  from valid have X2: "MipsTLBPT_is_instance mpt"
    by(auto simp:MipsTLBPT_valid_def)
      
  from valid have X3: " MIPSPT_valid (pte mpt)" 
    by(auto simp:MipsTLBPT_valid_def)
  
  from inrange inrange2 X3 have X5: 
      "\<And>vpn as. TLBENTRYWellFormed ( MIPSPT_mk_tlbentry (pte mpt) as vpn) "      
      by(simp add:MIPSPT_TLBENTRYWellFormed)
        
  from inrange X3 X0 X5 have X4: "\<And>vpn as. \<forall>i<(capacity (tlb mpt)).
       \<forall>m \<in> MipsTLBPT_update_tlb mpt as vpn . TLBEntryWellFormed (tlb (m)) i"
    by(simp add:MipsTLBPT_update_tlb_def, auto)
  
  from valid inrange inrange2 alleven X0 X2 X3 X4 X5 
  show "\<And>vpn as.  \<forall>m \<in> MipsTLBPT_fault mpt as vpn .  TLBValid (tlb m)"
    by(simp add:MipsTLBPT_fault_def TLBValid_def, auto)
qed
  
    
    
lemma 
    assumes valid: "\<And>mpt. MipsTLBPT_valid mpt "
    and inrange: "\<And>vpn. vpn < MIPSPT_EntriesMax"
    and inrange2: "\<And>as. ASIDValid as"
  shows "\<And>vpn mpt as.  \<forall>m \<in> MipsTLBPT_fault mpt as vpn .  MipsTLBPT_valid m"
  apply(subst MipsTLBPT_valid_def)
  apply(simp add:ball_conj_distrib)
  apply(simp add:MipsTLBT_keeps_ptvalid valid inrange inrange2 )
  apply(simp add:MipsTLBT_keeps_instance valid inrange)
  apply(simp add:MipsTLBT_keeps_TLBValid valid inrange inrange2 )
  done


end 