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
  where "MipsTLBPT_valid2 mpt = 
      (\<forall>vpn. MIPSTLB_translate (tlb mpt) vpn  (asid (pte mpt))
                 \<subseteq>  MIPSPT_translate (pte mpt) vpn)"


    
  
(* ========================================================================= *)  
section "Exception Handler"
(* ========================================================================= *)
  
text "The MIPS TLB exception handler replaces an entry of the TLB with 
      the contents of the page table. We provide two different implementations"  
                                   
(* ------------------------------------------------------------------------- *)   
subsection "Deterministic Exception Handler"  
(* ------------------------------------------------------------------------- *)    

text "We can formulate a deterministic replacement policy where we always
      replace the entry based on its VPN2 modulo the TLB capacity."

definition MIPSTLBIndex :: "TLBENTRY \<Rightarrow> nat"
  where "MIPSTLBIndex e = ((vpn2 (hi (e))) mod TLBCapacity)"

lemma MIPSTLBIndex_in_range:
  "\<forall>e. MIPSTLBIndex e <  TLBCapacity"
  by(auto simp:MIPSTLBIndex_def TLBCapacity_def)

    
definition MipsTLBPT_handle_exn_det :: "MipsTLBPT \<Rightarrow> nat \<Rightarrow> MipsTLBPT"
  where "MipsTLBPT_handle_exn_det mpt vpn = 
         \<lparr>tlb = (\<lparr> wired = (wired (tlb mpt)), 
                  entries = (entries (tlb mpt))(
                    (MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) )
                       :=  MIPSPT_mk_tlbentry (pte mpt) vpn) \<rparr> ), 
         pte = (pte mpt)\<rparr>"    

text "we show that the definition produces the same result as when using the 
      tlbwi function"
  
lemma "{\<lparr>tlb = t, pte = (pte mpt)\<rparr> | 
            t. t\<in> tlbwi (MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn)) 
           (MIPSPT_mk_tlbentry (pte mpt) vpn) (tlb mpt)} = {MipsTLBPT_handle_exn_det mpt vpn}"    
by(simp add:MipsTLBPT_handle_exn_det_def tlbwi_def MIPSTLBIndex_def TLBCapacity_def)

  
  
(* ------------------------------------------------------------------------- *)   
subsection "Random Exception handler"  
(* ------------------------------------------------------------------------- *) 

text "We can replace a random entry using the random write function of the "
  
definition MipsTLBPT_handle_exn_rdn :: "MipsTLBPT \<Rightarrow> nat \<Rightarrow> MipsTLBPT set"
  where "MipsTLBPT_handle_exn_rdn mpt vpn = 
          {\<lparr>tlb = t, pte = (pte mpt)\<rparr> | 
            t. t\<in> tlbwr (MIPSPT_mk_tlbentry (pte mpt) vpn) (tlb mpt)}"


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
  


lemma X1: "\<And>vpn mpt. MipsTLBPT_valid mpt \<Longrightarrow> vpn < MIPSPT_EntriesMax 
           \<Longrightarrow> MipsTLBPT_is_instance(MipsTLBPT_handle_exn_det mpt vpn)"       
  apply(simp add:MipsTLBPT_valid_def)
  apply(simp add:MipsTLBPT_is_instance_def)
  apply(simp add:MipsTLBPT_handle_exn_det_def)
  apply(simp add:MIPSTLBIndex_def TLBCapacity_def)
  apply(simp add:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)
  apply(simp add:MipsTLBPT_EntryMatch_def)
  done     

    
lemma X2 :
  assumes valid: "MipsTLBPT_valid mpt "
    and inrange: "vpn < MIPSPT_EntriesMax"
      shows "TLBValid(tlb (MipsTLBPT_handle_exn_det mpt vpn))"       
proof -
  from valid have X0: "TLBValid (tlb mpt)" 
    by(auto simp add:MipsTLBPT_valid_def)
  
  also have X1: "(wired (tlb (MipsTLBPT_handle_exn_det mpt vpn))) =  (wired (tlb mpt)) "
    by(simp add:MipsTLBPT_handle_exn_det_def)

  from valid have X3: " MIPSPT_valid (pte mpt)" 
    by(auto simp:MipsTLBPT_valid_def)
  
  from inrange X3 have X5: 
      "TLBENTRYWellFormed ( MIPSPT_mk_tlbentry (pte mpt) vpn) "      
      by(simp add:MIPSPT_TLBENTRYWellFormed)
      
  from inrange X3 X0 X5 have X4: "\<forall>i<TLBCapacity.
        TLBEntryWellFormed (tlb (MipsTLBPT_handle_exn_det mpt vpn)) i"
  proof -
    
    have A0:  "(\<forall>i<TLBCapacity. TLBEntryWellFormed (tlb (MipsTLBPT_handle_exn_det mpt vpn)) i) =
          (\<forall>i<TLBCapacity. (i = (MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn))
                                 \<longrightarrow> TLBEntryWellFormed (tlb (MipsTLBPT_handle_exn_det mpt vpn)) i) \<and>
                           (i \<noteq> (MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn))
                                 \<longrightarrow> TLBEntryWellFormed (tlb (MipsTLBPT_handle_exn_det mpt vpn)) i))"
      by(auto)
    have A1:  "... = (\<forall>i<TLBCapacity.
        (i = MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<longrightarrow> TLBENTRYWellFormed (MIPSPT_mk_tlbentry (pte mpt) vpn)) \<and>
        (i \<noteq> MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<longrightarrow> TLBENTRYWellFormed (entries (tlb mpt) i)))"
      by(simp add:MipsTLBPT_handle_exn_det_def TLBEntryWellFormed_def)
    
    with inrange A1 A0 X0 X3 show ?thesis 
      by(simp add:MIPSPT_TLBENTRYWellFormed TLBValid_def TLBEntryWellFormed_def MIPSTLBIndex_in_range)
  qed
      
  from X0 X1 X4 have X2: "TLBValid (tlb (MipsTLBPT_handle_exn_det mpt vpn)) =  (\<forall>i<TLBCapacity.
        TLBEntryConflictSet (entries (tlb (MipsTLBPT_handle_exn_det mpt vpn)) i) (tlb (MipsTLBPT_handle_exn_det mpt vpn)) \<subseteq> {i})"
    by(simp add:TLBValid_def)
  
      
  from inrange have X6: "... = X"
    apply(simp add:TLBEntryConflictSet_def EntryMatch_def)
    apply(auto)
      
  from X0 X1 X2 X3 X4 X5 X5 show ?thesis
    oops
  
qed
  
  

lemma X3: "\<And>vpn mpt. MipsTLBPT_valid mpt \<Longrightarrow> vpn < MIPSPT_EntriesMax 
           \<Longrightarrow>  MIPSPT_valid (pte (MipsTLBPT_handle_exn_det mpt vpn))"       
  by(simp add:MipsTLBPT_valid_def MipsTLBPT_handle_exn_det_def)
  

lemma "\<And>vpn mpt. MipsTLBPT_valid mpt \<Longrightarrow> vpn < MIPSPT_EntriesMax 
           \<Longrightarrow> MipsTLBPT_valid(MipsTLBPT_handle_exn_det mpt vpn)"    
  apply(subst MipsTLBPT_valid_def)
  apply(auto simp:X1 X2 X3)
  done


  
    
    

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