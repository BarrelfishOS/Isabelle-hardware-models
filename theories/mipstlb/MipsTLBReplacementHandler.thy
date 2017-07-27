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
  
text "The MIPS TLB exception handler replaces an entry of the TLB with 
      the contents of the page table. We provide two different implementations"  
                                   
(* ------------------------------------------------------------------------- *)   
subsection "Deterministic Exception Handler"  
(* ------------------------------------------------------------------------- *)    

text "We can formulate a deterministic replacement policy where we always
      replace the entry based on its VPN2 modulo the TLB capacity."

definition MIPSTLBIndex :: "TLBENTRY \<Rightarrow> nat"
  where "MIPSTLBIndex e = ((vpn2 (hi (e))) mod TLBCapacity)"

    
text "The calculated index is always in the valid range."

lemma MIPSTLBIndex_in_range:
  "\<forall>e. MIPSTLBIndex e <  TLBCapacity"
  by(auto simp:MIPSTLBIndex_def TLBCapacity_def)
    
    
text "If the indexes are different this implies that the two entries are not
     the same."
  
lemma "\<And>e f. MIPSTLBIndex e \<noteq> MIPSTLBIndex f \<Longrightarrow> ((vpn2 (hi e)) \<noteq> (vpn2 (hi f)))"
  by(auto simp add:MIPSTLBIndex_def TLBCapacity_def)

lemma "\<And>e f. MIPSTLBIndex e \<noteq> MIPSTLBIndex f \<Longrightarrow> e \<noteq> f"
  by(auto simp add:MIPSTLBIndex_def TLBCapacity_def)
    
    
text "We define the deterministic exception handler as follows."
    
definition MipsTLBPT_handle_exn_det :: "MipsTLBPT \<Rightarrow> nat \<Rightarrow> MipsTLBPT"
  where "MipsTLBPT_handle_exn_det mpt vpn = 
         \<lparr>tlb = (\<lparr> wired = (wired (tlb mpt)), 
                  entries = (entries (tlb mpt))(
                    (MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) )
                       :=  MIPSPT_mk_tlbentry (pte mpt) vpn) \<rparr> ), 
         pte = (pte mpt)\<rparr>"


text "we show that the definition produces the same result as when using the 
      tlbwi function, and therefore we can use the simpler, direct
      equivalent."
  
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

    
    
(* ========================================================================= *)  
section "Valid TLB+PageTables"
(* ========================================================================= *) 

  
text "We say that the combination is valid, if both the TLB and the page table
     are valid. In addition, the TLB is an instance of the page table if there
     is a corresponding entry in the page table for all entries in the TLB with
     a matching ASID. In addition, the deterministic replacement handler
     ensures a particular location for the entry."  
  
    
definition MipsTLBPT_is_instance :: "MipsTLBPT \<Rightarrow> bool"
  where "MipsTLBPT_is_instance mt = (\<forall>i<TLBCapacity. 
      ((EntryASIDMatchA (asid (pte mt)) ((entries (tlb mt)) i)) ) \<longleftrightarrow>
       (((entries (tlb mt) i) = 
            MIPSPT_mk_tlbentry (pte mt) (vpn2(hi(entries (tlb mt) i)))) \<and> 
       (i = MIPSTLBIndex (entries (tlb mt) i))))"    
        

text "If the TLB is an instance of the page table then forall entries if
      the ASID matches with the the ASID of the page table, then the 
      TLB entry must be the same as if its created from the page table."  
  
lemma  "MipsTLBPT_is_instance mt \<Longrightarrow>i < TLBCapacity \<Longrightarrow>
      (EntryASIDMatchA (asid (pte mt)) ((entries (tlb mt)) i)) \<Longrightarrow> 
      (entries (tlb mt) i) = MIPSPT_mk_tlbentry (pte mt) (vpn2(hi(entries (tlb mt) i)))"
  by(simp add:MipsTLBPT_is_instance_def)

    
text "If the index function of an entry in the page table is not the same as its
      actual index, then there must not be a match on the ASID."
  
lemma  "MipsTLBPT_is_instance mt \<Longrightarrow>i < TLBCapacity \<Longrightarrow> i \<noteq> MIPSTLBIndex (entries (tlb mt) i)
  \<Longrightarrow> \<not> (EntryASIDMatchA (asid (pte mt)) ((entries (tlb mt)) i))"
  by(simp add:MipsTLBPT_is_instance_def )  
 
  
text "We therefore can define the validity of a MIPS TLB + PageTable combination
      as the page tables and the TLB are valid and the TLB is an instance of
      the page tables."
  
definition MipsTLBPT_valid :: "MipsTLBPT \<Rightarrow> bool"
  where "MipsTLBPT_valid mt = ((MIPSPT_valid (pte mt)) \<and> (TLBValid (tlb mt)) 
                              \<and> (MipsTLBPT_is_instance mt) )"

    
text "If the MIPS TLB and PageTables are valid then for all VPNs the translate
      set of the TLB must be a subset of equal to the translate set of the 
      PageTable."
  
(* TODO *)  
  
lemma "\<forall>vpn. MipsTLBPT_valid mt \<Longrightarrow> MIPSTLB_translate (tlb mpt) vpn  (asid (pte mpt))
                 \<subseteq>  MIPSPT_translate (pte mpt) vpn"
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
          MIPSTLB_translate (tlb (MipsTLBPT_fault mtlb vpn)) vpn (asid (pte mtlb)) "



  
(* ========================================================================= *)  
section "Proofs"
(* ========================================================================= *)    

text "Next we proof that if the state of the MIPSTLB and page tables is valid
      then handling an exception will always results in a valid state again."  

lemma MipsTLBT_keeps_instance: 
  "\<And>vpn mpt. MipsTLBPT_valid mpt \<Longrightarrow> vpn < MIPSPT_EntriesMax 
           \<Longrightarrow> MipsTLBPT_is_instance(MipsTLBPT_handle_exn_det mpt vpn)"       
  apply(simp add:MipsTLBPT_valid_def)
  apply(simp add:MipsTLBPT_is_instance_def)
  apply(simp add:MipsTLBPT_handle_exn_det_def MIPSTLBIndex_in_range 
                 MIPSPT_TLBENTRY_asidmatch)
  apply(simp add:MIPSTLBIndex_def TLBCapacity_def)
  apply(simp add:MIPSPT_mk_tlbentry_def)
  apply(simp add:TLBENTRY.make_def)
  done     

lemma MipsTLBPT_not_match :
assumes valid: "MipsTLBPT_valid mpt"    
    and inrange: "\<And>vpn. vpn < MIPSPT_EntriesMax"
    and inoteq : "\<And>i vpn. i \<noteq>  MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn)"
    and ibound: "\<And>i. i < TLBCapacity" 
  shows "\<And>i vpn.  EntryMatch (MIPSPT_mk_tlbentry (pte mpt) vpn) (entries (tlb mpt) i) \<Longrightarrow> False"
proof -
  from valid have inst: "MipsTLBPT_is_instance mpt"
    by(simp add:MipsTLBPT_valid_def)
  
  from  inoteq ibound inrange inst have nomatch:
    "\<And>i.  EntryASIDMatch (MIPSPT_mk_tlbentry (pte mpt) vpn) (entries (tlb mpt) i) = False"
    by(auto simp add:EntryASIDMatch_def MipsTLBPT_is_instance_def MIPSPT_asid_is 
                     MIPSPT_mk_tlbentry_def TLBENTRY.make_def)
  
  from  inoteq ibound inrange inst nomatch 
    show "\<And>i vpn.  EntryMatch (MIPSPT_mk_tlbentry (pte mpt) vpn) (entries (tlb mpt) i) \<Longrightarrow> False"
    by(auto simp:EntryASIDMatch_def)
qed
    



  
lemma MipsTLBT_keeps_TLBValid :
  assumes valid: "MipsTLBPT_valid mpt "
    and inrange: "\<And>vpn. vpn < MIPSPT_EntriesMax"
      shows "\<And>vpn. TLBValid(tlb (MipsTLBPT_handle_exn_det mpt vpn))"       
proof -
  from valid have X0: "TLBValid (tlb mpt)" 
    by(auto simp add:MipsTLBPT_valid_def)
  
  from X0 have alleven: "\<forall>i < TLBCapacity. even (vpn2 (hi (entries (tlb mpt) i)))"
    by(simp add:TLBValid_def TLBEntryWellFormed_def TLBENTRYWellFormed_def TLBENTRYHIWellFormed_def 
                VPN2Valid_def)
      
  also have X1: "\<And>vpn. (wired (tlb (MipsTLBPT_handle_exn_det mpt vpn))) =  (wired (tlb mpt)) "
    by(simp add:MipsTLBPT_handle_exn_det_def)

  from valid have X2: "MipsTLBPT_is_instance mpt"
    by(auto simp:MipsTLBPT_valid_def)
      
  from valid have X3: " MIPSPT_valid (pte mpt)" 
    by(auto simp:MipsTLBPT_valid_def)
  
  from inrange X3 have X5: 
      "\<And>vpn. TLBENTRYWellFormed ( MIPSPT_mk_tlbentry (pte mpt) vpn) "      
      by(simp add:MIPSPT_TLBENTRYWellFormed)
      
  from inrange X3 X0 X5 have X4: "\<And>vpn. \<forall>i<TLBCapacity.
        TLBEntryWellFormed (tlb (MipsTLBPT_handle_exn_det mpt vpn)) i"
  proof -
    
    have A0:  "\<And>vpn. (\<forall>i<TLBCapacity. TLBEntryWellFormed (tlb (MipsTLBPT_handle_exn_det mpt vpn)) i) =
          (\<forall>i<TLBCapacity. (i = (MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn))
                                 \<longrightarrow> TLBEntryWellFormed (tlb (MipsTLBPT_handle_exn_det mpt vpn)) i) \<and>
                           (i \<noteq> (MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn))
                                 \<longrightarrow> TLBEntryWellFormed (tlb (MipsTLBPT_handle_exn_det mpt vpn)) i))"
      by(auto)
    
        
    have A1:  "... = ( \<lambda>vpn. \<forall>i<TLBCapacity.
        (i = MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<longrightarrow> TLBENTRYWellFormed (MIPSPT_mk_tlbentry (pte mpt) vpn)) \<and>
        (i \<noteq> MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<longrightarrow> TLBENTRYWellFormed (entries (tlb mpt) i)))"
      
      by(simp add:MipsTLBPT_handle_exn_det_def TLBEntryWellFormed_def)
    
    with inrange A1 A0 X0 X3 show "\<And>vpn. \<forall>i<TLBCapacity.
        TLBEntryWellFormed (tlb (MipsTLBPT_handle_exn_det mpt vpn)) i"
      by(auto simp:MIPSPT_TLBENTRYWellFormed TLBValid_def TLBEntryWellFormed_def MIPSTLBIndex_in_range)
  qed
      
  from X0 X1 X4 have X6: "\<And>vpn. TLBValid (tlb (MipsTLBPT_handle_exn_det mpt vpn)) =  (\<forall>i<TLBCapacity.
        TLBEntryConflictSet (entries (tlb (MipsTLBPT_handle_exn_det mpt vpn)) i) (tlb (MipsTLBPT_handle_exn_det mpt vpn)) \<subseteq> {i})"
    by(simp add:TLBValid_def)
  
 
  from inrange X2 have X7: "... =  (\<lambda>vpn. \<forall>i<TLBCapacity. {ia. ia < TLBCapacity \<and> EntryMatch (entries (tlb (MipsTLBPT_handle_exn_det mpt vpn)) ia) (entries (tlb (MipsTLBPT_handle_exn_det mpt vpn)) i)} \<subseteq> {i})"
    by(simp add:TLBEntryConflictSet_def)
      
  from inrange X2 have X8: "... = (\<lambda>vpn. \<forall>i. (i = MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<longrightarrow>
          {ia. ia \<noteq> MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<longrightarrow> ia < TLBCapacity \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) vpn) (entries (tlb mpt) ia)}
          \<subseteq> {MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn)}) \<and>
         (i \<noteq> MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<longrightarrow>
          i < TLBCapacity \<longrightarrow>
          {ia. (ia = MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<longrightarrow> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) vpn) (entries (tlb mpt) i)) \<and>
               (ia \<noteq> MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<longrightarrow> ia < TLBCapacity \<and> EntryMatch (entries (tlb mpt) i) (entries (tlb mpt) ia))}
          \<subseteq> {i}))"      
    by(simp add:MipsTLBPT_handle_exn_det_def MIPSTLBIndex_in_range EntryMatch_true EntryMatch_commute)
            
  from inrange valid  have X10: "... =  (\<lambda>vpn. \<forall>i. (i = MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<longrightarrow>
          {ia. ia \<noteq> MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<longrightarrow> ia < TLBCapacity \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) vpn) (entries (tlb mpt) ia)}
          \<subseteq> {MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn)}) \<and>
         (i \<noteq> MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<longrightarrow>
          i < TLBCapacity \<longrightarrow>
          {ia. ia \<noteq> MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<and>
                ia < TLBCapacity \<and> EntryMatch (entries (tlb mpt) i) (entries (tlb mpt) ia)}
          \<subseteq> {i}))"
    by(auto simp add:MipsTLBPT_not_match)
  
    from inrange valid X0 have X11:  "... =  (\<lambda>vpn. \<forall>i. (i = MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<longrightarrow>
          {ia. ia \<noteq> MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn)
      \<longrightarrow> ia < TLBCapacity \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) vpn) (entries (tlb mpt) ia)}
          \<subseteq> {MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn)}))"
      by(auto simp add:TLBValid_def TLBEntryConflictSet_def)
    
    have X12: "... = (\<lambda>vpn. {ia. ia \<noteq> MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn)
      \<longrightarrow> ia < TLBCapacity \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) vpn) (entries (tlb mpt) ia)}
          \<subseteq> {MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn)})"
      by(auto)
        
    
    have X13: "... = (\<lambda>vpn. 
          { MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) } \<union> 
          {ia. ia < TLBCapacity \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) vpn) (entries (tlb mpt) ia)}
          \<subseteq> {MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn)})"
      by(auto)
        
    have X14: "... =  (\<lambda>vpn. 
          { MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) } \<union>
           {ia. ia < TLBCapacity \<and>  ia \<noteq>  MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) vpn) (entries (tlb mpt) ia)} \<union>
           {ia. ia < TLBCapacity \<and> ia =  MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) vpn) (entries (tlb mpt) ia)}
          \<subseteq> {MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn)})"
     by(auto)
   
   have X15: "... =  (\<lambda>vpn. 
     {ia. ia < TLBCapacity \<and> ia \<noteq> MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) vpn) (entries (tlb mpt) ia)} \<union>
     {ia. ia < TLBCapacity \<and> ia = MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) vpn) (entries (tlb mpt) ia)}
     \<subseteq> {MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn)})"
     by(simp)
   
   from valid inrange have X16: "... = ( \<lambda>vpn. 
      {ia. ia < TLBCapacity \<and> ia = MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn) \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) vpn) (entries (tlb mpt) ia)}
     \<subseteq> {MIPSTLBIndex (MIPSPT_mk_tlbentry (pte mpt) vpn)})"
     by(auto simp add:MipsTLBPT_not_match )
   
   with valid inrange alleven X0 X1 X2 X3 X4 X5 X6 X7 X8 X10 X11 X12 X13 X14 X15 X16
    show "\<And>vpn. TLBValid(tlb (MipsTLBPT_handle_exn_det mpt vpn))"
      by(auto)
  
qed
  
  

lemma MipsTLBT_keeps_ptvalid: "\<And>vpn mpt. MipsTLBPT_valid mpt \<Longrightarrow> vpn < MIPSPT_EntriesMax 
           \<Longrightarrow>  MIPSPT_valid (pte (MipsTLBPT_handle_exn_det mpt vpn))"       
  by(simp add:MipsTLBPT_valid_def MipsTLBPT_handle_exn_det_def)
  
    
    
lemma 
    assumes valid: "MipsTLBPT_valid mpt "
    and inrange: "\<And>vpn. vpn < MIPSPT_EntriesMax"
shows  "\<And>vpn.  MipsTLBPT_valid(MipsTLBPT_handle_exn_det mpt vpn)"
  apply(subst MipsTLBPT_valid_def)
  apply(simp add:MipsTLBT_keeps_ptvalid valid inrange)
  apply(simp add:MipsTLBT_keeps_instance valid inrange)
  apply(simp add:MipsTLBT_keeps_TLBValid valid inrange)
  done


    
end 