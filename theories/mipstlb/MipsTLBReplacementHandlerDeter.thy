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

(* ######################################################################### *) 
chapter "Deterministic Exception Handler for the MIPS R4600"
(* ######################################################################### *)

(*<*)
theory MipsTLBReplacementHandlerDeter
  imports MipsTLB MipsTLBPageTable 
begin
(*>*)

text "This model is a deterministic version of a TLB + exceptin handler for
      the MIPS R4600 TLB model. In this model, each page table entry for a
      particular VPN will always be present int the very same entry in the
      TLB, if at all. "  
  

(* ========================================================================= *)  
section "MIPS TLB + MIPS PageTables"
(* ========================================================================= *)    
  
text "We now define the combination of a MIPS TLB and a MIPS PageTable. All
      entries of the TLB will be populated based on the page table."
  
record MipsTLBPT = 
  tlb :: MIPSTLB
  pte :: MIPSPT

    
  
(* ========================================================================= *)  
section "Deterministic Exception Handler"
(* ========================================================================= *)
  
text "This MIPS TLB exception handler replaces an entry of the TLB with 
      the contents of the page table in a deterministic fashion, i.e.
      for each VPN the entry to be replaced will always be the same. For
      this we defined first a TLB index function."

  
(* ------------------------------------------------------------------------- *)   
subsection "TLB Index calculation"  
(* ------------------------------------------------------------------------- *)  
  
  
text "We define the following function that takes a TLB entry and a TLB and
      produces an natural number, i.e. the index of the entry in the TLB. For
      this we use a simple hash function from the VPN2 of the entry modulo
      the TLB capacity."

definition MIPSTLBIndex :: "MIPSTLB \<Rightarrow> TLBENTRY \<Rightarrow> nat"
  where "MIPSTLBIndex t e = ((vpn2 (hi (e))) mod (capacity t))"  

 
text "The definition above will always produce a TLB Index which is within the
      valid range of the TLB i.e. does not exceed it's capacity."

lemma MIPSTLBIndex_in_range:
  "\<forall>e.  (capacity t) > 0 \<Longrightarrow>  MIPSTLBIndex t e <  (capacity t)"
  by(auto simp:MIPSTLBIndex_def)


text "Moreover, this definition of the index calculation gives us that if the 
      calculated indexes are different this implies that the two entries are not
      the same."

  
lemma "\<And>e f. MIPSTLBIndex t e \<noteq> MIPSTLBIndex t f \<Longrightarrow> ((vpn2 (hi e)) \<noteq> (vpn2 (hi f)))"
  by(auto simp add:MIPSTLBIndex_def)

lemma "\<And>e f. MIPSTLBIndex t e \<noteq> MIPSTLBIndex t f \<Longrightarrow> e \<noteq> f"
  by(auto simp add:MIPSTLBIndex_def)    

    
(* ------------------------------------------------------------------------- *)   
subsection "Deterministic Exception Handler"  
(* ------------------------------------------------------------------------- *)    
    
    
text "We define the deterministic exception handler as follows."
    
definition MipsTLBPT_update_tlb :: "MipsTLBPT \<Rightarrow> ASID \<Rightarrow> VPN  \<Rightarrow> MipsTLBPT"
  where "MipsTLBPT_update_tlb mpt as vpn = 
         \<lparr>tlb = (\<lparr> capacity = (capacity (tlb mpt)), 
                  wired = (wired (tlb mpt)), 
                  entries = (entries (tlb mpt))(
                    (MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as  vpn) )
                       :=  MIPSPT_mk_tlbentry (pte mpt) as vpn) \<rparr> ), 
         pte = (pte mpt)\<rparr>"


text "we show that the definition produces the same result as when using the 
      tlbwi function, and therefore we can use the simpler, direct
      equivalent."
  
lemma "(capacity  (tlb mpt)) > 0  \<Longrightarrow> {\<lparr>tlb = t, pte = (pte mpt)\<rparr> | 
            t. t\<in> tlbwi (MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as  vpn)) 
           (MIPSPT_mk_tlbentry (pte mpt) as vpn) (tlb mpt)} = {MipsTLBPT_update_tlb mpt as vpn}"    
by(simp add:MipsTLBPT_update_tlb_def tlbwi_def MIPSTLBIndex_def)

lemma MipsTLBPT_det_capacity :
  "(capacity (tlb (MipsTLBPT_update_tlb mpt as vpn))) = (capacity (tlb mpt)) "
  by(simp add:MipsTLBPT_update_tlb_def)
  
    
(* ========================================================================= *)  
section "Valid TLB+PageTables"
(* ========================================================================= *) 

  
text "We say that the combination is valid, if both the TLB and the page table
     are valid. In addition, the TLB is an instance of the page table if there
     is a corresponding entry in the page table for all entries in the TLB with
     a matching ASID. In addition, the deterministic replacement handler
     ensures a particular location for the entry."  
  
    
definition MipsTLBPT_is_instance :: "MipsTLBPT \<Rightarrow> bool"
  where "MipsTLBPT_is_instance mt = (\<forall>i<(capacity (tlb mt)). 
       (((entries (tlb mt) i) = 
            MIPSPT_mk_tlbentry (pte mt) (asid (hi(entries (tlb mt) i))) (vpn2(hi(entries (tlb mt) i)))) \<and> 
       (i = MIPSTLBIndex (tlb mt) (entries (tlb mt) i))))"    
        

text "If the TLB is an instance of the page table then forall entries if
      the ASID matches with the the ASID of the page table, then the 
      TLB entry must be the same as if its created from the page table."  
  
lemma  "MipsTLBPT_is_instance mt \<Longrightarrow>i < (capacity (tlb mt)) \<Longrightarrow> 
      (entries (tlb mt) i) = MIPSPT_mk_tlbentry (pte mt)  (asid (hi(entries (tlb mt) i))) (vpn2(hi(entries (tlb mt) i)))"
  by(simp add:MipsTLBPT_is_instance_def)

 
  
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
  
lemma "\<forall>vpn. MipsTLBPT_valid mt \<Longrightarrow> MIPSTLB_translate (tlb mpt) as vpn
                 \<subseteq>  MIPSPT_translate (pte mpt) as vpn"
  oops
    


    

(* ========================================================================= *)  
section "Translate Function"
(* ========================================================================= *)    

text "The Translate function checks whether the VPN can be translated using the
      TLB, if not the exception handler is invoked and the tried again."  
       
  
definition MipsTLBPT_translate :: "MipsTLBPT \<Rightarrow> ASID \<Rightarrow> VPN \<Rightarrow> PFN set"
  where "MipsTLBPT_translate  mtlb as vpn = 
          MIPSTLB_translate (tlb (MipsTLBPT_update_tlb mtlb as vpn)) as vpn "



  
(* ========================================================================= *)  
section "Proofs"
(* ========================================================================= *)    

text "Next we proof that if the state of the MIPSTLB and page tables is valid
      then handling an exception will always results in a valid state again."  

lemma MipsTLBT_keeps_instance: 
  "\<And>vpn mpt as. MipsTLBPT_valid mpt \<Longrightarrow> vpn < MIPSPT_EntriesMax 
           \<Longrightarrow> MipsTLBPT_is_instance(MipsTLBPT_update_tlb mpt as vpn)"       
  apply(simp add:MipsTLBPT_valid_def)
  apply(simp add:MipsTLBPT_is_instance_def)
  apply(simp add:MipsTLBPT_update_tlb_def MIPSTLBIndex_in_range 
                 MIPSPT_TLBENTRY_asidmatch)
  apply(simp add:MIPSTLBIndex_def)
  apply(simp add:MIPSPT_mk_tlbentry_def)
  apply(simp add:TLBENTRY.make_def)
  done     

lemma MipsTLBPT_not_match :
assumes valid: "MipsTLBPT_valid mpt"    
    and inrange: "\<And>vpn. vpn < MIPSPT_EntriesMax"
    and inoteq : "\<And>i vpn. i \<noteq>  MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn)"
    and ibound: "\<And>i. i < (capacity (tlb mt))" 
  shows "\<And>i vpn.  EntryMatch (MIPSPT_mk_tlbentry (pte mpt) as vpn) (entries (tlb mpt) i) \<Longrightarrow> False"
proof -
  from valid have inst: "MipsTLBPT_is_instance mpt"
    by(simp add:MipsTLBPT_valid_def)
  
  from  inoteq ibound inrange inst have nomatch:
    "\<And>i.  EntryASIDMatch (MIPSPT_mk_tlbentry (pte mpt) as vpn) (entries (tlb mpt) i) = False"
    by(auto simp add:EntryASIDMatch_def MipsTLBPT_is_instance_def MIPSPT_TLBENTRY_asid_is 
                     MIPSPT_mk_tlbentry_def TLBENTRY.make_def)
  
  from  inoteq ibound inrange inst nomatch 
    show "\<And>i vpn.  EntryMatch (MIPSPT_mk_tlbentry (pte mpt) as vpn) (entries (tlb mpt) i) \<Longrightarrow> False"
    by(auto simp:EntryASIDMatch_def)
qed
    



  
lemma MipsTLBT_keeps_TLBValid :
  assumes valid: "MipsTLBPT_valid mpt "
    and inrange: "\<And>vpn. vpn < MIPSPT_EntriesMax"
    and inrange2: "\<And>as. ASIDValid as"
      shows "\<And>vpn as. TLBValid(tlb (MipsTLBPT_update_tlb mpt as vpn))"       
proof -
  from valid have X0: "TLBValid (tlb mpt)" 
    by(auto simp add:MipsTLBPT_valid_def)
  
  from X0 have alleven: "\<forall>i < (capacity (tlb mpt)). even (vpn2 (hi (entries (tlb mpt) i)))"
    by(simp add:TLBValid_def TLBEntryWellFormed_def TLBENTRYWellFormed_def TLBENTRYHIWellFormed_def 
                VPN2Valid_def)
      
  also have X1: "\<And>vpn as. (wired (tlb (MipsTLBPT_update_tlb mpt as vpn))) =  (wired (tlb mpt)) "
    by(simp add:MipsTLBPT_update_tlb_def)

  from valid have X2: "MipsTLBPT_is_instance mpt"
    by(auto simp:MipsTLBPT_valid_def)
      
  from valid have X3: " MIPSPT_valid (pte mpt)" 
    by(auto simp:MipsTLBPT_valid_def)
  
  from inrange inrange2 X3 have X5: 
      "\<And>vpn as. TLBENTRYWellFormed ( MIPSPT_mk_tlbentry (pte mpt) as vpn) "      
      by(simp add:MIPSPT_TLBENTRY_wellformed)
      
  from inrange X3 X0 X5 have X4: "\<And>vpn as. \<forall>i<(capacity (tlb mpt)).
        TLBEntryWellFormed (tlb (MipsTLBPT_update_tlb mpt as vpn)) i"
  proof -
    
    have A0:  "\<And>vpn as. (\<forall>i<(capacity (tlb mpt)).
           TLBEntryWellFormed (tlb (MipsTLBPT_update_tlb mpt as vpn)) i) =
          (\<forall>i<(capacity (tlb mpt)). 
              (i = (MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn))
                   \<longrightarrow> TLBEntryWellFormed (tlb (MipsTLBPT_update_tlb mpt as vpn)) i) \<and>
              (i \<noteq> (MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn))
                   \<longrightarrow> TLBEntryWellFormed (tlb (MipsTLBPT_update_tlb mpt as vpn)) i))"
      by(auto)
    
        
    have A1:  "... = ( \<lambda>vpn as. \<forall>i<(capacity (tlb mpt)).
        (i = MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn) 
            \<longrightarrow> TLBENTRYWellFormed (MIPSPT_mk_tlbentry (pte mpt) as vpn)) \<and>
        (i \<noteq> MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn)
            \<longrightarrow> TLBENTRYWellFormed (entries (tlb mpt) i)))"
      
      by(simp add:MipsTLBPT_update_tlb_def TLBEntryWellFormed_def)
    
    with inrange A1 A0 X0 X3 show "\<And>vpn as. \<forall>i<(capacity (tlb mpt)).
        TLBEntryWellFormed (tlb (MipsTLBPT_update_tlb mpt as vpn)) i"
      by(auto simp:MIPSPT_TLBENTRY_wellformed TLBValid_def TLBEntryWellFormed_def MIPSTLBIndex_in_range)
  qed
      
  from X0 X1 X4 have X6: 
      "\<And>vpn as. TLBValid (tlb (MipsTLBPT_update_tlb mpt as vpn)) = 
      (\<forall>i<(capacity (tlb mpt)).
          TLBEntryConflictSet (entries (tlb (MipsTLBPT_update_tlb mpt as vpn)) i)
                              (tlb (MipsTLBPT_update_tlb mpt as vpn)) \<subseteq> {i})"
    by(simp add:TLBValid_def MipsTLBPT_det_capacity)
  
  from inrange X2 have X7: "... =  (\<lambda>vpn as. \<forall>i<(capacity (tlb mpt)). 
        {ia. ia < (capacity (tlb mpt)) \<and> 
            EntryMatch (entries (tlb (MipsTLBPT_update_tlb mpt as vpn)) ia) 
                       (entries (tlb (MipsTLBPT_update_tlb mpt as vpn)) i)} \<subseteq> {i})"
   by(simp add:TLBEntryConflictSet_def MipsTLBPT_det_capacity)
    
      
  from inrange X2 have X8: "... = (\<lambda>vpn as. \<forall>i. (i = MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn) \<longrightarrow>
          {ia. ia \<noteq> MIPSTLBIndex  (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn) 
            \<longrightarrow> ia < (capacity (tlb mpt)) \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) as vpn) (entries (tlb mpt) ia)}
          \<subseteq> {MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as  vpn)}) \<and>
         (i \<noteq> MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt)as vpn) \<longrightarrow>
          i < (capacity (tlb mpt)) \<longrightarrow>
          {ia. (ia = MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn) 
              \<longrightarrow> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) as vpn) (entries (tlb mpt) i)) \<and>
               (ia \<noteq> MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn) 
              \<longrightarrow> ia < (capacity (tlb mpt)) \<and> EntryMatch (entries (tlb mpt) i) (entries (tlb mpt) ia))}
          \<subseteq> {i}))"      
    by(auto simp add:MipsTLBPT_update_tlb_def MIPSTLBIndex_in_range EntryMatch_true EntryMatch_commute  )
            
  from inrange valid  have X10: "... =  (\<lambda>vpn as. \<forall>i. (i = MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn)
         \<longrightarrow>  {ia. ia \<noteq> MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn) 
              \<longrightarrow> ia < (capacity (tlb mpt)) \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) as vpn) (entries (tlb mpt) ia)}
          \<subseteq> {MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn)}) \<and>
         (i \<noteq> MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn) \<longrightarrow>
          i < (capacity (tlb mpt)) \<longrightarrow>
          {ia. ia \<noteq> MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn) \<and>
                ia < (capacity (tlb mpt)) \<and> EntryMatch (entries (tlb mpt) i) (entries (tlb mpt) ia)}
          \<subseteq> {i}))"
    by(auto simp add:MipsTLBPT_not_match)
  
    from inrange valid X0 have X11:  "... =  (\<lambda>vpn as. \<forall>i. (i = MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn) \<longrightarrow>
          {ia. ia \<noteq> MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn)
      \<longrightarrow> ia < (capacity (tlb mpt)) \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) as vpn) (entries (tlb mpt) ia)}
          \<subseteq> {MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn)}))"
      by(auto simp add:TLBValid_def TLBEntryConflictSet_def)
    
    have X12: "... = (\<lambda>vpn as. {ia. ia \<noteq> MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn)
      \<longrightarrow> ia < (capacity (tlb mpt)) \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) as vpn) (entries (tlb mpt) ia)}
          \<subseteq> {MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn)})"
      by(auto)
        
    
    have X13: "... = (\<lambda>vpn as. 
          { MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn) } \<union> 
          {ia. ia < (capacity (tlb mpt)) \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) as vpn) (entries (tlb mpt) ia)}
          \<subseteq> {MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn)})"
      by(auto)
        
    have X14: "... =  (\<lambda>vpn as. 
          { MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn) } \<union>
           {ia. ia < (capacity (tlb mpt)) 
              \<and>  ia \<noteq>  MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn)
              \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) as vpn) (entries (tlb mpt) ia)} \<union>
           {ia. ia < (capacity (tlb mpt)) 
              \<and> ia =  MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn) 
              \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) as vpn) (entries (tlb mpt) ia)}
          \<subseteq> {MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn)})"
     by(auto)
   
   have X15: "... =  (\<lambda>vpn as. 
     {ia. ia < (capacity (tlb mpt)) 
        \<and> ia \<noteq> MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn) 
        \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) as vpn) (entries (tlb mpt) ia)} \<union>
     {ia. ia < (capacity (tlb mpt)) 
        \<and> ia = MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn) 
        \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) as vpn) (entries (tlb mpt) ia)}
     \<subseteq> {MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn)})"
     by(simp)
   
   from valid inrange have X16: "... = ( \<lambda>vpn as. 
      {ia. ia < (capacity (tlb mpt)) 
          \<and> ia = MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn) 
          \<and> EntryMatch (MIPSPT_mk_tlbentry (pte mpt) as vpn) (entries (tlb mpt) ia)}
     \<subseteq> {MIPSTLBIndex (tlb mpt) (MIPSPT_mk_tlbentry (pte mpt) as vpn)})"
     by(auto simp add:MipsTLBPT_not_match )
   
   with valid inrange alleven inrange2 X0 X1 X2 X3 X4 X5 X6 X7 X8 X10 X11 X12 X13 X14 X15 X16
    show "\<And>vpn as. TLBValid(tlb (MipsTLBPT_update_tlb mpt as vpn))"
      by(auto)
qed
  
  

lemma MipsTLBT_keeps_ptvalid: "\<And>vpn mpt as. MipsTLBPT_valid mpt \<Longrightarrow> vpn < MIPSPT_EntriesMax 
           \<Longrightarrow>  MIPSPT_valid (pte (MipsTLBPT_update_tlb mpt as vpn))"       
  by(simp add:MipsTLBPT_valid_def MipsTLBPT_update_tlb_def)
  
    
    
lemma 
    assumes valid: "MipsTLBPT_valid mpt "
    and inrange: "\<And>vpn. vpn < MIPSPT_EntriesMax"
    and inrange2: "\<And>as. ASIDValid as"
shows  "\<And>vpn as.  MipsTLBPT_valid(MipsTLBPT_update_tlb mpt as vpn)"
  apply(subst MipsTLBPT_valid_def)
  apply(simp add:MipsTLBT_keeps_ptvalid valid inrange)
  apply(simp add:MipsTLBT_keeps_instance valid inrange)
  apply(simp add:MipsTLBT_keeps_TLBValid valid inrange inrange2)
  done

    
(* ========================================================================= *)  
section "Equivalence to Large TLB"
(* ========================================================================= *)  

text "Next we show that for all " 

lemma "\<And>mpt vpn as. MipsTLBPT_translate mpt as vpn = MIPSTLB_translate (MipsTLBLarge_create (pte mpt)) as vpn"
  oops
    
end 