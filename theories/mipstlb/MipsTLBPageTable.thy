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
theory MipsTLBPageTable
  imports Main Set MipsTLB
begin
(*>*)  

(* ========================================================================= *)  
section "MIPS Page Table"
(* ========================================================================= *)
    
text "The PageTable is a function from a VPN to an EntryLo. The page table 
      has an associated ASID i.e. the page table is tied to a particular
      process with this ASID. Global entries are assumed to be present in
      all page tables."
  
record MIPSPT = 
  entry :: "ASID \<Rightarrow> VPN \<Rightarrow> TLBENTRYLO"
  
  
    
(* ------------------------------------------------------------------------- *)   
subsection "Wellformed MIPSPT entries"  
(* ------------------------------------------------------------------------- *)   
  
text "The MIPSPT entries are wellformed if their TLBENTRYLO is well formed. Thus 
      we say that the all entries of the TLB are wellformed if all corresponding
      TLBENTRYLO are wellformed too."
  
definition MIPSPT_Entries_wellformed :: "MIPSPT \<Rightarrow> bool"
  where "MIPSPT_Entries_wellformed pt =
           (\<forall>vpn as. TLBENTRYLOWellFormed ((entry pt) as vpn) MASK4K)"
   

text "Consequently, the MIPSPT is valid if all its entries are well formed and 
      the ASID is within the valid range as defined by the MIPS TLB."
  
definition MIPSPT_valid :: "MIPSPT \<Rightarrow> bool"
  where "MIPSPT_valid pt =  (MIPSPT_Entries_wellformed pt)"


text "We now proof that if the MIPS PageTable is valid, then forall possible
      VPN, the corresponding entry is well formed."
  
lemma MIPSPT_valid_wellformed:
  "\<And>pt vpn as. MIPSPT_valid pt  \<Longrightarrow> TLBENTRYLOWellFormed ((entry pt) as vpn) MASK4K"
  by(simp add:MIPSPT_valid_def MIPSPT_Entries_wellformed_def)
  
    
    
(* ========================================================================= *)  
section "Page Table operations"
(* ========================================================================= *)   

text "In this section we define the initialization, read and write operations
      on the page table."
  
  
(* ------------------------------------------------------------------------- *)   
subsection "Initialization"  
(* ------------------------------------------------------------------------- *)   

text "The page table is initialized by zeroing out all entries. "
  
definition MIPSPT_create :: "MIPSPT"
  where "MIPSPT_create = \<lparr> entry = (\<lambda>_. \<lambda>_. null_entry_lo) \<rparr>"


text "The newly initialized page table has all entries as null EntryLo"
  
lemma MIPSPT_create_all_null:
  "\<forall>vpn as. (entry (MIPSPT_create)) as vpn = null_entry_lo"
  by(auto simp:MIPSPT_create_def)      
    
    
text "If the ASID used to create the MIPSPT was valid, then the newly
      created MIPSPT is valid"

lemma "\<And>as. MIPSPT_valid (MIPSPT_create)"    
  by(simp add:MIPSPT_valid_def MIPSPT_Entries_wellformed_def 
              MIPSPT_create_all_null NullEntryLoWellFormed MIPSPT_create_def)
  
  

(* ------------------------------------------------------------------------- *)   
subsection "Read Page Table Entry"  
(* ------------------------------------------------------------------------- *)     

text "Reads the entry with a particular VPN from the page table."
  
definition MIPSPT_read :: "ASID \<Rightarrow> VPN \<Rightarrow> MIPSPT \<Rightarrow> TLBENTRYLO"
  where "MIPSPT_read as vpn pt = (entry pt) as  vpn"

    
text "The page table reads the null entry for all entries of a newly created
      page table."
  
lemma "\<forall>vpn as. MIPSPT_read as vpn (MIPSPT_create) = null_entry_lo"
  by(auto simp:MIPSPT_read_def MIPSPT_create_def)
    
    
(* ------------------------------------------------------------------------- *)   
subsection "Write Page Table Entry"  
(* ------------------------------------------------------------------------- *)    

text "Writes an entry at index of the VPN  in the MIPS Page Table"  
  
definition MIPSPT_write :: "ASID \<Rightarrow> VPN \<Rightarrow> TLBENTRYLO \<Rightarrow> MIPSPT \<Rightarrow> MIPSPT"
  where "MIPSPT_write as vpn e pt =  
    \<lparr> entry = (entry pt)(as := ((entry pt) as)(vpn := e)) \<rparr>"
    
    
text "An entry can be cleared, by writing it with the null EntryLo. Likewise
      we can clear all entries of a page table."
    
definition MIPSPT_clear :: "ASID \<Rightarrow> VPN \<Rightarrow> MIPSPT \<Rightarrow> MIPSPT"
  where "MIPSPT_clear as vpn pt = (MIPSPT_write as vpn null_entry_lo pt)"
    
definition MIPSPT_clearall :: "MIPSPT \<Rightarrow> MIPSPT"
  where "MIPSPT_clearall pt = pt \<lparr> entry := (\<lambda>_. \<lambda>_ . null_entry_lo) \<rparr> "
    

text "An entry that is written to, is read back after wards"

lemma "\<And>vpn e as. MIPSPT_read as vpn (MIPSPT_write as vpn e pt) = e"
  by(auto simp:MIPSPT_read_def MIPSPT_write_def)

    
text "An entry that is cleared reads as null entry"    

lemma "\<And>vpn as. MIPSPT_read as vpn (MIPSPT_clear as vpn pt) = null_entry_lo"
  by(auto simp:MIPSPT_read_def MIPSPT_clear_def MIPSPT_write_def)

    
text "clearing a page tabel is equvalent to crate a new page table with the 
      same ASID."

lemma "\<And>pt. MIPSPT_clearall pt = MIPSPT_create"
  by(auto simp:MIPSPT_create_def MIPSPT_clearall_def) 
    
    
text "If the MIPSPT was valid, then clearing an entry will result in a valid
      MISPT again."
  
lemma "\<And>pt as vpn. MIPSPT_valid pt \<Longrightarrow> MIPSPT_valid (MIPSPT_clear as vpn pt)"        
  by(auto simp:MIPSPT_clear_def MIPSPT_write_def MIPSPT_valid_def 
               MIPSPT_Entries_wellformed_def NullEntryLoWellFormed)

             
text "If the MIPSPT was valid, then clearing all entry will result in a valid
      MISPT again."
  
lemma "\<And>pt. MIPSPT_valid pt \<Longrightarrow> MIPSPT_valid (MIPSPT_clearall pt)"    
  by(auto simp:MIPSPT_clearall_def MIPSPT_valid_def MIPSPT_Entries_wellformed_def
               NullEntryLoWellFormed)
  
             
text "If the MIPSPT was valid and the new entry is well formed, then the
      resulting MIPSPT will be valid too."
  
lemma "\<And>pt as. MIPSPT_valid pt \<Longrightarrow> (TLBENTRYLOWellFormed e MASK4K)
             \<Longrightarrow> MIPSPT_valid (MIPSPT_write as  vpn e pt)"    
  by(auto simp: MIPSPT_write_def MIPSPT_valid_def MIPSPT_Entries_wellformed_def)
    
    
             
(* ========================================================================= *)  
section "VPN to PFN translation"
(* ========================================================================= *)  

  
text "The translate function converts a VPN into a set of PFN it translates to.
      If the entry is marked as not-valid then there is no translation."  
  
definition MIPSPT_translate :: "MIPSPT \<Rightarrow> ASID \<Rightarrow> VPN \<Rightarrow> PFN set"  
  where "MIPSPT_translate pt as vpn = (if (v (MIPSPT_read as vpn pt)) then
                                       {(pfn (MIPSPT_read as vpn pt))} 
                                    else {})"  
    
    
text "The translate function will always return an empty or a singleton
      set of a particular VPN. In particular, if the entry is valid, then
      the singleton set is returned, otherwise the empty set."    

lemma "MIPSPT_translate (MIPSPT_write as vpn e pt) as vpn \<subseteq> {(pfn e)}"
  by(auto simp add: MIPSPT_translate_def MIPSPT_write_def MIPSPT_read_def)
  
lemma "\<And>e. (v e) \<Longrightarrow> MIPSPT_translate (MIPSPT_write as vpn e pt) as vpn = {(pfn e)}"
  by(auto simp add: MIPSPT_translate_def MIPSPT_write_def MIPSPT_read_def)

lemma "\<And>e. \<not>(v e) \<Longrightarrow> MIPSPT_translate (MIPSPT_write as vpn e pt) as vpn = {}"
  by(auto simp add: MIPSPT_translate_def MIPSPT_write_def MIPSPT_read_def)    
    
    
text "The translate function of a newly created or cleared page table is empty
      for all VPN."
  
lemma "\<forall>vpn as. MIPSPT_translate (MIPSPT_create) as vpn = {}"
  by(auto simp:MIPSPT_create_def MIPSPT_translate_def
               MIPSPT_read_def null_entry_lo_def)      

lemma "\<forall>vpn as. MIPSPT_translate (MIPSPT_clearall pt) as vpn = {}"
  by(auto simp:MIPSPT_clearall_def MIPSPT_translate_def
               MIPSPT_read_def null_entry_lo_def)      
    
             
text "The translate function of a cleared entry will be empty:"             
  
lemma "\<forall>vpn as. MIPSPT_translate (MIPSPT_clear as vpn pt) as vpn = {}"
  by(auto simp: MIPSPT_translate_def MIPSPT_clear_def MIPSPT_write_def 
                MIPSPT_read_def null_entry_lo_def)



(* ========================================================================= *)  
section "Creating of a TLB Entry"
(* ========================================================================= *)             

text "From a MIPS PageTable we can create a MIPS TLB entry by converting the 
      PageTable entries. To ensure that created MIPS TLB entries form the MIPSPT 
      are well formed, we define the maximum number of entries to be the number 
      of 4k pages the MIPS TLB supports to span its 1TB=256M x 4k address space.
      This is needed as the MIPS TLB defines the range of valid VPN2"
  

definition MIPSPT_EntriesMax :: nat
  where "MIPSPT_EntriesMax = 268435456"
  

text "The maximum number of entries defined above spans the 1TB VAS of the
      MIPS TLB and hence is equal to the number of 4k pages."    
  
lemma "MIPSPT_EntriesMax * 4096 = GB 1024"
  by(auto simp:MIPSPT_EntriesMax_def GB_def)
    
lemma "MIPSPT_EntriesMax = page_count MASK4K"
  by(auto simp:MIPSPT_EntriesMax_def page_count_def MB_def)  
  
  
text "For a particular VPN we can create the MIPSTLB entry pair as follows.
      We need to account for the fact that the MIPS TLB has pairs of EntryLO
      and therefore the VPN needs to be even."
  
definition MIPSPT_mk_tlbentry :: "MIPSPT \<Rightarrow> ASID \<Rightarrow> VPN \<Rightarrow> TLBENTRY"
  where "MIPSPT_mk_tlbentry pt as vpn = 
        (if (even vpn) then
            TLBENTRY.make MASK4K \<lparr> vpn2=vpn, asid=as \<rparr> 
                          ((entry pt) as vpn) ((entry pt) as (vpn + 1)) 
           else  
            TLBENTRY.make MASK4K \<lparr> vpn2=(vpn-1), asid=as \<rparr> 
                          ((entry pt) as (vpn - 1)) ((entry pt) as vpn))"
   
    
text "We proof that the created TLBEntry will always have an even VPN."    
  
lemma "\<forall>vpn. (even (vpn2 (hi (MIPSPT_mk_tlbentry pt as vpn))))"
  by(auto simp:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)


text "The asid of the created MIPS TLB Entry is always the one from the 
      MIPS PageTable."    
  
lemma MIPSPT_asid_is :
   "\<forall>vpn as. (TLBENTRYHI.asid (hi (MIPSPT_mk_tlbentry pt as vpn))) = as"
  by(auto simp:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)

    
text "Likewise, the ASID match function will always evaluate to true for a
     Entry which is crated from the very same page table."    
    
lemma MIPSPT_TLBENTRY_asidmatch:
  "\<forall>forall. EntryASIDMatchA as  (MIPSPT_mk_tlbentry (pte mpt) as vpn)"
  by(auto simp:EntryASIDMatchA_def MIPSPT_mk_tlbentry_def TLBENTRY.make_def)

    
text "The EntryHi part of the created entry is always well formed. 
      We first define two helper lemmas that shows the bounds on the VPN. "
  
lemma VPNEvenBounds: 
  assumes limit: "vpn < (Suc (Suc a))"
      and even: " even vpn"
      and aeven : "even a"
    shows  "vpn \<le> a"
  proof -
    from limit have X0:
      "vpn \<le> Suc a"
      by(auto)
    also from even aeven have X2:
      "vpn \<noteq> Suc a"
      by(auto)
    also from even X0 X2 have X1:
      "vpn < (Suc a)"
      by(auto)
    with X1 show ?thesis by(auto)
  qed    
  
    
lemma VPNWithinValidBounds: 
  assumes bound: "vpn < MIPSPT_EntriesMax"
       and even: "even vpn "
       shows "(Suc vpn) < MIPSPT_EntriesMax"
proof -
  have aeven: "even MIPSPT_EntriesMax" by(simp add:MIPSPT_EntriesMax_def)
  with bound even aeven have X0: "vpn \<le> MIPSPT_EntriesMax - 2"
    by(simp add:VPNEvenBounds)

  from X0 have X1: "(Suc vpn) \<le> (MIPSPT_EntriesMax - 1)" 
    by(auto simp:MIPSPT_EntriesMax_def)
  with X1 show ?thesis by(auto)
qed    


text "We show that all the created TLBEntries have a valid Hi part."    

lemma MIPSPT_ENTRYHIWellformed:
  "\<And>vpn as pt. MIPSPT_valid pt \<Longrightarrow> vpn < MIPSPT_EntriesMax \<Longrightarrow> ASIDValid as \<Longrightarrow>
             TLBENTRYHIWellFormed (hi (MIPSPT_mk_tlbentry pt as vpn)) MASK4K"
  by(auto simp:MIPSPT_mk_tlbentry_def TLBENTRYHIWellFormed_def TLBENTRY.make_def 
               MIPSPT_valid_def VPN2Valid_def VPNMin_def VPN2Max_def MB_def 
               MIPSPT_EntriesMax_def VPNEvenBounds)

             
text "Currently  all the entries have a page size of 4k"             
  
lemma MIPSPT_EntryMask_is:
  "\<And>vpn as pt. (mask (MIPSPT_mk_tlbentry pt as vpn)) = MASK4K"
  by(auto simp:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)
             

text "Next we show that if the MIPS PageTable was in a valid state, then the 
      created entry is always well formed with respect to the MIPS TLB 
      specifications."
     
lemma MIPSPT_TLBENTRYWellFormed:
   "\<And>pt vpn. MIPSPT_valid pt \<Longrightarrow> vpn < MIPSPT_EntriesMax \<Longrightarrow> ASIDValid as \<Longrightarrow>
              TLBENTRYWellFormed ( MIPSPT_mk_tlbentry pt as vpn)"
  apply(simp add:TLBENTRYWellFormed_def)
  apply(simp add:MIPSPT_ENTRYHIWellformed MIPSPT_EntryMask_is)
  apply(simp add:MIPSPT_valid_def MIPSPT_Entries_wellformed_def)
  apply(simp add:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)
  done
    
end