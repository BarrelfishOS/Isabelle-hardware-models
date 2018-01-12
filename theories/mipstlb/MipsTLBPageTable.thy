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
chapter "Page Table Model for a software loaded TLB"
(* ######################################################################### *)

  
(*<*)
theory MipsTLBPageTable
  imports Main Set MipsTLB
begin
(*>*)  
  
text "A TLB is a cache for the translations stored in a page table. We now 
      provide a formal definition for a page table model to be used in 
      conjunction with the MIPS R4600 TLB model defined earlier."

  
(* ========================================================================= *)  
section "Page Table Specification"
(* ========================================================================= *)

text "We now define the page tabe specification followed by predicates that
      ensure the validity. This page tables specification targets the 
      MIPS R4600 software loaded TLB and would need to be changed if a
      different TLB model is to be used."
  
(* ------------------------------------------------------------------------- *)   
subsection "Definition"  
(* ------------------------------------------------------------------------- *)   
  
  
text "Conceptually the page table store the EntryLO as defined in the MIPS
      R4600 TLB model. We therefore express the page table entry as a 
      partially defined function from a VPN and ASID to an EntryLO where
      the result is undefined if either the ASID or VPN are outside of 
      their valid ranges as defined by the MIPS R4600 TLB model. Note,
      we define the function to take the VPN argument before the ASID 
      to handle updates using global entries as we will see later."
  
  
record MIPSPT = 
  entry :: "VPN \<Rightarrow> ASID \<Rightarrow> TLBENTRYLO"
  

    
(* ------------------------------------------------------------------------- *)   
subsection "Wellformed Page Table Entry"  
(* ------------------------------------------------------------------------- *)   
  
text "The MIPSPT entries are wellformed if their TLBENTRYLO is well formed. 
     Thus  we say that the all entries of the TLB are wellformed if all 
     corresponding TLBENTRYLO are wellformed too. Note that all entries 
     in the page tables are of the smallest page size, which is 4k."
  
definition MIPSPT_Entries_wellformed :: "MIPSPT \<Rightarrow> bool"
  where "MIPSPT_Entries_wellformed pt =
           (\<forall>vpn as. TLBENTRYLOWellFormed ((entry pt) vpn as) MASK4K)"

(* ------------------------------------------------------------------------- *)
subsection "No Global Page Table Entries"
(* ------------------------------------------------------------------------- *)
    
text "We restrict the page table from having global entries. The update function
      of the page table will take care of updating all the entries for the
      different ASIDs accordingly. "
  
definition MIPSPT_Entries_not_global ::  "MIPSPT \<Rightarrow> bool"
  where "MIPSPT_Entries_not_global pt = (\<forall>vpn as. \<not>(g ((entry pt) vpn as)))"


(* ------------------------------------------------------------------------- *)
subsection "A Valid Page Table"
(* ------------------------------------------------------------------------- *)

text "Consequently, we define the page table to be valid, if all its entries
      are well formed as defined in the corresponding predicate and none of
      its entries are marked global."

  
definition MIPSPT_valid :: "MIPSPT \<Rightarrow> bool"
  where "MIPSPT_valid pt = ((MIPSPT_Entries_wellformed pt) 
                              \<and> (MIPSPT_Entries_not_global pt))"    
    

text "Therefore, a valid page table implies that for all ASID and VPN
      the stored EntryLO is well formed and not global."
  
lemma MIPSPT_valid_wellformed:
  "\<And>pt. MIPSPT_valid pt  \<Longrightarrow> 
        \<forall>vpn as. TLBENTRYLOWellFormed ((entry pt) vpn as) MASK4K"
  by(simp add:MIPSPT_valid_def MIPSPT_Entries_wellformed_def)
  
lemma MIPSPT_valid_not_global:
  "\<And>pt. MIPSPT_valid pt \<Longrightarrow> \<forall>vpn as.\<not> g ((entry pt) vpn as)"
  by(simp add:MIPSPT_valid_def MIPSPT_Entries_not_global_def)
    
    
(* ========================================================================= *)  
section "Page Table Operations"
(* ========================================================================= *)   

text "We now define the abstract operations to initialize, read and write
      the page table as defined above and proof assertions about the semantics
      of the operations."
       
  
(* ------------------------------------------------------------------------- *)   
subsection "Initialization"  
(* ------------------------------------------------------------------------- *)   

text "Logically, we model the initialization or creation of the page table
      similar to allocating and zeroing region of memory and thus the
      created page table will contain all NullEntryLo entries."
  
definition MIPSPT_create :: "MIPSPT"
  where "MIPSPT_create = \<lparr> entry = (\<lambda>_. \<lambda>_. null_entry_lo) \<rparr>"


text "Next we proof that when using the MIPSPT-create function from above,
      the resulting page table is valid. For this purpose we show first that
      all the entries are NullEntryLo and then use this lemma to show the 
      validity."
  
lemma MIPSPT_create_all_null:
  "\<forall>vpn as. (entry (MIPSPT_create)) vpn as = null_entry_lo"
  by(auto simp:MIPSPT_create_def)      

lemma MIPSPT_create_valid:
  "MIPSPT_valid (MIPSPT_create)"    
  by(simp add:MIPSPT_valid_def MIPSPT_Entries_wellformed_def 
              MIPSPT_create_all_null NullEntryLoWellFormed MIPSPT_create_def
              MIPSPT_Entries_not_global_def NullEntryLo_not_global)
  
  

(* ------------------------------------------------------------------------- *)   
subsection "Read Operation"  
(* ------------------------------------------------------------------------- *)     

text "The page table read operation returns the EntryLo for the supplied 
      ASID and VPN.  "
  
definition MIPSPT_read :: "ASID \<Rightarrow> VPN \<Rightarrow> MIPSPT \<Rightarrow> TLBENTRYLO"
  where "MIPSPT_read as vpn pt = (entry pt) vpn as"

    
text "The page table reads the null entry for all entries of a newly created / 
      initialized page table and that those entries are wellformed if the
      page table is valid."
  
lemma "\<forall>vpn as. MIPSPT_read as vpn (MIPSPT_create) = null_entry_lo"
  by(auto simp:MIPSPT_read_def MIPSPT_create_def)

lemma MIPSPT_read_wellformed:
  "\<And>pt. MIPSPT_valid pt \<Longrightarrow> 
    (\<forall> as vpn. TLBENTRYLOWellFormed (MIPSPT_read as vpn pt) MASK4K)"
  by(simp add:MIPSPT_valid_def MIPSPT_Entries_wellformed_def MIPSPT_read_def)
    
    
(* ------------------------------------------------------------------------- *)   
subsection "Write Operation"  
(* ------------------------------------------------------------------------- *)    

text "The write operation updates the the entry function of the page table.
      If the entry to be written is global, then the function is updated
      for all the possible ASIDs and the entry is marked non-global."

   
definition MIPSPT_write :: "ASID \<Rightarrow> VPN \<Rightarrow> TLBENTRYLO \<Rightarrow> MIPSPT \<Rightarrow> MIPSPT"
  where "MIPSPT_write as vpn e pt = 
   (if g e then
     \<lparr> entry = (entry pt)(
        vpn := \<lambda>_. \<lparr> pfn=(pfn e), v=(v e), d=(d e), g=False \<rparr>
       ) \<rparr>
    else 
     \<lparr> entry = (entry pt)(vpn := ((entry pt) vpn)(as := e)) \<rparr> )"   
    
    
text "Next we show that the write operation preserves the validity of the
      page tables if the entry to be written is well formed. "
  
lemma MIPSPT_write_valid:
  "\<And>pt. MIPSPT_valid pt \<and> (TLBENTRYLOWellFormed e MASK4K)
               \<Longrightarrow> MIPSPT_valid (MIPSPT_write as vpn e pt)"    
  apply(simp add:MIPSPT_write_def)
  apply(cases "g e")
   apply(simp_all add:MIPSPT_valid_def MIPSPT_Entries_wellformed_def 
                      MIPSPT_Entries_not_global_def)
  apply(simp add:TLBENTRYLOWellFormed_def)
  done   

      
paragraph "Clearing of Entries"    
   
    
text "When a translation is removed the page table entry has to be cleared.
      We can express this operation as a special case of the write operation
      where we write the NullEntryLo to the ASID/VPN of the page table. 
      Likewise, all entries or global entries of the page table can be cleared."
      

definition MIPSPT_clear :: "ASID \<Rightarrow> VPN \<Rightarrow> MIPSPT \<Rightarrow> MIPSPT"
  where "MIPSPT_clear as vpn pt = (MIPSPT_write as vpn null_entry_lo pt)"
    
definition MIPSPT_clearglobal :: "VPN \<Rightarrow> MIPSPT \<Rightarrow> MIPSPT"
  where "MIPSPT_clearglobal vpn pt =  
    \<lparr> entry = (entry pt)(vpn := \<lambda>_. null_entry_lo) \<rparr>"    
    
definition MIPSPT_clearall :: "MIPSPT \<Rightarrow> MIPSPT"
  where "MIPSPT_clearall pt = pt \<lparr> entry := (\<lambda>_. \<lambda>_ . null_entry_lo) \<rparr>"
    
    
text "Any of the clear function above will return the NullEntryLo if
      the entry is read back again."    
  

lemma MIPSPT_clear_is_null_entry:
  "MIPSPT_read as vpn (MIPSPT_clear as vpn pt) = null_entry_lo"
  by(auto simp:MIPSPT_read_def MIPSPT_clear_def MIPSPT_write_def 
               NullEntryLo_not_global)

lemma MIPSPT_clearglobal_null_entry:
  "\<forall>as. MIPSPT_read as vpn (MIPSPT_clearglobal vpn pt) = null_entry_lo"
  by(auto simp:MIPSPT_read_def MIPSPT_clearglobal_def MIPSPT_write_def 
               NullEntryLo_not_global)             
  
lemma MIPSPT_clearall_null_entry:
  "\<forall>as vpn. MIPSPT_read as vpn (MIPSPT_clearall pt) = null_entry_lo"
  by(auto simp:MIPSPT_read_def MIPSPT_clearall_def MIPSPT_write_def 
               NullEntryLo_not_global)              
             
text "Furthermore, clearing the entire page table is equivalent to 
      create or initialize a new page table."

lemma MIPSPT_clearall_is_create :
  "MIPSPT_clearall pt = MIPSPT_create"
  by(auto simp:MIPSPT_create_def MIPSPT_clearall_def) 
    
    
text "Next we show for all of the clear operation variants that the, the
      resulting page table will remain valid."
  
  
lemma MIPSPT_clear_valid:
  "\<And>pt. MIPSPT_valid pt \<Longrightarrow> MIPSPT_valid (MIPSPT_clear as vpn pt)"
  by(simp add:MIPSPT_clear_def MIPSPT_write_def NullEntryLo_not_global
              MIPSPT_valid_def  MIPSPT_Entries_wellformed_def
              NullEntryLoWellFormed MIPSPT_Entries_not_global_def)
            
lemma MIPSPT_clearglobal_valid:
  "\<And>pt. MIPSPT_valid pt \<Longrightarrow> MIPSPT_valid (MIPSPT_clearglobal vpn pt)"    
  by(auto simp:MIPSPT_clearglobal_def MIPSPT_valid_def 
               MIPSPT_Entries_wellformed_def NullEntryLoWellFormed 
               MIPSPT_Entries_not_global_def NullEntryLo_not_global)   

lemma MIPSPT_clearall_valid :
  "\<And>pt. MIPSPT_valid pt \<Longrightarrow> MIPSPT_valid (MIPSPT_clearall pt)"    
  by(auto simp:MIPSPT_clearall_def MIPSPT_valid_def 
               MIPSPT_Entries_wellformed_def NullEntryLoWellFormed 
               MIPSPT_Entries_not_global_def NullEntryLo_not_global)  

             
(* ========================================================================= *)  
section "Address Translation"
(* ========================================================================= *)  

  
text "The translate function takes an  ASID and VPN and produces a set of PFN
      that the ASID-VPN-combination translates to. If the entry is marked as 
      not-valid then there is no translation."
  
definition MIPSPT_translate :: "MIPSPT \<Rightarrow> ASID \<Rightarrow> VPN \<Rightarrow> PFN set"  
  where "MIPSPT_translate pt as vpn = 
      (if (v (MIPSPT_read as vpn pt)) then {(pfn (MIPSPT_read as vpn pt))} 
       else {})"  
    
    
text "Next we show that the translate function will always return an empty 
      or a singleton  set of a particular VPN. In particular, if the entry is 
      valid, then the singleton set is returned, otherwise the empty set."

lemma MIPSPT_translate_set:
  "MIPSPT_translate (MIPSPT_write as vpn e pt) as vpn \<subseteq> {(pfn e)}"
  by(auto simp add: MIPSPT_translate_def MIPSPT_write_def MIPSPT_read_def)
  
lemma MIPSPT_translate_set_valid:
  "\<And>e. (v e) \<Longrightarrow> MIPSPT_translate (MIPSPT_write as vpn e pt) as vpn = {(pfn e)}"
  by(auto simp add: MIPSPT_translate_def MIPSPT_write_def MIPSPT_read_def)

lemma MIPSPT_translate_set_not_valid:
  "\<And>e. \<not>(v e) \<Longrightarrow> MIPSPT_translate (MIPSPT_write as vpn e pt) as vpn = {}"
  by(auto simp add: MIPSPT_translate_def MIPSPT_write_def MIPSPT_read_def)    
    
    
text "The translate function of a newly created or one of the clear operations 
      will result into an empty translation for all VPN."
  
lemma MIPSPT_translate_create_emtpy:
  "\<forall>vpn as. MIPSPT_translate (MIPSPT_create) as vpn = {}"
  by(auto simp:MIPSPT_create_def MIPSPT_translate_def
               MIPSPT_read_def null_entry_lo_def)      

lemma MIPSPT_translate_clearall_emtpy:
  "\<forall>vpn as. MIPSPT_translate (MIPSPT_clearall pt) as vpn = {}"
  by(auto simp:MIPSPT_clearall_def MIPSPT_translate_def
               MIPSPT_read_def null_entry_lo_def)      

lemma MIPSPT_translate_clearglobal_emtpy:
  "\<forall>vpn as. MIPSPT_translate (MIPSPT_clearglobal vpn pt) as vpn = {}"
  by(auto simp:MIPSPT_clearglobal_def MIPSPT_translate_def MIPSPT_write_def
               MIPSPT_read_def null_entry_lo_def)             
             
lemma MIPSPT_translate_clear_emtpy:
  "\<forall>vpn as. MIPSPT_translate (MIPSPT_clear as vpn pt) as vpn = {}"
  by(auto simp:MIPSPT_clear_def MIPSPT_translate_def MIPSPT_write_def
               MIPSPT_read_def null_entry_lo_def)
             

(* ========================================================================= *)  
section "Creating of a TLB Entry"
(* ========================================================================= *)             

text "From the page table we can now create an EntryPair for the MIPS R4600
      TLB model by combining two adjacent entries in the page table. We 
      give a definition on how the TLB entry is created and then show that
      all created entries will be well formed."
  
  
(* ------------------------------------------------------------------------- *)   
subsection "Maximum Number of Entries in the Page Table"  
(* ------------------------------------------------------------------------- *)     
  
text "To ensure that created MIPS TLB entries form the MIPSPT 
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

    
(* ------------------------------------------------------------------------- *)   
subsection "TLB Entry Creation"  
(* ------------------------------------------------------------------------- *)      


text "For a particular ASID and VPN we can create the TLB EntryPair as 
      in the following definition. Because the VPN of the EntryPair needs
      to be even, we need to do a case distinction. We then create
      the TLB EntryPair based on two consecutive entries in the page table."
  
definition MIPSPT_mk_tlbentry :: "MIPSPT \<Rightarrow> ASID \<Rightarrow> VPN \<Rightarrow> TLBENTRY"
  where "MIPSPT_mk_tlbentry pt as vpn = 
        (if (even vpn) then
            TLBENTRY.make MASK4K \<lparr> region=0, vpn2=vpn, asid=as \<rparr> 
                          ((entry pt) vpn as) ((entry pt) (vpn + 1) as) 
           else  
            TLBENTRY.make MASK4K \<lparr> region=0, vpn2=(vpn-1), asid=as \<rparr> 
                          ((entry pt) (vpn - 1) as) ((entry pt) vpn as ))"
   
(* ------------------------------------------------------------------------- *)   
subsection "Queries on created TLB EntryPairs"  
(* ------------------------------------------------------------------------- *)  

text "We provide lemmas to quickly obtain the fields of a  TLB EntryPair
     created from a page table. "  
  
paragraph "ASID" 
text "The ASID is the same as the creation function was invoked with."
  
lemma MIPSPT_TLBENTRY_asid_is :
   "(TLBENTRYHI.asid (hi (MIPSPT_mk_tlbentry pt as vpn))) = as"
  by(auto simp:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)    

paragraph "Page Mask" 
text "The page mask for all entries is always 4kB."             
  
lemma MIPSPT_TLBENTRY_mask_is:
  "(mask (MIPSPT_mk_tlbentry pt as vpn)) = MASK4K"
  by(auto simp:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)

paragraph "VPN" 
text "Depending whether the VPN was odd or even, the VPN2 of the entry is either
      VPN or VPN - 1."      
    
lemma MIPSPT_TLBENTRY_vpn2_is_even :
  "\<And>vpn as pt. even vpn \<Longrightarrow> (vpn2 (hi (MIPSPT_mk_tlbentry pt as vpn))) = vpn"
  by(simp add:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)
             
lemma MIPSPT_TLBENTRY_vpn2_is_odd :
  "\<And>vpn as pt. odd vpn 
        \<Longrightarrow> (vpn2 (hi (MIPSPT_mk_tlbentry pt as vpn))) = vpn - 1"
  by(simp add:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)
    
lemma MIPSPT_TLBENTRY_vpn2_is :
  "\<And>vpn as pt. (vpn2 (hi (MIPSPT_mk_tlbentry pt as vpn))) = 
          (if (even vpn) then vpn else (vpn -1 ))"
  by(simp add:MIPSPT_TLBENTRY_vpn2_is_odd MIPSPT_TLBENTRY_vpn2_is_even)
    
paragraph "Minimum and Maximum VPN" 
text "The minimum and maximum VPN an entry can have, depends on whether
      the VPN is even or odd and can be obtained as follows."       

lemma MIPSPT_TLBENTRY_Min4kVPN_even: 
  "even vpn \<Longrightarrow> EntryMin4KVPN (MIPSPT_mk_tlbentry pt as vpn) = vpn"
  by(simp add:MIPSPT_mk_tlbentry_def TLBENTRY.make_def EntryMin4KVPN_def)

lemma MIPSPT_TLBENTRY_Max4kVPN_even: 
  "even vpn \<Longrightarrow> EntryMax4KVPN (MIPSPT_mk_tlbentry pt as vpn) = Suc vpn"
  by(simp add:MIPSPT_mk_tlbentry_def TLBENTRY.make_def EntryMax4KVPN_def)
  
lemma MIPSPT_TLBENTRY_Min4kVPN_odd: 
  "odd vpn \<Longrightarrow> EntryMin4KVPN1 (MIPSPT_mk_tlbentry pt as vpn) = vpn"
  by(simp add:MIPSPT_mk_tlbentry_def TLBENTRY.make_def EntryMin4KVPN1_def)

paragraph "Address Range"
text "The address range that an entry covers is given by the minimum and 
     maximum VPN multiplied by the page size"
  
lemma MIPSPT_TLBENTRY_range_even :
  "\<And>pt as vpn.  even vpn 
        \<Longrightarrow> EntryRange (MIPSPT_mk_tlbentry pt as vpn) 
                   = {x. vpn * 4096 \<le> x \<and> x < (vpn + 2) * 4096}"
  by(simp add:EntryRange_def EntrySize_def EntryMinVA_def EntryMaxVA_def 
              MIPSPT_TLBENTRY_mask_is MIPSPT_TLBENTRY_vpn2_is_even KB_def, 
              auto)
        
    
(* ------------------------------------------------------------------------- *)   
subsection "The Created Entry is Well Formed"  
(* ------------------------------------------------------------------------- *)  
  
text "We must make sure that the TLB keeps valid when a created entry is
      written into the TLB. For this we need to show that a created entry
      from the page table will be well formed with respect to the MIPS
      R4600 TLB model specification. We therefore show first that the
      VPN will always be even and within valid bounds."
  
lemma MIPSPT_TLBENTRY_vpn2_even: 
  "\<forall>vpn. (even (vpn2 (hi (MIPSPT_mk_tlbentry pt as vpn))))"
  by(auto simp:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)


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
  have aeven: 
    "even MIPSPT_EntriesMax" 
    by(simp add:MIPSPT_EntriesMax_def)
  with bound even aeven have X0: 
    "vpn \<le> MIPSPT_EntriesMax - 2"
    by(simp add:VPNEvenBounds)
  from X0 have X1: 
    "(Suc vpn) \<le> (MIPSPT_EntriesMax - 1)" 
    by(auto simp:MIPSPT_EntriesMax_def)
  with X1 show ?thesis by(auto)
qed    


text "Next we use the lemmas from above to show that the created EntryPair will
      have a valid EntryHi part. "

lemma MIPSPT_TLBENTRYHI_wellformed:
  "\<And>vpn as pt. MIPSPT_valid pt \<Longrightarrow> vpn < MIPSPT_EntriesMax \<Longrightarrow> ASIDValid as \<Longrightarrow>
             TLBENTRYHIWellFormed (hi (MIPSPT_mk_tlbentry pt as vpn)) MASK4K"
  by(auto simp:MIPSPT_mk_tlbentry_def TLBENTRYHIWellFormed_def TLBENTRY.make_def 
               MIPSPT_valid_def VPN2Valid_def VPNMin_def VPN2Max_def MB_def 
               MIPSPT_EntriesMax_def VPNEvenBounds)    


text "And finally we show that the created TLB EntryPair will always be 
      well formed."
     
lemma MIPSPT_TLBENTRY_wellformed:
   "\<And>pt vpn as. MIPSPT_valid pt \<Longrightarrow> vpn < MIPSPT_EntriesMax \<Longrightarrow> ASIDValid as
         \<Longrightarrow> TLBENTRYWellFormed ( MIPSPT_mk_tlbentry pt as vpn)"
  apply(simp add:TLBENTRYWellFormed_def)
  apply(simp add:MIPSPT_TLBENTRYHI_wellformed MIPSPT_TLBENTRY_mask_is)
  apply(simp add:MIPSPT_valid_def MIPSPT_Entries_wellformed_def)
  apply(simp add:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)
  done
    
    
(* ------------------------------------------------------------------------- *)   
subsection "Entry is not Global"
(* ------------------------------------------------------------------------- *)               

text "If the page table was in a valid state, then the created TLB EntryPair
      will be not global for any VPN and ASID." 

             
lemma MIPSPT_TLBENTRY_not_global:
  "\<And>pt. MIPSPT_valid pt
          \<Longrightarrow> \<forall>vpn as. \<not>EntryIsGlobal (MIPSPT_mk_tlbentry pt as vpn)"
  by(simp add:MIPSPT_valid_def MIPSPT_Entries_not_global_def
                 EntryIsGlobal_def MIPSPT_mk_tlbentry_def TLBENTRY.make_def)
             

(* ------------------------------------------------------------------------- *)   
subsection "Entry Match"
(* ------------------------------------------------------------------------- *)                
    
text "The ASID match function will always evaluate to true for a EntryPair if
      the ASID is equal to the one used for creating the TLB EntryPair."    
    
lemma MIPSPT_TLBENTRY_asidmatch:
  "EntryASIDMatchA as  (MIPSPT_mk_tlbentry pte as vpn)"
  by(auto simp:EntryASIDMatchA_def MIPSPT_mk_tlbentry_def TLBENTRY.make_def)

lemma "\<And>as1 as2. \<forall> mpt vpn. 
       as1 = as2 \<Longrightarrow>  EntryASIDMatch (MIPSPT_mk_tlbentry (pte mpt) as1 vpn)
                                     (MIPSPT_mk_tlbentry (pte mpt) as2 vpn)" 
   by(simp add: EntryASIDMatch_def)  

text "The EntryPair will match on the first/second half if the VPN was the
      same as used when creating the entry, and the VPN was odd or even
      respectively. "
     
lemma MIPSPT_TLBENTRY_match0_even :
  "even vpn \<Longrightarrow> EntryMatchVPNASID0 vpn as (MIPSPT_mk_tlbentry pt as vpn)"
  by(simp add:EntryMatchVPNASID0_def MIPSPT_mk_tlbentry_def TLBENTRY.make_def
              EntryVPNMatchV0_def EntryMin4KVPN_def EntryMin4KVPN1_def 
              EntryASIDMatchA_def)
  

lemma MIPSPT_TLBENTRY_match1_odd :
  "odd vpn \<Longrightarrow> EntryMatchVPNASID1 vpn as (MIPSPT_mk_tlbentry pt as (vpn))"
  by(simp add:EntryMatchVPNASID1_def MIPSPT_mk_tlbentry_def TLBENTRY.make_def
              EntryASIDMatchA_def EntryVPNMatchV1_def  EntryMin4KVPN1_def 
              EntryMax4KVPN_def)
  

text "Lastly, we show that for all ASID and VPNs there will be a match if
      the same ASID or VPN has been used to create the TLB EntryPair."    
    
lemma MIPSPT_TLBENTRY_match :
  "EntryMatchVPNASID vpn as (MIPSPT_mk_tlbentry pt as vpn)"
  by(simp add:EntryMatchVPNASID_def MIPSPT_TLBENTRY_asidmatch EntryVPNMatchV_def
              EntryMin4KVPN_def EntryMax4KVPN_def MIPSPT_TLBENTRY_mask_is
              MIPSPT_mk_tlbentry_def TLBENTRY.make_def EntryASIDMatchA_def) 

    

(* ------------------------------------------------------------------------- *)   
subsection "Entry Equivalence"
(* ------------------------------------------------------------------------- *)              

text "For two consecutive VPNs the entries are actually the same"

lemma MIPSPT_TLBENTRY_equal_odd:
  "odd vpn \<Longrightarrow> (MIPSPT_mk_tlbentry pt as vpn)
                   = (MIPSPT_mk_tlbentry pt as (vpn - 1))"  
  by(simp add:MIPSPT_mk_tlbentry_def)

lemma MIPSPT_TLBENTRY_equal_even:
  "even vpn \<Longrightarrow> (MIPSPT_mk_tlbentry pt as vpn) 
                   = (MIPSPT_mk_tlbentry pt as (vpn + 1))"  
  by(simp add:MIPSPT_mk_tlbentry_def)    

(* ------------------------------------------------------------------------- *)   
subsection "Translate Function"
(* ------------------------------------------------------------------------- *)      

text "We can now simplify the translate function for a created TLB entry."  
  
lemma MIPSPT_TLBENTRY_translate_is :
  "(TLBENTRY_translate (MIPSPT_mk_tlbentry pte as vpn) as vpn) = 
   (if (v ((entry pte) vpn as)) then {(pfn ((entry  pte) vpn as))} else {})"
  apply(cases "even vpn", simp_all add:TLBENTRY_translate_def MIPSPT_TLBENTRY_match)
   apply(simp_all add:MIPSPT_mk_tlbentry_def TLBENTRY.make_def EntryIsValid0_def
                      EntryIsValid1_def EntryMin4KVPN_def EntryMin4KVPN1_def)
  done  
    
        
(*>*)
end  
(*<*)
