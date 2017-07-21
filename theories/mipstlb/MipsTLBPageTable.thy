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

text "The MIPS PageTable has 256M x 4kB entries to fill the entire 1TB virtual 
      address space."
  
definition MIPSPT_EntriesMax :: nat
  where "MIPSPT_EntriesMax = 268435456"   
  
lemma "MIPSPT_EntriesMax * 4096 = GB 1024"
  by(auto simp:MIPSPT_EntriesMax_def GB_def)
  
text "The PageTable is a partially defined function from a VPN to an EntryLo
      and the page table is created for a particular ASID."
  
record MIPSPT = 
  entry :: "VPN \<Rightarrow> TLBENTRYLO"
  asid :: ASID

    
    
(* ========================================================================= *)  
section "Page Table operations"
(* ========================================================================= *)   


(* ------------------------------------------------------------------------- *)   
subsection "Initialization"  
(* ------------------------------------------------------------------------- *)   

text "The page table is initialized by zeroing out all entries."
  
definition MIPSPT_create :: "ASID \<Rightarrow> MIPSPT"
  where "MIPSPT_create as = \<lparr> entry = (\<lambda>_. null_entry_lo), asid=as \<rparr>"


text "The newly initialized page table has all entries of the null
      entry lo"
lemma "\<forall>vpn. (entry (MIPSPT_create as)) vpn = null_entry_lo"
  by(auto simp:MIPSPT_create_def)  
  

(* ------------------------------------------------------------------------- *)   
subsection "Read Page Table Entry"  
(* ------------------------------------------------------------------------- *)     


text "Reads the entry with a particular VPN from the page table."
  
definition MIPSPT_read :: "VPN \<Rightarrow> MIPSPT \<Rightarrow> TLBENTRYLO"
  where "MIPSPT_read vpn pt = (entry pt) vpn"
    
text "The page table reads the null entry for all entries of a newly created
      page table."
  
lemma "\<forall>vpn. MIPSPT_read vpn (MIPSPT_create as) = null_entry_lo"
  by(auto simp:MIPSPT_read_def MIPSPT_create_def)
    
    
(* ------------------------------------------------------------------------- *)   
subsection "Write Page Table Entry"  
(* ------------------------------------------------------------------------- *)    

text "Writes an entry in the MIPS Page Table"  
  
definition MIPSPT_write :: "VPN \<Rightarrow> TLBENTRYLO \<Rightarrow> MIPSPT \<Rightarrow> MIPSPT"
  where "MIPSPT_write vpn e pt =  \<lparr> entry = (entry pt)(vpn := e), asid=(asid pt)\<rparr>"

text "An entry can be cleared, by writing it with the Null entry"
    
definition MIPSPT_clear :: "VPN \<Rightarrow> MIPSPT \<Rightarrow> MIPSPT"
  where "MIPSPT_clear vpn pt = (MIPSPT_write vpn null_entry_lo pt)"
    
definition MIPSPT_clearall :: "MIPSPT \<Rightarrow> MIPSPT"
  where "MIPSPT_clearall pt = pt \<lparr> entry := (\<lambda>_. null_entry_lo) \<rparr> "
    

text "An entry that is written to, is read back after wards"
lemma "\<And>vpn e. MIPSPT_read vpn (MIPSPT_write vpn e pt) = e"
  by(auto simp:MIPSPT_read_def MIPSPT_write_def)

text "An entry that is cleared reads as null entry"    
lemma "\<And>vpn e. MIPSPT_read vpn (MIPSPT_clear vpn pt) = null_entry_lo"
  by(auto simp:MIPSPT_read_def MIPSPT_clear_def MIPSPT_write_def)
    
text "clearing a page tabel is equvalent to crate a new page table with the same
      ASID."    
lemma "\<And>pt. MIPSPT_clearall pt = MIPSPT_create (asid pt)"
  by(auto simp:MIPSPT_create_def MIPSPT_clearall_def) 
    

(* ========================================================================= *)  
section "VPN to PFN translation"
(* ========================================================================= *)  

text "The translate function converts a VPN into a set of PFN it translates to."  
  
definition MIPSPT_translate :: "MIPSPT \<Rightarrow> VPN \<Rightarrow> PFN set"  
  where "MIPSPT_translate pt vpn =  (if (v (MIPSPT_read  vpn pt)) then
                                       {(pfn (MIPSPT_read vpn pt))} 
                                       else {}) "  

text "The translate function will always return an empty or a singleton
      set of a particular vpn"    

lemma "MIPSPT_translate (MIPSPT_write vpn e pt) vpn \<subseteq> {(pfn e)}"
  by(auto simp add: MIPSPT_translate_def MIPSPT_write_def MIPSPT_read_def)

    
text "The translate function of a newly created or cleared page table is empty
      for all vpn"
  
lemma "\<forall>vpn. MIPSPT_translate (MIPSPT_create as) vpn = {}"
  by(auto simp:MIPSPT_create_def MIPSPT_translate_def
               MIPSPT_read_def null_entry_lo_def)      

lemma "\<forall>vpn. MIPSPT_translate (MIPSPT_clearall pt) vpn = {}"
  by(auto simp:MIPSPT_clearall_def MIPSPT_translate_def
               MIPSPT_read_def null_entry_lo_def)      
    
lemma "\<forall>vpn. MIPSPT_translate (MIPSPT_clear vpn pt) vpn = {}"
  by(auto simp: MIPSPT_translate_def MIPSPT_clear_def MIPSPT_write_def MIPSPT_read_def 
                null_entry_lo_def)

(* ========================================================================= *)  
section "Creating of a TLB Entry"
(* ========================================================================= *)               

definition MIPSPT_mk_tlbentry :: "MIPSPT \<Rightarrow> VPN \<Rightarrow> TLBENTRY"
  where "MIPSPT_mk_tlbentry pt vpn = 
      (if (even vpn) then
           TLBENTRY.make MASK4K  \<lparr> vpn2=vpn, asid=(asid pt) \<rparr> 
                         ((entry pt) vpn) ((entry pt) (vpn + 1)) 
        else  
           TLBENTRY.make MASK4K  \<lparr> vpn2=(vpn-1), asid=(asid pt) \<rparr> 
                         ((entry pt) (vpn - 1)) ((entry pt) vpn))"

lemma "\<forall>vpn. (even (vpn2 (hi (MIPSPT_mk_tlbentry pt vpn))))"
  by(auto simp:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)
    
    
end  

