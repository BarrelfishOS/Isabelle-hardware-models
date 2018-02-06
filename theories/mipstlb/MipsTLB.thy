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
chapter "The MIPS R4600 TLB Model - A software loaded TLB"
(* ######################################################################### *)


(*<*)
theory MipsTLB
  imports Main Set "../model/Model" "../model/Syntax" Parity Nat
begin
(*>*)  

  
(* ========================================================================= *)
section "Helper definitions"
(* ========================================================================= *)
  
text "Getting a nicer representation for kB and MB"
  
definition KB :: "nat \<Rightarrow> nat" 
  where "KB n = n * 1024"

definition MB :: "nat \<Rightarrow> nat" 
  where "MB n = n * 1048576"

definition GB :: "nat \<Rightarrow> nat" 
  where "GB n = n * 1073741824"


(* ========================================================================= *)    
section "Basic type definitions"
(* ========================================================================= *)  

text "First we define base types we use in the TLB. This are the Virtual Page 
     Number (VPN), the Physical Frame Number (PFN), the Address Space 
     Identifier (ASID) and the Page Mask."  

  
(* ------------------------------------------------------------------------- *)  
subsection "Page MASK"
(* ------------------------------------------------------------------------- *)

text "The MASK defines which bits are used in matching the TLB entry as well
      as the page size used for this mapping."
  
datatype MASK = MASK4K | MASK16K | MASK64K | MASK256K | MASK1M | MASK4M | MASK16M 

(*
primrec mask_val :: "MASK \<Rightarrow> nat"  where 
  "mask_val(MASK4K)   = 0"    |  "mask_val(MASK16K)  = 3"    |
  "mask_val(MASK64K)  = 15"   |  "mask_val(MASK256K) = 63"   | 
  "mask_val(MASK1M)   = 255"  |  "mask_val(MASK4M)   = 1023" | 
  "mask_val(MASK16M)  = 4095"
*)
  
primrec page_size :: "MASK \<Rightarrow> nat" where
  "page_size(MASK4K)   = KB 4"   |  "page_size(MASK16K)  = KB 16"  |
  "page_size(MASK64K)  = KB 64"  |  "page_size(MASK256K) = KB 256" | 
  "page_size(MASK1M)   = MB 1"   |  "page_size(MASK4M)   = MB 4"   | 
  "page_size(MASK16M)  = MB 16"

primrec page_count :: "MASK \<Rightarrow> nat" where
  "page_count(MASK4K)   = MB 256" |  "page_count(MASK16K)  = MB 64"  |
  "page_count(MASK64K)  = MB 16"  |  "page_count(MASK256K) = MB 4"   | 
  "page_count(MASK1M)   = MB 1"   |  "page_count(MASK4M)   = KB 256" | 
  "page_count(MASK16M)  = KB 64"

primrec frame_count :: "MASK \<Rightarrow> nat" where
  "frame_count(MASK4K)   = MB 16" |  "frame_count(MASK16K)  = MB 4"   |
  "frame_count(MASK64K)  = MB 1"  |  "frame_count(MASK256K) = KB 256" | 
  "frame_count(MASK1M)   = KB 64" |  "frame_count(MASK4M)   = KB 16"  | 
  "frame_count(MASK16M)  = KB 4"    


primrec num_4k_pages :: "MASK \<Rightarrow> nat" where
  "num_4k_pages(MASK4K)   = 1"     |  "num_4k_pages(MASK16K)  = 4"   |
  "num_4k_pages(MASK64K)  = 16"    |  "num_4k_pages(MASK256K) = 64" | 
  "num_4k_pages(MASK1M)   = 256"   |  "num_4k_pages(MASK4M)   = 1024"  | 
  "num_4k_pages(MASK16M)  = 40961"   

  
(* ------------------------------------------------------------------------- *)  
subsection "Virtual Page Number"  
(* ------------------------------------------------------------------------- *)  
  
text "The Virtual Page Number (VPN) identifies a page of a given size in a 
      40-bit virtual genaddress space (1 TB)"

definition VASize :: nat 
  where "VASize = 1099511627776"   (* 1TB *)    
  
    
text "We define the VPN to be of type nat"     

type_synonym VPN = nat

  
text "The minimum valid VPN is always 0, whereas the maximum VPN depends on
      the page size"  
  
definition VPNMin :: nat
  where "VPNMin = 0"
  
definition VPNMax :: "MASK \<Rightarrow> nat"
  where "VPNMax m = ((page_count m) - 1)"

definition VPN2Max :: "MASK \<Rightarrow> nat"
  where "VPN2Max m = ((page_count m) - 2)"    
    
definition VPNValid :: "MASK \<Rightarrow> nat \<Rightarrow> bool"
  where "VPNValid m vpn = ((VPNMin \<le> vpn) \<and> (vpn \<le> (VPNMax m)))"

definition VPN2Valid :: "MASK \<Rightarrow> nat \<Rightarrow> bool"
  where "VPN2Valid m vpn = ((VPNMin \<le> vpn) \<and> (vpn \<le> (VPN2Max m)) \<and> (even vpn))"    
    
definition VPNValidList :: "MASK \<Rightarrow> nat list"
  where "VPNValidList m = [0..<Suc (VPNMax m)]"

definition VPNValidSet :: "MASK \<Rightarrow> nat set"
  where "VPNValidSet m = {a. VPNMin \<le> a \<and> a \<le> (VPNMax m)}"

    
text "The following lemmas ensure that the maximum VPN multiplied with the page
     size always equals the VASize. Note, we have to add 1 or 2 respectively."

lemma "page_count (m) * page_size(m) = VASize"  
  by(cases m, simp_all add:VASize_def GB_def MB_def KB_def)
  
lemma  "((VPNMax m) + 1) * (page_size m) = VASize"
  by(cases m, simp_all add:VPNMax_def GB_def MB_def KB_def VASize_def)

lemma  "((VPN2Max m) + 2) * (page_size m) = VASize"
  by(cases m, simp_all add:VPN2Max_def GB_def MB_def KB_def VASize_def)    
  
    
text "The VPN 0 is always valid for all page sizes."    
  
lemma VPN0Valid : "\<forall>m. VPNValid m 0"
  by(simp add:VPNValid_def VPNMin_def)     
    
    
lemma "VPN2Valid m vpn \<Longrightarrow> VPNValid m vpn"
  by(auto simp add:VPN2Valid_def VPNValid_def VPNMin_def VPN2Max_def VPNMax_def)

    
(* ------------------------------------------------------------------------- *)    
subsection "Physical Frame Number"  
(* ------------------------------------------------------------------------- *)  

text "The Physical Frame Number (PFN) is an index into the array of physical frames.
      There is a physical genaddress space of 36 bits or 64 GB. The maximum number of 
      frames depends on the actual frame size i.e. the MASK. "
  
definition PASize :: nat 
  where "PASize = GB 64"  
  
    
text "We define the PFN to be of type NAT"
  
type_synonym PFN = nat


text "The minimum valid PFN is always zero, whereas the maximum valid PFN
      depends on the used page size."
  
definition PFNMin :: nat
  where "PFNMin = 0"
  
definition PFNMax :: "MASK \<Rightarrow> nat"
  where "PFNMax m = (frame_count m) - 1"
       
definition PFNValid :: "MASK \<Rightarrow> nat \<Rightarrow> bool"
  where "PFNValid m a = ((PFNMin \<le> a) \<and> (a \<le> PFNMax m))"
    
definition PFNValidList :: "MASK \<Rightarrow> nat list"
  where "PFNValidList m = [0..<Suc (PFNMax m)]"

definition PFNValidSet :: "MASK \<Rightarrow> nat set"
  where "PFNValidSet m = {a. PFNMin \<le> a \<and> a \<le> (PFNMax m)}"    
    

text "The following lemmas proof that the maximum PFN multiplied by the
      actual page number is always the physical genaddress space size."
  
lemma  "((PFNMax m) + 1) * (page_size m) = PASize"
  by(cases m, simp_all add:PFNMax_def PASize_def GB_def MB_def KB_def)

    
text "The PFN 0 is always a valid one."
  
lemma PFN0Valid : "\<forall>m. PFNValid m 0"
  by(simp add:PFNValid_def PFNMin_def)    
  

(* ------------------------------------------------------------------------- *)      
subsection "Address Space Identifier"
(* ------------------------------------------------------------------------- *)    
  
text "The Address Space Identifier (ASID) is an 8-bit number identifying the 
      current genaddress space that is active and hence the 'view' of the system"

type_synonym ASID = nat
  

text "ASID are 8 bits and thus range from 0 to 255."  
  
definition ASIDMin :: nat
  where "ASIDMin = 0"
  
definition ASIDMax :: nat
  where "ASIDMax = 256"
      
    
definition ASIDValid :: "nat \<Rightarrow> bool"
  where "ASIDValid a = ((ASIDMin \<le> a) \<and> (a < ASIDMax))"
    
definition ASIDValidList :: "nat list"
  where "ASIDValidList = [0..<ASIDMax]"

definition ASIDValidSet :: "nat set"
  where "ASIDValidSet = {(a::nat). ASIDMin \<le> a \<and> a < ASIDMax}"    
    
text "ASID 0 is always valid"
  
lemma ASID0Valid : "ASIDValid 0"
  by(simp add:ASIDValid_def ASIDMin_def ASIDMax_def)

lemma ASIDValidSet_notempty :
  "ASIDValidSet \<noteq> {}"
  apply(simp add:ASIDValidSet_def ASIDMin_def ASIDMax_def)
  apply(rule exI[where x = 0], auto)
  done 

(* ------------------------------------------------------------------------- *)     
subsection "Offset" 
(* ------------------------------------------------------------------------- *)   

text "The offset is the index into a page. The maximum offset depends on the 
      page size."
  
type_synonym OFFSET = nat
  
definition OFFSETMin :: nat
  where "OFFSETMin = 0"
  
definition OFFSETMax :: "MASK \<Rightarrow> nat"
  where "OFFSETMax m = (page_size m) - 1"

definition OFFSETValid :: "MASK \<Rightarrow> nat \<Rightarrow> bool"
  where "OFFSETValid m a = ((OFFSETMin \<le> a) \<and> (a \<le> OFFSETMax m))"
    
definition OFFSETValidList :: "MASK \<Rightarrow> nat list"
  where "OFFSETValidList m = [0..<Suc (OFFSETMax m)]"

definition OFFSETValidSet :: "MASK \<Rightarrow> nat set"
  where "OFFSETValidSet m = {a. OFFSETMin \<le> a \<and> a \<le> (OFFSETMax m)}"        
    
    
(* ------------------------------------------------------------------------- *)    
subsection "Compound Types"
(* ------------------------------------------------------------------------- *)
  
text "Based on the those base types we can define more complex types like virtual
     genaddress and physical genaddress as follows"
    
type_synonym VA = "ASID \<times> VPN \<times> OFFSET"
type_synonym PA = "PFN \<times> OFFSET"


  
(* ========================================================================= *)  
section "TLB Registers and TLB entry fields"
(* ========================================================================= *)  

text "We now define the relevant TLB registers, which are writable by software.
      The TLB entries can only be update using this registers"

  
(* ------------------------------------------------------------------------- *) 
subsection "EntryHi"
(* ------------------------------------------------------------------------- *)   

text "The EntryHi stores the Virtual Page Number of the entry pair and the 
      Address space identifier of the entry."
  
record TLBENTRYHI = 
  region :: nat
  vpn2 :: VPN
  asid :: ASID

  
text "The EntryHi is well formed, if its VPN and ASID are within the valid range"
  
definition TLBENTRYHIWellFormed :: "TLBENTRYHI \<Rightarrow> MASK \<Rightarrow> bool"
  where "TLBENTRYHIWellFormed hi m =((VPN2Valid m (vpn2 hi)) \<and> ASIDValid (asid hi))"

    
text "The NullEntryHi has the VPN2 of 0 and the ASID of 0. "  

definition null_entry_hi :: TLBENTRYHI
  where "null_entry_hi = \<lparr> region=0, vpn2=0, asid=0 \<rparr>"
    
    
text "The NullEntryHi is valid."    
  
lemma NullEntryHiWellFormed : 
  "TLBENTRYHIWellFormed null_entry_hi MASK4K"
 by(auto simp:TLBENTRYHIWellFormed_def null_entry_hi_def
              ASID0Valid VPN2Valid_def VPNMin_def)
 

(* ------------------------------------------------------------------------- *)  
subsection "EntryLo"
(* ------------------------------------------------------------------------- *)    

text "The EntryLo stores the associated Physical Frame Number together with bits
      indicating whether the PFN is valid, or writable. "
  
record TLBENTRYLO = 
  pfn :: PFN
  v   :: bool  
  d   :: bool
  g   :: bool
  
text "The EntryLo is well formed if the PFN is in the valid range."
  
definition TLBENTRYLOWellFormed :: "TLBENTRYLO \<Rightarrow> MASK \<Rightarrow> bool"
  where "TLBENTRYLOWellFormed lo m = (PFNValid m (pfn lo))"

text "The NullEntryLo has PFN, v, d, g, all zeros."
    
definition null_entry_lo :: TLBENTRYLO where
  "null_entry_lo = \<lparr> pfn=0, v=False, d=False, g=False \<rparr>"
    
lemma NullEntryLoWellFormed :
  "TLBENTRYLOWellFormed null_entry_lo MASK4K"
  by(auto simp:TLBENTRYLOWellFormed_def null_entry_lo_def  PFN0Valid)

lemma NullEntryLo_not_global :
  "\<not>g null_entry_lo"
  by(simp add:null_entry_lo_def)
  
    
(* ------------------------------------------------------------------------- *)    
subsection "TLB Entry"
(* ------------------------------------------------------------------------- *)    

text "The TLB Entry represents an entry pair and includes an EntryHi fields, two
      EntryLo fields and a mask field indicating the size of the mapping
      represented by the entry pair. "
  
record TLBENTRY = 
  mask :: MASK
  hi   :: TLBENTRYHI
  lo0  :: TLBENTRYLO
  lo1  :: TLBENTRYLO

  
text "The TLBEntry is well formed if is EntryHi and the two EntryLo are well formed"  
definition TLBENTRYWellFormed :: "TLBENTRY \<Rightarrow> bool"
  where "TLBENTRYWellFormed e = ((TLBENTRYHIWellFormed (hi e) (mask e))  \<and> 
                            (TLBENTRYLOWellFormed (lo0 e) (mask e)) \<and> 
                            (TLBENTRYLOWellFormed (lo1 e) (mask e)))"  

    
text "We define the reset function on the TLBEntry to set the EntryLo to zero
     and the VPN2 of EntryHi to index. Note the VPN2 has to be even, so we
     multiply the index with two."    
  
definition TLBEntryReset :: "nat \<Rightarrow> TLBENTRY"
  where "TLBEntryReset idx = TLBENTRY.make MASK4K \<lparr> region=0, vpn2=(idx * 2), asid=0 \<rparr> 
                                           null_entry_lo null_entry_lo"

text "The NullEntry is the rest with index 0"

definition null_entry :: TLBENTRY where
  "null_entry = TLBEntryReset 0"

text "For all entries, the TLB Entry at reset is well formed"
  
lemma TLBEntryResetWellFormed :
  "\<And>x. (2 * x) < VPN2Max MASK4K \<Longrightarrow> TLBENTRYWellFormed(TLBEntryReset x)"
  by(simp add:TLBENTRYWellFormed_def TLBEntryReset_def TLBENTRY.make_def 
              NullEntryLoWellFormed TLBENTRYHIWellFormed_def ASID0Valid 
              VPN2Valid_def VPNMin_def VPN2Max_def MB_def)

lemma TLBEntryResetASID_is :
  "\<And>idx. (asid (hi (TLBEntryReset x))) = 0"
  by(auto simp:TLBEntryReset_def TLBENTRY.make_def)

lemma TLBEntryResetVPN2_is :
  "\<And>idx. (vpn2 (hi (TLBEntryReset x))) = 2*x"
  by(auto simp:TLBEntryReset_def TLBENTRY.make_def)

lemma TLBEntryResetMask_is:
  "(mask (TLBEntryReset i)) = MASK4K"
  by(auto simp:TLBEntryReset_def TLBENTRY.make_def)
  


text "The NULL Entry is always valid"    
    
lemma NullEntryIsValid :
  "TLBENTRYWellFormed null_entry"
  by(simp add:null_entry_def TLBEntryResetWellFormed TLBEntryReset_def
              TLBENTRY.make_def TLBENTRYWellFormed_def TLBENTRYHIWellFormed_def
              NullEntryLoWellFormed VPN2Valid_def VPNMin_def ASIDValid_def 
              ASIDMin_def ASIDMax_def)
  
  
    
text "A well formed TLB Entry has a valid ASID and VPN"
            
lemma TLBENTRYWellFormedASIDValid : 
  "TLBENTRYWellFormed e \<Longrightarrow>  ASIDValid (asid (hi e))"
  by(simp add: TLBENTRYWellFormed_def TLBENTRYHIWellFormed_def)    

lemma TLBENTRYWellFormedVPN2Valid:
  "TLBENTRYWellFormed e \<Longrightarrow>  VPN2Valid (mask e) (vpn2 (hi e))"
  by(auto simp add: TLBENTRYWellFormed_def TLBENTRYHIWellFormed_def)
    
    
(* ------------------------------------------------------------------------- *)      
subsection "The MIPS TLB"
(* ------------------------------------------------------------------------- *)    

text "The MIPS TLB has a fixed number of entries ('capacity') where some of them
      are wired and not replaced by the random replacement."

record MIPSTLB = 
  capacity  :: nat
  wired     :: nat
  random    :: nat
  entries   :: "nat \<Rightarrow> TLBENTRY"

  
text "The MIPS TLB has in total 48 entries, of which are at maximum 32 wired."

definition MIPSR4600Capacity :: nat
  where "MIPSR4600Capacity = 48"
    
definition TLBMaximumWired :: nat
  where "TLBMaximumWired  = 48"

text "The following creates an invalid TLB, which also satisfies that state
      after reset."
  
definition invalid_tlb :: "MIPSTLB"
  where "invalid_tlb = \<lparr> capacity = MIPSR4600Capacity, 
                         wired    = 0, 
                         random   = MIPSR4600Capacity - 1,
                         entries  = (\<lambda>_. null_entry) \<rparr>"    

    
(* ========================================================================= *)  
section "Queries on the TLB Entry"
(* ========================================================================= *)
  
text "In the following we define functions to obtain the properties of the
      TLB entries"
  
  
(* ------------------------------------------------------------------------- *)     
subsection "Global Entry"
(* ------------------------------------------------------------------------- *)   

text "The entry is considered global, if both global bits in the EntryLo are
      set."

definition EntryIsGlobal :: "TLBENTRY \<Rightarrow> bool"
  where "EntryIsGlobal e = ((g (lo1 e)) \<and>  (g (lo0 e)))"    
  
(* ------------------------------------------------------------------------- *)      
subsection "Entry Size"
(* ------------------------------------------------------------------------- *)      
  
text "The MASK defines the size of the mapping for this entry. Each entry is. 
      effectively an entry pair, and thus maps 2x the page size defined by the
      MASK."

definition EntrySize :: "TLBENTRY \<Rightarrow> nat " where
  "EntrySize e = (page_size (mask e))"

definition EntryPairSize :: "TLBENTRY \<Rightarrow> nat"
  where "EntryPairSize e = (EntrySize e) + (EntrySize e)"  

text "The size of an entry is always positive"
  
  
lemma EntrySize_positive:
  "0 < EntrySize e"
  by(cases "mask e", simp_all add:EntrySize_def KB_def MB_def)

lemma EntryPairSize_positive:
  "0 < EntryPairSize e"
  by(cases "mask e", simp_all add:EntryPairSize_def EntrySize_positive)


(* ------------------------------------------------------------------------- *)
subsection "Obtaining the minimum and maximum VA"
(* ------------------------------------------------------------------------- *)

text {* The entry pair maps the range [EntryMinVA, EntryMaxVA). Divided into two
        ranges [EntryMinVA0, EntryMaxVA0] and [EntryMinVA1, EntryMaxVA1]  *}

definition EntryMinVA :: "TLBENTRY \<Rightarrow> genaddr" where
  "EntryMinVA e = (vpn2 (hi e)) * page_size (mask e)"
  
definition EntryMaxVA :: "TLBENTRY \<Rightarrow> genaddr" where
  "EntryMaxVA e = (EntryMinVA e) + (EntrySize e) + (EntrySize e) - 1"
  
definition EntryMinVA0 :: "TLBENTRY \<Rightarrow> genaddr" where
  "EntryMinVA0 e = (EntryMinVA e)"
  
definition EntryMaxVA0 :: "TLBENTRY \<Rightarrow> genaddr" where
  "EntryMaxVA0 e = ((EntryMinVA0 e) + (EntrySize e) - 1)"
  
definition EntryMinVA1 :: "TLBENTRY \<Rightarrow> genaddr" where
  "EntryMinVA1 e = ((EntryMinVA e) + (EntrySize e))"   
  
definition EntryMaxVA1 :: "TLBENTRY \<Rightarrow> genaddr" where
  "EntryMaxVA1 e = EntryMaxVA e"
 
  
text "The two entries must be consecutive"

lemma entry_va_consecutive :  "EntryMinVA1 e = Suc (EntryMaxVA0 e)"
  by(simp add:EntryMinVA1_def EntryMaxVA0_def EntryMinVA0_def EntrySize_positive)

    
text "The NullEntry has defined minimum and maximum VA."

lemma VPN2NullEntry : "vpn2 (hi null_entry) = 0"
  by(auto simp:null_entry_def TLBEntryReset_def TLBENTRY.make_def 
               TLBENTRYHI.make_def)

lemma EntrySizeNullEntry : "EntrySize null_entry = 4096"
  by(auto simp:EntrySize_def null_entry_def TLBEntryReset_def page_size_def 
               TLBENTRY.make_def KB_def)  
  
lemma MinVANullEntry : "EntryMinVA null_entry = 0"
  by(auto simp:EntryMinVA_def VPN2NullEntry) 
    
lemma MaxVANullEntry : "EntryMaxVA null_entry = 8191"
  by(auto simp:EntryMaxVA_def MinVANullEntry EntrySizeNullEntry)


(* ------------------------------------------------------------------------- *)      
subsection "TLB Entry ASID ranges"
(* ------------------------------------------------------------------------- *)      
    
definition EntryASIDRange :: "TLBENTRY \<Rightarrow> genaddr set"
  where "EntryASIDRange e = (if EntryIsGlobal e 
                             then {x. ASIDMin \<le> x \<and> x < ASIDMax} 
                             else {(asid (hi e))})"
    
(* ------------------------------------------------------------------------- *)      
subsection "TLB Entry genaddress ranges"
(* ------------------------------------------------------------------------- *)          

text "From the minimum and maximum genaddresses we can now define the range of
      genaddresses and entry spans i.e. the set of genaddresses"
  
definition EntryRange :: "TLBENTRY \<Rightarrow> genaddr set"
  where "EntryRange e =  {x.  (EntryMinVA e) \<le> x \<and> x \<le> (EntryMaxVA e)}"
  
definition EntryRange0 :: "TLBENTRY \<Rightarrow> genaddr set" 
  where "EntryRange0 e =  {x.  (EntryMinVA0 e) \<le> x \<and> x \<le> (EntryMaxVA0 e)}"  

definition EntryRange1 :: "TLBENTRY \<Rightarrow> genaddr set" 
  where "EntryRange1 e =  {x.  (EntryMinVA1 e) \<le> x \<and> x \<le> (EntryMaxVA1 e)}"
    
text "the range covered by the full entry must be the union of the two entries"
 
lemma entry_range_union:  "EntryRange e = (EntryRange0 e) \<union> (EntryRange1 e)"   
  by(auto simp:EntryRange_def EntryMaxVA_def EntryRange1_def EntryRange0_def
               EntryMinVA_def EntrySize_def EntryMinVA1_def EntryMinVA0_def
               EntryMaxVA0_def EntryMaxVA1_def)

lemma EntryRangeNullEntry : "EntryRange null_entry = {x.  0 \<le> x \<and> x \<le> 8191}"
  by(auto simp: EntryRange_def MinVANullEntry MaxVANullEntry)

text "A wellformed entry has a range with falls within the virtual genaddress space."
    
lemma TLBENTRYWellFormedEntryRangeValid :
  "TLBENTRYWellFormed e1 \<Longrightarrow>  \<forall> x \<in> EntryRange e1. x < VASize"
  apply(simp add: TLBENTRYWellFormed_def TLBENTRYHIWellFormed_def VPN2Valid_def
                  VPNMin_def VPN2Max_def page_count_def EntryRange_def 
                  EntryMinVA_def EntryMaxVA_def
                  page_size_def EntrySize_def)
  apply(cases "mask e1")
  apply(simp_all add:MB_def KB_def VASize_def)
  done
    
(* ------------------------------------------------------------------------- *)      
subsection "Extended Address Ranges"
(* ------------------------------------------------------------------------- *)      

  
text "The extended genaddress is the genaddress extended with the genaddress space identifier.
      we define the function to take a set of genaddresses and ASIDs and then expand any
      genaddress with all the ASIDs. "
  
definition mk_extended_range :: "nat set \<Rightarrow> nat set \<Rightarrow> nat set"
  where "mk_extended_range A R = 
            { (va + (VASize * asid)) | va asid. va \<in> R \<and> asid \<in> A }"

(* ------------------------------------------------------------------------- *)     
subsubsection "Singleton definitions"    
(* ------------------------------------------------------------------------- *) 
  
  
text "The following simplifications allow to replace the expression if either 
      of the two sets is a singleton set. "  
  
lemma mk_extended_range_singleton1:
  "mk_extended_range A {r} = {(r + (VASize * a)) |a. a \<in> A}"
  by(auto simp:mk_extended_range_def)
    
lemma mk_extended_range_singleton2:
  " mk_extended_range {a} R =  {(r + (VASize * a)) |r. r \<in> R}"  
  by(auto simp:mk_extended_range_def)
    
lemma mk_extended_range_singleton3:
  "mk_extended_range {a} {r} =  {(r + (VASize * a))}"  
  by(auto simp:mk_extended_range_def)

lemma "mk_extended_range X {} = {}"
  by(auto simp:mk_extended_range_def)
    
lemma "mk_extended_range {} X = {}"    
  by(auto simp:mk_extended_range_def)

lemma "mk_extended_range {} {} = {}"    
  by(auto simp:mk_extended_range_def)    
    
    
(* ------------------------------------------------------------------------- *)     
subsubsection "Extended Range Unions"    
(* ------------------------------------------------------------------------- *) 
  
  
lemma mk_extended_range_genaddr_union: 
  "mk_extended_range X (A \<union> B) = (mk_extended_range X A) \<union> (mk_extended_range X B)"
  by(auto simp:mk_extended_range_def)

lemma mk_extended_range_asid_union: 
  "mk_extended_range (A \<union> B) X = (mk_extended_range A X) \<union> (mk_extended_range B X)"
  by(auto simp:mk_extended_range_def)    

lemma mk_extended_rang_union: 
  "mk_extended_range (A \<union> B) (X \<union> Y) =
        (mk_extended_range A X) \<union> (mk_extended_range B X) 
             \<union>  (mk_extended_range A Y) \<union>  (mk_extended_range B Y)"
  by(auto simp:mk_extended_range_def)    
  

(* ------------------------------------------------------------------------- *)     
subsubsection "Extended Range Intersections"       
(* ------------------------------------------------------------------------- *) 
  
  
lemma mk_extended_range_genaddr_inter: 
 assumes spaceA:  "\<forall>a\<in>A . a < VASize" 
    and  spaceB:  "\<forall>b\<in>B . b < VASize" 
  shows "mk_extended_range X (A \<inter> B) = 
               (mk_extended_range X A) \<inter> (mk_extended_range X B)"
     (is "?X = ?Y")
proof(intro antisym subsetI)
  fix x
  assume "x \<in> ?X"
  then obtain asid va
    where "asid \<in> X" "va \<in> (A \<inter> B)"  "x = va + VASize * asid"
    by(auto simp:mk_extended_range_def)
   hence "asid \<in> X"  "va \<in> A" "va \<in> B" "x = va + VASize * asid"
    by(auto simp:mk_extended_range_def)
  thus "x \<in> ?Y" by(auto simp:mk_extended_range_def)
  next
    fix x
    assume "x \<in> ?Y" 
    then obtain asid1 asid2 va1 va2
     where A: "asid1 \<in> X" "asid2 \<in> X" "va1 \<in> A" "va2 \<in> B" and
           B: "x = va1 + VASize * asid1" and C: "x = va2 + VASize * asid2"
    by(auto simp:mk_extended_range_def) 
    from A spaceA have "va1 < VASize" by(auto)
    hence "va1 = va1 mod VASize" by(auto)
    also have "... = (va1 + VASize * asid1) mod VASize" by(auto)
    also from B C have "... = (va2 + VASize * asid2) mod VASize" by(simp)
    also have "... = va2 mod VASize" by(auto)
    also {
    from A spaceB have "va2 < VASize" by(auto)
    hence "va2 mod VASize = va2" by(auto)
  }
  finally have F: "va1 = va2" .
    have nz: "VASize \<noteq> 0" by(simp add:VASize_def)  
    with F B C nz have E: "asid1 = asid2" by(auto)
    with A B C F E show "x \<in> ?X"
      unfolding mk_extended_range_def by(auto)      
qed
  

lemma mk_extended_range_asid_inter:
  assumes space:  "\<forall>x \<in> X . x < VASize"
  shows   "mk_extended_range (A \<inter> B) X 
                    = (mk_extended_range A X) \<inter> (mk_extended_range B X)"
    (is "?X = ?Y")
proof(intro antisym subsetI)
  fix x
  assume "x \<in> ?X"
  then obtain asid va
  where "asid \<in> A \<inter> B" "va \<in> X" "x = va + VASize * asid"
    by(auto simp:mk_extended_range_def)
  hence "asid \<in> A" "asid \<in> B" "va \<in> X" "x = va + VASize * asid"
    by(auto)
  thus "x \<in> ?Y" by(auto simp:mk_extended_range_def)
next
  fix x
  assume "x \<in> ?Y"
  then obtain asid1 asid2 va1 va2
    where A: "asid1 \<in> A" "asid2 \<in> B" "va1 \<in> X" "va2 \<in> X" and
          B: "x = va1 + VASize * asid1" and C: "x = va2 + VASize * asid2"
    by(auto simp:mk_extended_range_def)
      
  from A space have "va1 < VASize" by(auto)
  hence "va1 = va1 mod VASize" by(auto)
  also have "... = (va1 + VASize * asid1) mod VASize" by(auto)
  also from B C have "... = (va2 + VASize * asid2) mod VASize" by(simp)
  also have "... = va2 mod VASize" by(auto)
  also {
    from A space have "va2 < VASize" by(auto)
    hence "va2 mod VASize = va2" by(auto)
  }
  finally have E: "va1 = va2" .
  have nz: "VASize \<noteq> 0" by(simp add:VASize_def)        
  with B C nz E have "asid1 = asid2" by(auto)
  with A have "asid1 \<in> A \<inter> B" by(simp)
  with A B show "x \<in> ?X"
    unfolding mk_extended_range_def by(auto)
qed

  
lemma mk_extended_range_inter: 
  assumes spaceC:  "\<forall>c\<in>C . c < VASize" 
      and spaceD:  "\<forall>d\<in>D . d < VASize"
    shows "mk_extended_range (A \<inter> B) (C \<inter> D)
                  = (mk_extended_range A C) \<inter> (mk_extended_range B D)"
      (is "?X = ?Y")
proof(intro antisym subsetI)
  fix x
  assume "x \<in> ?X"
  then obtain asid va
  where "asid \<in> A \<inter> B" "va \<in> (C \<inter> D)" "x = va + VASize * asid"
    by(auto simp:mk_extended_range_def)
  hence "asid \<in> A" "asid \<in> B" "va \<in> C" "va \<in> D" "x = va + VASize * asid"
    by(auto)
  thus "x \<in> ?Y" by(auto simp:mk_extended_range_def)
next
  fix x
  assume "x \<in> ?Y"
  then obtain asid1 asid2 va1 va2
    where A: "asid1 \<in> A" "asid2 \<in> B" "va1 \<in> C" "va2 \<in> D" and
          B: "x = va1 + VASize * asid1" and C: "x = va2 + VASize * asid2"
    by(auto simp:mk_extended_range_def)
      
  have nz: "VASize \<noteq> 0" by(simp add:VASize_def)           
  from A spaceC have "va1 < VASize" by(auto)
  hence "va1 = va1 mod VASize" by(auto)
  also have "... = (va1 + VASize * asid1) mod VASize" by(auto)
  also from B C have "... = (va2 + VASize * asid2) mod VASize" by(simp)
  also have "... = va2 mod VASize" by(auto)
  also {
    from A spaceD have "va2 < VASize" by(auto)
    hence "va2 mod VASize = va2" by(auto)
  }
  finally have F: "va1 = va2" .
  with B C nz have E: "asid1 = asid2" by(auto)
  with A have "asid2 \<in> A \<inter> B" by(simp)      
  with F A have "va1 \<in> C \<inter> D" by(simp)
  with A B C F E show "x \<in> ?X"
    unfolding mk_extended_range_def by(auto)
qed      
    
lemma mk_extended_range_inter2: 
  assumes spaceC:  "\<forall>c\<in>C . c < VASize" 
      and spaceD:  "\<forall>d\<in>D . d < VASize"
    shows "mk_extended_range (A \<inter> B) (C \<inter> D)
                 = (mk_extended_range B C) \<inter> (mk_extended_range A D)"
      (is "?X = ?Y")
proof(intro antisym subsetI)
  fix x
  assume "x \<in> ?X"
  then obtain asid va
  where "asid \<in> A \<inter> B" "va \<in> (C \<inter> D)" "x = va + VASize * asid"
    by(auto simp:mk_extended_range_def)
  hence "asid \<in> A" "asid \<in> B" "va \<in> C" "va \<in> D" "x = va + VASize * asid"
    by(auto)
  thus "x \<in> ?Y" by(auto simp:mk_extended_range_def)
next
  fix x
  assume "x \<in> ?Y"
  then obtain asid1 asid2 va1 va2
    where A: "asid1 \<in> A" "asid2 \<in> B" "va1 \<in> C" "va2 \<in> D" and
          B: "x = va1 + VASize * asid2" and C: "x = va2 + VASize * asid1"
    by(auto simp:mk_extended_range_def)
  have nz: "VASize \<noteq> 0" by(simp add:VASize_def)                 
  from A spaceC have "va1 < VASize" by(auto)
  hence "va1 = va1 mod VASize" by(auto)
  also have "... = (va1 + VASize * asid1) mod VASize" by(auto)
  also from B C have "... = (va2 + VASize * asid1) mod VASize" by(simp)
  also have "... = va2 mod VASize" by(auto)
  also {
    from A spaceD have "va2 < VASize" by(auto)
    hence "va2 mod VASize = va2" by(auto)
  }
  finally have F: "va1 = va2" .
  with B C nz have E: "asid1 = asid2" by(auto)
  with A have "asid2 \<in> A \<inter> B" by(simp)      
  with F A have "va1 \<in> C \<inter> D" by(simp)
  with A B C F E show "x \<in> ?X"
    unfolding mk_extended_range_def by(auto)
qed  
    
lemma mk_extended_range_inter3: 
  assumes spaceC:  "\<forall>c\<in>C . c < VASize" 
      and spaceD:  "\<forall>d\<in>D . d < VASize"
    shows "mk_extended_range (A \<inter> B) (C \<inter> D) 
                 = (mk_extended_range A D) \<inter> (mk_extended_range B C)"
      (is "?X = ?Y")
proof(intro antisym subsetI)
  fix x
  assume "x \<in> ?X"
  then obtain asid va
  where "asid \<in> A \<inter> B" "va \<in> (C \<inter> D)" "x = va + VASize * asid"
    by(auto simp:mk_extended_range_def)
  hence "asid \<in> A" "asid \<in> B" "va \<in> C" "va \<in> D" "x = va + VASize * asid"
    by(auto)
  thus "x \<in> ?Y" by(auto simp:mk_extended_range_def)
next
  fix x
  assume "x \<in> ?Y"
  then obtain asid1 asid2 va1 va2
    where A: "asid1 \<in> A" "asid2 \<in> B" "va1 \<in> C" "va2 \<in> D" and
          B: "x = va1 + VASize * asid2" and C: "x = va2 + VASize * asid1"
    by(auto simp:mk_extended_range_def)
  
  have nz: "VASize \<noteq> 0" by(simp add:VASize_def)                 
  from A spaceC have "va1 < VASize" by(auto)
  hence "va1 = va1 mod VASize" by(auto)
  also have "... = (va1 + VASize * asid1) mod VASize" by(auto)
  also from B C have "... = (va2 + VASize * asid1) mod VASize" by(simp)
  also have "... = va2 mod VASize" by(auto)
  also {
    from A spaceD have "va2 < VASize" by(auto)
    hence "va2 mod VASize = va2" by(auto)
  }
  finally have F: "va1 = va2" .
  with B C nz have E: "asid1 = asid2" by(auto)
  with A have "asid2 \<in> A \<inter> B" by(simp)      
  with F A have "va1 \<in> C \<inter> D" by(simp)
  with A B C F E show "x \<in> ?X"
    unfolding mk_extended_range_def by(auto)
qed   
  
    
lemma mk_extended_range_empty_genaddr_inter :
  assumes nempty : "X \<noteq> {}"
  shows  "(A \<inter> B = {}) = (mk_extended_range X (A \<inter> B) = {})"
proof 
  show "A \<inter> B = {} \<Longrightarrow> mk_extended_range X (A \<inter> B) = {}"
    by(simp add:mk_extended_range_def)
next
  show "mk_extended_range X (A \<inter> B) = {} \<Longrightarrow> A \<inter> B = {}"
  proof -
    have X0:  "mk_extended_range X (A \<inter> B) = {} \<Longrightarrow> X = {} \<or> (A \<inter> B) = {}"
      by(auto simp:mk_extended_range_def)
    
    with nempty show "mk_extended_range X (A \<inter> B) = {} \<Longrightarrow> (A \<inter> B) = {}"
      by(auto)
    qed
qed

lemma mk_extended_range_empty_asid_inter :
  assumes nempty : "X \<noteq> {}"
  shows  "(A \<inter> B = {}) = (mk_extended_range (A \<inter> B) X = {})"  
proof 
  show "A \<inter> B = {} \<Longrightarrow> mk_extended_range (A \<inter> B) X  = {}"
    by(simp add:mk_extended_range_def)
next
  show "mk_extended_range (A \<inter> B) X = {} \<Longrightarrow> A \<inter> B = {}"
  proof -
    have X0:  "mk_extended_range (A \<inter> B) X = {} \<Longrightarrow> X = {} \<or> (A \<inter> B) = {}"
      by(auto simp:mk_extended_range_def)
    
    with nempty show "mk_extended_range (A \<inter> B) X = {} \<Longrightarrow> (A \<inter> B) = {}"
      by(auto)
    qed
qed    
  

lemma mk_extended_range_empty_genaddr_inter2 :
  assumes spaceA:  "\<forall>a\<in>A . a < VASize" 
      and spaceB:  "\<forall>b\<in>B . b < VASize"
      and nz: "VASize \<noteq> 0"
    shows "A \<inter> B = {} \<Longrightarrow> (mk_extended_range Y A) \<inter> (mk_extended_range X B) = {}"
  apply(simp add:mk_extended_range_inter2[symmetric] spaceA spaceB nz)
  apply(simp add:mk_extended_range_def VASize_def spaceA spaceB)
  done        

   
(* ------------------------------------------------------------------------- *) 
subsection "TLB Entry Extended Address Ranges"    
(* ------------------------------------------------------------------------- *) 
  
    
definition EntryExtendedRange :: "TLBENTRY \<Rightarrow> genaddr set"
  where "EntryExtendedRange e =  (if (EntryIsGlobal e) then
                                    (mk_extended_range ASIDValidSet (EntryRange e))
                                  else  
                                    (mk_extended_range {asid (hi e)} (EntryRange e)))"
  
definition EntryExtendedRange0 :: "TLBENTRY \<Rightarrow> genaddr set" 
  where "EntryExtendedRange0 e =   (if (EntryIsGlobal e) then
                                     (mk_extended_range ASIDValidSet  (EntryRange0 e))
                                   else
                                     (mk_extended_range {asid (hi e)} (EntryRange0 e)))"  

definition EntryExtendedRange1 :: "TLBENTRY \<Rightarrow> genaddr set" 
  where "EntryExtendedRange1 e =   (if (EntryIsGlobal e) then
                                      (mk_extended_range ASIDValidSet (EntryRange1 e))
                                   else
                                       (mk_extended_range {asid (hi e)} (EntryRange1 e)))"  

(* ------------------------------------------------------------------------- *) 
subsection "Extended Range Union"    
(* ------------------------------------------------------------------------- *)     
    
lemma entry_extended_range_union:  
  "EntryExtendedRange e = (EntryExtendedRange0 e) \<union> (EntryExtendedRange1 e)"   
  by(simp add:EntryExtendedRange_def EntryExtendedRange0_def EntryExtendedRange1_def 
              mk_extended_range_genaddr_union[symmetric] entry_range_union)

            
(* ------------------------------------------------------------------------- *) 
subsection "Extended Range Intersection"    
(* ------------------------------------------------------------------------- *)       

lemma entry_mk_extended_range_inter :
  assumes wfe1: "TLBENTRYWellFormed e1"
      and wfe2: "TLBENTRYWellFormed e2"
      and nz: "VASize \<noteq> 0"
    shows "EntryRange e1 \<inter> EntryRange e2 = {} \<Longrightarrow> 
           mk_extended_range X (EntryRange e1) \<inter> mk_extended_range X (EntryRange e2) = {}"
proof -
  fix x1 x2
  assume empty: "EntryRange e1 \<inter> EntryRange e2 = {}"
  from wfe1 have space1:  "\<forall>x1\<in>EntryRange e1 . x1 < VASize"
    by(simp add :TLBENTRYWellFormedEntryRangeValid)
  also from wfe2 have space2: "\<forall>x2\<in>EntryRange e2 . x2 < VASize"
    by(simp add :TLBENTRYWellFormedEntryRangeValid)
  with space1 have X0:  "mk_extended_range X (EntryRange e1) \<inter> mk_extended_range X (EntryRange e2) = 
                        mk_extended_range X ((EntryRange e1) \<inter> (EntryRange e2))"
    by(simp add:mk_extended_range_genaddr_inter[symmetric] space1 space2 nz)
  
  hence X1: "mk_extended_range X (EntryRange e1 \<inter> EntryRange e2)  = mk_extended_range X {}"
     by(simp add:empty)

   thus ?thesis 
     apply(simp add:X0 X1) 
     apply(simp add:mk_extended_range_def)
     done        
qed
    
lemma entry_extended_range_intersect:
  assumes wfe1: "TLBENTRYWellFormed e1"
      and wfe2: "TLBENTRYWellFormed e2"
      and nz: "VASize \<noteq> 0"
  shows "(EntryRange e1 \<inter> EntryRange e2) = {} \<Longrightarrow> (EntryExtendedRange e1 \<inter> EntryExtendedRange e2) = {}"
proof cases
  assume e1g: "EntryIsGlobal e1" and empty: "EntryRange e1 \<inter> EntryRange e2 = {}"
  show ?thesis
  proof cases
    assume e2g: "EntryIsGlobal e2"
    show ?thesis 
      by(simp add:EntryExtendedRange_def e1g e2g 
                  entry_mk_extended_range_inter empty wfe1 wfe2 nz)
  next
    assume ne2g: "\<not>(EntryIsGlobal e2)"
    show ?thesis
    proof - 
      fix x1 x2
      from wfe1 have space1:  "\<forall>x1\<in>EntryRange e1 . x1 < VASize"
        by(simp add :TLBENTRYWellFormedEntryRangeValid)
      also from wfe2 have space2: "\<forall>x2\<in>EntryRange e2 . x2 < VASize"
        by(simp add :TLBENTRYWellFormedEntryRangeValid)
      with e1g ne2g have X0: "(EntryExtendedRange e1 \<inter> EntryExtendedRange e2) = 
              mk_extended_range ASIDValidSet (EntryRange e1) 
                   \<inter> mk_extended_range {asid (hi e2)} (EntryRange e2)"
        by(simp add:EntryExtendedRange_def)
      with space1 space2 empty nz show ?thesis 
         by(auto simp add:mk_extended_range_empty_genaddr_inter2)      
     qed
  qed              
next
  assume ne1g: "\<not>(EntryIsGlobal e1)" and  empty: "EntryRange e1 \<inter> EntryRange e2 = {}"    
  show ?thesis
  proof cases
    assume e2g: "EntryIsGlobal e2"
    show ?thesis 
      proof - 
      fix x1 x2
      from wfe1 have space1:  "\<forall>x1\<in>EntryRange e1 . x1 < VASize"
        by(simp add :TLBENTRYWellFormedEntryRangeValid)
      also from wfe2 have space2: "\<forall>x2\<in>EntryRange e2 . x2 < VASize"
        by(simp add :TLBENTRYWellFormedEntryRangeValid)
      with ne1g e2g have X0: "(EntryExtendedRange e1 \<inter> EntryExtendedRange e2) = 
              mk_extended_range {asid (hi e1)} (EntryRange e1) 
                  \<inter> mk_extended_range ASIDValidSet  (EntryRange e2)"
        by(simp add:EntryExtendedRange_def)
      with space1 space2 empty nz show ?thesis 
         by(auto simp add:mk_extended_range_empty_genaddr_inter2)      
     qed
  next
    assume ne2g: "\<not>(EntryIsGlobal e2)"
    show ?thesis 
      proof - 
      fix x1 x2
      from wfe1 have space1:  "\<forall>x1\<in>EntryRange e1 . x1 < VASize"
        by(simp add :TLBENTRYWellFormedEntryRangeValid)
      also from wfe2 have space2: "\<forall>x2\<in>EntryRange e2 . x2 < VASize"
        by(simp add :TLBENTRYWellFormedEntryRangeValid)
      with ne1g ne2g have X0: "(EntryExtendedRange e1 \<inter> EntryExtendedRange e2) = 
              mk_extended_range {asid (hi e1)} (EntryRange e1)
                   \<inter> mk_extended_range {asid (hi e2)}  (EntryRange e2)"
        by(simp add:EntryExtendedRange_def)
      with space1 space2 empty nz show ?thesis 
         by(auto simp add:mk_extended_range_empty_genaddr_inter2)      
     qed
  qed              
qed      
  

(* ------------------------------------------------------------------------- *) 
subsection "TLB Entry Physical Addresses"
(* ------------------------------------------------------------------------- *)  
    
text "The TLB entry pair maps to two physical regions, we need to multiply the PFN
      with the actual frame size to get the genaddress"  
  
definition EntryPA0 :: "TLBENTRY \<Rightarrow> genaddr" 
  where "EntryPA0 e = (pfn (lo0 e)) * (EntrySize e)"
 
definition EntryPA1 :: "TLBENTRY \<Rightarrow> genaddr" 
  where "EntryPA1 e = (pfn (lo1 e)) * (EntrySize e)"

    
(* ------------------------------------------------------------------------- *)     
subsection "Queries whether the entry is VALID or not"
(* ------------------------------------------------------------------------- *)  

text "A TLB entry is valid if the corresponding valid bit has been set. Thus
      the entry pair is considered valid if either of the two entries is valid."  
  
definition EntryIsValid0 :: "TLBENTRY \<Rightarrow> bool"
  where "EntryIsValid0 e = (v (lo0 e))"

definition EntryIsValid1 :: "TLBENTRY \<Rightarrow> bool"
  where "EntryIsValid1 e = (v (lo1 e))"    
    
definition EntryIsValid :: "TLBENTRY \<Rightarrow> bool"
  where "EntryIsValid e = ((EntryIsValid0 e) \<or> (EntryIsValid1 e))"
    

lemma TLBEntryResetNotValid_id :
  "\<not>EntryIsValid(TLBEntryReset idx)"
  by(simp add:TLBEntryReset_def TLBENTRY.make_def
                 null_entry_lo_def EntryIsValid_def 
                 EntryIsValid0_def EntryIsValid1_def)    
    

(* ------------------------------------------------------------------------- *)       
subsection "Queries whether the entry matches with the ASID"
(* ------------------------------------------------------------------------- *)   
  
text "An ASID matches the entry, if the ASID matches or the entry is global.
      Comparing two entries, either the ASID matches or one of them is global."
  
definition EntryASIDMatchA :: "ASID \<Rightarrow> TLBENTRY \<Rightarrow> bool"
  where "EntryASIDMatchA a e = (((asid (hi e)) = a) \<or>  (EntryIsGlobal e))"

definition EntryASIDMatch :: "TLBENTRY \<Rightarrow> TLBENTRY \<Rightarrow> bool"
  where "EntryASIDMatch e1 e2 = ((((asid (hi e1)) = (asid (hi e2)))
                                  \<or> (EntryIsGlobal e1)) 
                                  \<or> (EntryIsGlobal e2))"


lemma EntryASIDMatch_true :
  "EntryASIDMatch e e = True"
  by(simp add:EntryASIDMatch_def)    

lemma EntryASIDMatch_commute :
  "\<forall> e f. EntryASIDMatch e f = EntryASIDMatch f e"
  by(auto simp add:EntryASIDMatch_def)    

lemma  "ASIDValid a \<Longrightarrow> a \<in> ASIDValidSet"
  by(simp add: ASIDValid_def ASIDValidSet_def)

lemma  "ASIDValid a \<Longrightarrow> {a} \<inter> ASIDValidSet = {a}"
  by(simp add: ASIDValid_def ASIDValidSet_def)    

lemma TLBEntryResetASID_match :
  "\<And>i j. EntryASIDMatch (TLBEntryReset i) (TLBEntryReset j)"
  by(auto simp:EntryASIDMatch_def TLBEntryResetASID_is)     
    
(* ------------------------------------------------------------------------- *)        
subsection "VPN Match"  
(* ------------------------------------------------------------------------- *)   

text "The VPN matches if their respective virtual genaddresses fall within the
      ranges. "   
  
definition EntryMax4KVPN :: "TLBENTRY \<Rightarrow> VPN"
  where "EntryMax4KVPN e = (num_4k_pages (mask e) * (vpn2 (hi e) + 2)) - 1"
    
definition EntryMin4KVPN :: "TLBENTRY \<Rightarrow> VPN"
  where "EntryMin4KVPN e = num_4k_pages (mask e) * (vpn2 (hi e))"

definition EntryMin4KVPN1 :: "TLBENTRY \<Rightarrow> VPN"
  where "EntryMin4KVPN1 e = num_4k_pages (mask e) * ((vpn2 (hi e)) + 1)"    
    
definition EntryVPNMatchV :: "VPN \<Rightarrow> TLBENTRY \<Rightarrow> bool"
  where "EntryVPNMatchV vpn e = ((EntryMin4KVPN e) \<le> vpn \<and> vpn \<le> EntryMax4KVPN e)"

definition EntryVPNMatchV0 :: "VPN \<Rightarrow> TLBENTRY \<Rightarrow> bool"
  where "EntryVPNMatchV0 vpn e = ((EntryMin4KVPN e) \<le> vpn \<and> vpn < EntryMin4KVPN1 e)"

definition EntryVPNMatchV1 :: "VPN \<Rightarrow> TLBENTRY \<Rightarrow> bool"
  where "EntryVPNMatchV1 vpn e = ((EntryMin4KVPN1 e) \<le> vpn \<and> vpn \<le> EntryMax4KVPN e)"
        
definition EntryVPNMatch ::  "TLBENTRY \<Rightarrow> TLBENTRY \<Rightarrow> bool"
  where "EntryVPNMatch e1 e2 = (((EntryRange e1) \<inter> (EntryRange e2)) \<noteq> {})"

lemma EntryVPNMatch_commute :
 "\<forall>e f. EntryVPNMatch e f = EntryVPNMatch f e"
 by(simp add:EntryVPNMatch_def Int_commute)
   
lemma  EntryVPNMatch_true :
  " EntryVPNMatch e e = True"
  apply(cases "(mask e)")
  apply(simp_all add: EntryVPNMatch_def EntryRange_def EntryMinVA_def
                      page_size_def EntryMaxVA_def EntrySize_def KB_def MB_def)
  apply(auto)
  done     
    
lemma EntryVPNMatchV_true:
  assumes size : "(mask e) = MASK4K"
  shows  "EntryVPNMatchV (vpn2 (hi e)) e = True"
  by(simp add:EntryVPNMatchV_def  EntryMax4KVPN_def EntryMin4KVPN_def size)
  

lemma TLBEntryResetVPN_match :
  "\<And>i j. i = j \<longleftrightarrow> EntryVPNMatch (TLBEntryReset i) (TLBEntryReset j)"
  by(auto simp:EntryVPNMatch_def EntryRange_def EntryMinVA_def
               TLBEntryResetVPN2_is TLBEntryResetMask_is EntryMaxVA_def
               EntrySize_def KB_def) 

             
lemma EntryVPNMatch_is_vpn2match :
  assumes size1: "(mask e1) = MASK4K"
    and size2: "mask e2 = MASK4K"
    and even1: "(even (vpn2 (hi e1)))"
    and even2: "(even (vpn2 (hi e2)))"
  shows "EntryVPNMatch e1 e2 = ((vpn2 (hi e1)) = (vpn2 (hi e2)))"
proof
  assume match: "EntryVPNMatch e1 e2"
  show "vpn2 (hi e1) = vpn2 (hi e2)"
  proof -
    from match size1 size2 have X0:
      "({x. vpn2 (hi e1) * 4096 \<le> x \<and> x \<le> 8191 + vpn2 (hi e1) * 4096} 
      \<inter> {x. vpn2 (hi e2) * 4096 \<le> x \<and> x \<le> 8191 + vpn2 (hi e2) * 4096} \<noteq> {})"
      by(simp add:EntryVPNMatch_def EntryRange_def EntryMinVA_def EntryMaxVA_def 
                  EntrySize_def KB_def)
        
    from X0 have X1 : 
      "({x. (vpn2 (hi e1) * 4096 \<le> x) \<and> (vpn2 (hi e2) * 4096 \<le> x) 
            \<and> (x < 8192 + vpn2 (hi e1) * 4096) 
            \<and>  (x \<le> 8191 + vpn2 (hi e2) * 4096)} \<noteq> {})"
      by(auto)
        
    from X1 have X2: 
      "({x. (vpn2 (hi e1) * 4096 \<le> x) \<and> (vpn2 (hi e2) * 4096 \<le> x) 
          \<and> (x < (2 + vpn2 (hi e1)) * 4096) \<and>  (x < ( 2 + vpn2 (hi e2)) * 4096)} \<noteq> {})"
      by(auto)        


    from X2 have X3: 
      "({x. (vpn2 (hi e2) * 4096 \<le> x) \<and> (x < (2 + vpn2 (hi e1)) * 4096)} \<noteq> {})"
      by(auto)
    
    from X2 have X4: 
      "({x. (vpn2 (hi e1) * 4096 \<le> x) \<and>  (x < ( 2 + vpn2 (hi e2)) * 4096)} \<noteq> {})"
      by(auto)        
    
    from even1 even2 have X5 : "vpn2 (hi e2) \<noteq> Suc (vpn2 (hi e1))"        
      by(auto)
    from even1 even2 have X12 : "vpn2 (hi e1) \<noteq> Suc (vpn2 (hi e2))"        
      by(auto)          
        
    from X3 have X6: "vpn2 (hi e2) < 2 + vpn2 (hi e1)"
      by(auto)
    from X6 have X7:  "vpn2 (hi e2) \<le> Suc (vpn2 (hi e1))"
      by(auto)
    from even1 even2 X5 X7 have X9: "vpn2 (hi e2) \<le> (vpn2 (hi e1))"
      by(auto)
        
    from X4 have X10: "vpn2 (hi e1) < 2 + vpn2 (hi e2)"
      by(auto)
    from X10 have X11:  "vpn2 (hi e1) \<le> Suc (vpn2 (hi e2))"
      by(auto)
    
    from even1 even2 X12 X11 have X12: "vpn2 (hi e1) \<le> (vpn2 (hi e2))"
      by(auto)        
        
    from X12 X9 show ?thesis 
      by(auto)
  qed
next
  assume eq: "vpn2 (hi e1) = vpn2 (hi e2)"
  show "EntryVPNMatch e1 e2 "
  proof -
    from size1 size2 even1 even2 have X0:
      "EntryVPNMatch e1 e2 = ({x. vpn2 (hi e1) * 4096 \<le> x \<and> x \<le> 8191 + vpn2 (hi e1) * 4096}
           \<inter> {x. vpn2 (hi e2) * 4096 \<le> x \<and> x \<le> 8191 + vpn2 (hi e2) * 4096} \<noteq> {})"
      by(simp add:EntryVPNMatch_def EntryRange_def EntryMinVA_def EntryMaxVA_def 
                  EntrySize_def KB_def)
    from eq have X1: "... = ({x. vpn2 (hi e1) * 4096 \<le> x \<and> x \<le> 8191 + vpn2 (hi e1) * 4096} 
          \<inter> {x. vpn2 (hi e1) * 4096 \<le> x \<and> x \<le> 8191 + vpn2 (hi e1) * 4096} \<noteq> {})"
      by(auto)
    have X2 : "... = ({x. vpn2 (hi e1) * 4096 \<le> x \<and> x \<le> 8191 + vpn2 (hi e1) * 4096} \<noteq> {})"
      by(auto)
    from X0 X1 X2 show ?thesis 
      by(auto)
  qed
qed
             
lemma EntryVPNMatch_alter :
assumes size1: "(mask e1) = MASK4K"
    and size2: "mask e2 = MASK4K"
    and even1: "(even (vpn2 (hi e1)))"
    and even2: "(even (vpn2 (hi e2)))"
  shows "EntryVPNMatch e1 e2 = EntryVPNMatchV (vpn2 (hi e1)) e2"
proof cases
  assume eq: "e1 = e2"
  then show ?thesis 
  proof -
    from eq have X0: "EntryVPNMatch e1 e2" 
      by(simp add:EntryVPNMatch_true)
    from eq size1 have X1: "EntryVPNMatchV (vpn2 (hi e1)) e2"
      by(simp add:EntryVPNMatchV_true)
    from X0 X1 show ?thesis 
      by(auto)
  qed
next
  assume neq: "e1 \<noteq> e2"
  then show ?thesis 
  proof cases
    assume match: "EntryVPNMatch e1 e2"
    then show ?thesis 
    proof -
      from match size1 size2 even1 even2 have X0: 
        "(vpn2 (hi e1)) = (vpn2 (hi e2))"
        by(simp add:EntryVPNMatch_is_vpn2match)  
      
      from match size1 size2 X0 show ?thesis
        by(simp add:EntryVPNMatchV_def EntryMin4KVPN_def EntryMax4KVPN_def)
    qed      
  next
    assume nomatch: "\<not>EntryVPNMatch e1 e2"
    then show ?thesis
    proof -
      from nomatch size1 size2 even1 even2 have X0: 
        "(vpn2 (hi e1)) \<noteq>  (vpn2 (hi e2))"
        by(simp add:EntryVPNMatch_is_vpn2match)  
       
      from  size1 size2  have X1:
        "EntryVPNMatchV (vpn2 (hi e1)) e2 =
        (vpn2 (hi e2) \<le> vpn2 (hi e1) \<and> vpn2 (hi e1) \<le> Suc (vpn2 (hi e2)))"
        by(simp add:EntryVPNMatchV_def EntryMin4KVPN_def EntryMax4KVPN_def)

      from X0 even1 even2 have X2:
        "... = (vpn2 (hi e2) < vpn2 (hi e1) \<and> vpn2 (hi e1) \<le> Suc (vpn2 (hi e2)))"
        by(auto)

      from even1 even2 have X3 :
        "vpn2 (hi e1) \<noteq> Suc (vpn2 (hi e2))"
        by(auto)
          
      from X0 X3 even1 even2 have X3:
        "... = (vpn2 (hi e2) < vpn2 (hi e1) \<and> vpn2 (hi e1) < Suc (vpn2 (hi e2)))"
        by(auto)
      
      from nomatch neq X0 X1 X2 X3 size1 size2 even1 even2 show ?thesis
        by(auto)
    qed
  qed
qed
  

  
(* ------------------------------------------------------------------------- *)     
subsection "Matching Entry"
(* ------------------------------------------------------------------------- *)   

definition EntryMatchVPNASID :: "VPN \<Rightarrow> ASID \<Rightarrow> TLBENTRY \<Rightarrow> bool" 
  where "EntryMatchVPNASID vpn a e = ((EntryVPNMatchV vpn e) \<and> (EntryASIDMatchA a e))"

definition EntryMatchVPNASID0 :: "VPN \<Rightarrow> ASID \<Rightarrow> TLBENTRY \<Rightarrow> bool" 
  where "EntryMatchVPNASID0 vpn a e = ((EntryVPNMatchV0 vpn e) \<and> (EntryASIDMatchA a e))"

definition EntryMatchVPNASID1 :: "VPN \<Rightarrow> ASID \<Rightarrow> TLBENTRY \<Rightarrow> bool" 
  where "EntryMatchVPNASID1 vpn a e = ((EntryVPNMatchV1 vpn e) \<and> (EntryASIDMatchA a e))"    
    
    
text "From the definition, the two entry match if their VPNs and ASIDs match."    
  
definition EntryMatch :: "TLBENTRY \<Rightarrow> TLBENTRY \<Rightarrow> bool" where
  "EntryMatch e1 e2 = ((EntryVPNMatch e1 e2) \<and> (EntryASIDMatch e1 e2))"


text "The Extended Range match already includes the ASID so if they intersect the
     the two entry match."  
  
definition EntryMatchER :: "TLBENTRY \<Rightarrow> TLBENTRY \<Rightarrow> bool" where
  "EntryMatchER e1 e2 = ((EntryExtendedRange e1) \<inter> (EntryExtendedRange e2) \<noteq> {})"  

text "We show that the EntryMatchER is equal to the definition of a match in the
      specifictaion"

lemma EntryMatchEqualsEntryMatchER :
  assumes wfe1: "TLBENTRYWellFormed e1"
      and wfe2: "TLBENTRYWellFormed e2"
      and nz: "VASize \<noteq> 0"
    shows "(EntryMatch e1 e2) = (EntryMatchER e1 e2)"
proof cases
  assume e1g: "EntryIsGlobal e1"
  show ?thesis
  proof cases
    assume e2g: "EntryIsGlobal e2"
    show ?thesis 
    proof -
      from wfe1 have space1:  "\<forall>x1\<in>EntryRange e1 . x1 < VASize"
        by(simp add :TLBENTRYWellFormedEntryRangeValid)
      also from wfe2 have space2: "\<forall>x2\<in>EntryRange e2 . x2 < VASize"
        by(simp add :TLBENTRYWellFormedEntryRangeValid)
      have nemtpy: "ASIDValidSet \<noteq> {}" 
        by(simp add:ASIDValidSet_notempty)
      have X0: "EntryMatch e1 e2 = (EntryRange e1 \<inter> EntryRange e2 \<noteq> {})" 
        by(simp add:EntryMatch_def EntryVPNMatch_def EntryASIDMatch_def e1g)
      have X1: "EntryMatchER e1 e2 = (mk_extended_range ASIDValidSet (EntryRange e1) 
            \<inter> mk_extended_range ASIDValidSet (EntryRange e2) \<noteq> {})"
        by(simp add:EntryMatchER_def EntryExtendedRange_def e1g e2g)
      hence  X2: "... = (mk_extended_range ASIDValidSet (EntryRange e1 \<inter> EntryRange e2) \<noteq> {})"
        by(simp add:mk_extended_range_genaddr_inter nz space1 space2)
      with X0 X1 show ?thesis by(simp add:X0 X1 X2 nemtpy mk_extended_range_empty_genaddr_inter)
    qed
  next
    assume ne2g: "\<not>(EntryIsGlobal e2)"
    show ?thesis 
    proof -
      from wfe1 have space1:  "\<forall>x1\<in>EntryRange e1 . x1 < VASize"
        by(simp add :TLBENTRYWellFormedEntryRangeValid)
      also from wfe2 have space2: "\<forall>x2\<in>EntryRange e2 . x2 < VASize"
        by(simp add :TLBENTRYWellFormedEntryRangeValid)
      from wfe2 have asidvalid : "ASIDValid (asid (hi e2))" by(simp add:TLBENTRYWellFormedASIDValid)
      from asidvalid have asidset: "ASIDValidSet \<inter> { (asid (hi e2))} = { (asid (hi e2))} "
         by(simp add: ASIDValid_def ASIDValidSet_def)    
      have X0: "EntryMatch e1 e2 = (EntryRange e1 \<inter> EntryRange e2 \<noteq> {})" 
        by(simp add:EntryMatch_def EntryVPNMatch_def EntryASIDMatch_def e1g)
      have X1: "EntryMatchER e1 e2 = (mk_extended_range ASIDValidSet (EntryRange e1) \<inter> mk_extended_range  {asid (hi e2)} (EntryRange e2) \<noteq> {})"
        by(simp add:EntryMatchER_def EntryExtendedRange_def e1g ne2g)
      have X2: "... = (mk_extended_range (ASIDValidSet \<inter> { (asid (hi e2))}) (EntryRange e1 \<inter> EntryRange e2) \<noteq> {})"
        by(simp add:mk_extended_range_inter space1 space2 nz) 
      from asidset have X3: "... = (mk_extended_range {asid (hi e2)} (EntryRange e1 \<inter> EntryRange e2) \<noteq> {})"
        by(auto)
      with X0 X1 show ?thesis by(simp add:X0 X1 X2 X3 mk_extended_range_empty_genaddr_inter)
    qed
  qed              
next
  assume ne1g: "\<not>(EntryIsGlobal e1)"    
  show ?thesis
  proof cases
    assume e2g: "EntryIsGlobal e2"
    show ?thesis
   proof -
      from wfe1 have space1:  "\<forall>x1\<in>EntryRange e1 . x1 < VASize"
        by(simp add :TLBENTRYWellFormedEntryRangeValid)
      also from wfe2 have space2: "\<forall>x2\<in>EntryRange e2 . x2 < VASize"
        by(simp add :TLBENTRYWellFormedEntryRangeValid)
      from wfe1 have asidvalid : "ASIDValid (asid (hi e1))" by(simp add:TLBENTRYWellFormedASIDValid)
      from asidvalid have asidset: "{ (asid (hi e1))} \<inter> ASIDValidSet = { (asid (hi e1))} "
         by(simp add: ASIDValid_def ASIDValidSet_def)    
      have X0: "EntryMatch e1 e2 = (EntryRange e1 \<inter> EntryRange e2 \<noteq> {})" 
        by(simp add:EntryMatch_def EntryVPNMatch_def EntryASIDMatch_def e2g)
      have X1: "EntryMatchER e1 e2 = (mk_extended_range  {asid (hi e1)} (EntryRange e1) \<inter> mk_extended_range  ASIDValidSet (EntryRange e2) \<noteq> {})"
        by(simp add:EntryMatchER_def EntryExtendedRange_def ne1g e2g)
      have X2: "... = (mk_extended_range ({ (asid (hi e1))} \<inter> ASIDValidSet) (EntryRange e1 \<inter> EntryRange e2) \<noteq> {})"
        by(simp add:mk_extended_range_inter space1 space2 nz) 
      from asidset have X3: "... = (mk_extended_range {asid (hi e1)} (EntryRange e1 \<inter> EntryRange e2) \<noteq> {})"
        by(auto)
      with X0 X1 show ?thesis by(simp add:X0 X1 X2 X3 mk_extended_range_empty_genaddr_inter)
    qed      
  next
    assume ne2g: "\<not>(EntryIsGlobal e2)"
    show ?thesis   
      proof -
      from wfe1 have space1:  "\<forall>x1\<in>EntryRange e1 . x1 < VASize"
        by(simp add :TLBENTRYWellFormedEntryRangeValid)
      also from wfe2 have space2: "\<forall>x2\<in>EntryRange e2 . x2 < VASize"
        by(simp add :TLBENTRYWellFormedEntryRangeValid)
      from wfe1 have asidvalid1 : "ASIDValid (asid (hi e1))" by(simp add:TLBENTRYWellFormedASIDValid)
      from wfe2 have asidvalid1 : "ASIDValid (asid (hi e2))" by(simp add:TLBENTRYWellFormedASIDValid)          
      have X1: "EntryMatchER e1 e2 = (mk_extended_range {asid (hi e1)} (EntryRange e1) \<inter> mk_extended_range  {asid (hi e2)} (EntryRange e2) \<noteq> {})"
        by(simp add:EntryMatchER_def EntryExtendedRange_def ne1g ne2g)
      hence X2: "... = (mk_extended_range ({ (asid (hi e1))} \<inter> {(asid (hi e2))}) (EntryRange e1 \<inter> EntryRange e2) \<noteq> {})"
        by(simp add:mk_extended_range_inter space1 space2 nz) 
      with X1 X2 show ?thesis
      proof cases
        assume eq:  "(asid (hi e1)) =  (asid (hi e2))"
        show ?thesis
          proof -
            from X2 eq have X3: "(mk_extended_range ({ (asid (hi e1))} \<inter> {(asid (hi e2))}) (EntryRange e1 \<inter> EntryRange e2) \<noteq> {}) =
                              (mk_extended_range ({(asid (hi e2))}) (EntryRange e1 \<inter> EntryRange e2) \<noteq> {})"
              by(auto)
            from eq have asidmatch: "EntryASIDMatch e1 e2" by(simp add:EntryASIDMatch_def)
            have X0: "EntryMatch e1 e2 = (EntryRange e1 \<inter> EntryRange e2 \<noteq> {})"
              by(simp add:EntryMatch_def asidmatch EntryVPNMatch_def)
            with X1 X2 X3 X0 show ?thesis 
              by(simp add:X1 X2 X3 X0 mk_extended_range_empty_genaddr_inter)
          qed
        next
        assume eq:  "(asid (hi e1)) \<noteq>  (asid (hi e2))"
        show ?thesis 
                    proof -
            from X2 eq have X3: "(mk_extended_range ({ (asid (hi e1))} \<inter> {(asid (hi e2))}) (EntryRange e1 \<inter> EntryRange e2) \<noteq> {}) =
                              (mk_extended_range {} (EntryRange e1 \<inter> EntryRange e2) \<noteq> {})"
              by(auto)
            from eq have nasidmatch: "\<not>EntryASIDMatch e1 e2" by(simp add:EntryASIDMatch_def ne2g ne1g)
            have X0: "EntryMatch e1 e2 =  False"
              by(simp add:EntryMatch_def nasidmatch)
            with X1 X2 X3 X0 show ?thesis 
              by(auto simp:mk_extended_range_def X1 X2 X3 X0 mk_extended_range_empty_genaddr_inter)
          qed
        qed
    qed  
  qed              
qed      

  

lemma EntryMatch_true :
  "\<forall>e. EntryMatch e e = True"
  by(simp add:EntryMatch_def EntryVPNMatch_true EntryASIDMatch_true)
   
lemma EntryMatch_commute :
  "\<forall>e f. EntryMatch e f = EntryMatch f e"
  by(simp add:EntryMatch_def EntryVPNMatch_commute EntryASIDMatch_commute)

lemma EntryVPNMatchV_equals_odd :
  assumes vodd : "odd vpn"
    and  vpn2even:  "even (vpn2 (hi (e)))"
    and  mask4k:   "(mask (e)) = MASK4K"
  shows "EntryVPNMatchV vpn (e) = EntryVPNMatchV (vpn - 1) (e)"
proof 
  assume match: "EntryVPNMatchV vpn (e)"
  show " EntryVPNMatchV (vpn - 1) (e)" 
  proof - 
         
  from match have X0:
    "(vpn2 (hi (e)) \<le> vpn)"
    by(simp add:EntryVPNMatchV_def EntryMin4KVPN_def EntryMax4KVPN_def 
                num_4k_pages_def mask4k)
  
  from match have X1:
    "vpn \<le> Suc (vpn2 (hi (e)))"
    by(simp add:EntryVPNMatchV_def EntryMin4KVPN_def EntryMax4KVPN_def 
                num_4k_pages_def mask4k)      
      
  from vpn2even X0 vodd have X2: 
    "(vpn2 (hi (e)) \<le> (vpn - 1))"
  proof -
    from vpn2even vodd have Y0: "(vpn2 (hi (e))) \<noteq> vpn"
      by(auto)
    from X0 vpn2even vodd Y0 show ?thesis 
      by(auto)
  qed
      
  from X1 have X3:
    "vpn - 1 \<le> Suc (vpn2 (hi (e)))" 
    by(auto)
  
  have X4: "EntryVPNMatchV (vpn - 1) (e) = 
     (vpn2 (hi (e)) \<le> vpn - 1 \<and> vpn - 1 \<le> Suc (vpn2 (hi (e))))"
    by(simp add:EntryVPNMatchV_def EntryMin4KVPN_def EntryMax4KVPN_def 
                num_4k_pages_def mask4k) 
  
    from X2 X3 X4 show ?thesis 
      by(auto)
  qed
next
  assume match2: "EntryVPNMatchV (vpn - 1) (e) "
  show "EntryVPNMatchV vpn (e)" 
  proof -
      
  from match2 have X0:
    "(vpn2 (hi (e)) \<le> (vpn - 1))"
    by(simp add:EntryVPNMatchV_def EntryMin4KVPN_def EntryMax4KVPN_def 
                num_4k_pages_def mask4k)
  
  from match2 have X1:
    "(vpn - 1) \<le> Suc (vpn2 (hi (e)))"
    by(simp add:EntryVPNMatchV_def EntryMin4KVPN_def EntryMax4KVPN_def 
                num_4k_pages_def mask4k)      
      
  from vpn2even X0 vodd have X2: 
    "(vpn2 (hi (e)) \<le> vpn)"
    by(auto)
      
  from X1 vpn2even vodd have X3:
    "vpn  \<le> Suc (vpn2 (hi (e)))"
  proof -
    from vpn2even have Y0:
      "odd (Suc (vpn2 (hi (e))))"
      by(auto)
    from vodd have Y1:
      "even (vpn - 1)"
      by(auto)
         
    from Y1 Y0  have Y2:
      "vpn \<noteq> (Suc (Suc (vpn2 (hi (e)))))"
      by(auto)
        
    from X1 vpn2even vodd Y0 Y2 show ?thesis 
      by(auto)
  qed
      
  have X4: "EntryVPNMatchV vpn e = 
    (vpn2 (hi (e)) \<le> vpn  \<and> vpn  \<le> Suc (vpn2 (hi (e))))"
    by(simp add:EntryVPNMatchV_def EntryMin4KVPN_def EntryMax4KVPN_def
                num_4k_pages_def mask4k) 
  
    from X2 X3 X4 show ?thesis 
      by(auto)
  qed
qed
  
lemma EntryMatch_equals_odd :
  assumes eodd: "odd vpn"
    and  vpn2even:  "even (vpn2 (hi (e)))"
    and  mask4k:   "(mask (e)) = MASK4K"
  shows "EntryMatchVPNASID vpn as e = EntryMatchVPNASID (vpn - 1)  as e"
proof cases
  assume match : "EntryMatchVPNASID vpn as e"
  then show ?thesis 
  proof -
    from match have X0:
      "EntryASIDMatchA as e"
      by(simp add:EntryMatchVPNASID_def)
    from match have X1:
      "EntryVPNMatchV vpn e"
      by(simp add:EntryMatchVPNASID_def)
    
    from eodd vpn2even mask4k have X3:
      "EntryVPNMatchV vpn e = EntryVPNMatchV (vpn - 1) e"
      by(simp add:EntryVPNMatchV_equals_odd)
    
    have X4: "EntryMatchVPNASID (vpn - 1)  as e = 
        (EntryVPNMatchV (vpn - 1) e \<and> EntryASIDMatchA as e)"
       by(simp add:EntryMatchVPNASID_def)
    
     from match X4 X0 X3 X1 show ?thesis 
       by(auto)
  qed
next
  assume nmatch : "\<not> EntryMatchVPNASID vpn as e"
  then show ?thesis 
  proof cases
    assume asidmatch: "EntryASIDMatchA as e"
    then show ?thesis 
    proof -
      from nmatch asidmatch have X0:
        "\<not>EntryVPNMatchV vpn e"
        by(simp add:EntryMatchVPNASID_def)
      
      from  vpn2even mask4k eodd have X1:
        "EntryVPNMatchV vpn e = EntryVPNMatchV (vpn - 1) e"
        by(simp add:EntryVPNMatchV_equals_odd)

      have X2: "EntryMatchVPNASID (vpn - 1)  as e = 
        (EntryVPNMatchV (vpn - 1) e \<and> EntryASIDMatchA as e)"
       by(simp add:EntryMatchVPNASID_def)
          
      from nmatch X0 X1 X2 show ?thesis 
        by(auto)
    qed
  next
    assume nasidmatch: "\<not>EntryASIDMatchA as e"
    then show ?thesis 
    proof -
      have X0: "EntryMatchVPNASID (vpn - 1)  as e = 
        (EntryVPNMatchV (vpn - 1) e \<and> EntryASIDMatchA as e)"
        by(simp add:EntryMatchVPNASID_def)
      
      from nmatch nasidmatch X0 show ?thesis 
        by(auto)
    qed
  qed    
qed
  

lemma EntryMatch_equals_even :
  assumes eeven: "even vpn"
      and vpn2even: "even (vpn2 (hi (e)))"
      and mask4k: "(mask (e)) = MASK4K"
    shows "EntryMatchVPNASID vpn as e = EntryMatchVPNASID (vpn + 1)  as e"
proof -
  from eeven have X0 :
    "odd (vpn + 1)"
    by(auto)
  
  from vpn2even X0 mask4k have X1: 
    "EntryMatchVPNASID (vpn + 1) as e = EntryMatchVPNASID ((vpn + 1) -1)  as e"
    by(auto simp:EntryMatch_equals_odd)
   
  from X1 show ?thesis 
    by(auto)
qed
  
  


  
(* ------------------------------------------------------------------------- *)   
subsection "TLB Entry Ranges"
(* ------------------------------------------------------------------------- *)   
  
text "Function to create the set of valid indexes for the given TLB"
  
definition ValidIndexRange :: "MIPSTLB \<Rightarrow> nat set"  
  where "ValidIndexRange tlb =  {x.  0 \<le> x \<and> x < (capacity tlb)}"
  
definition RandomIndexRange :: "MIPSTLB \<Rightarrow> nat set"  
  where "RandomIndexRange tlb =  {x.  (wired tlb) \<le> x \<and> x < (capacity tlb)} \<union> {(capacity tlb) - 1}"


lemma RandomIndex_in_capacity:
"\<And>i. (capacity tlb) > 0 \<Longrightarrow> i \<in> RandomIndexRange tlb \<Longrightarrow>  i < (capacity tlb)"
  by(auto simp add:RandomIndexRange_def)
    

    
(* ========================================================================= *)    
section "TLB Predicates"
(* ========================================================================= *)  

text "The following are predicates on the TLB state"  
  
  
(* ------------------------------------------------------------------------- *) 
subsection "TLB Entries Valid"  
(* ------------------------------------------------------------------------- *)   
  
definition TLBEntryWellFormed :: "MIPSTLB \<Rightarrow> nat \<Rightarrow> bool"
  where "TLBEntryWellFormed tlb e = (TLBENTRYWellFormed ((entries tlb) e))"
    
definition TLBEntriesWellFormed :: "MIPSTLB \<Rightarrow> bool"
  where "TLBEntriesWellFormed tlb = (\<forall>i < (capacity tlb). TLBEntryWellFormed tlb i)"     


(* ------------------------------------------------------------------------- *) 
subsection "Entry Conflicts"  
(* ------------------------------------------------------------------------- *)     

text "The following predicate returns true, if and only if the supplied TLB entry
      does not match with any of the TLB entries."
  
  
definition TLBEntryNoConflict ::  "TLBENTRY \<Rightarrow> MIPSTLB \<Rightarrow> bool"
  where "TLBEntryNoConflict e tlb = (\<forall>i < (capacity tlb). \<not> EntryMatch ((entries tlb) i) e)"

definition TLBEntryConflictSet ::  "TLBENTRY \<Rightarrow> MIPSTLB \<Rightarrow> nat set"
  where "TLBEntryConflictSet e tlb = {i . i < (capacity tlb) \<and> EntryMatch ((entries tlb) i) e}"

definition TLBEntryConflictSetER ::  "TLBENTRY \<Rightarrow> MIPSTLB \<Rightarrow> nat set"
  where "TLBEntryConflictSetER e tlb = {i . i < (capacity tlb) \<and> EntryMatchER ((entries tlb) i) e}"    


text "If there is no conflict, then the conflict set is emtpy"
lemma NoConflictNoConflictSet:
  "\<And>e.( TLBEntryNoConflict e tlb) = (TLBEntryConflictSet e tlb = {})"
  by(simp add:TLBEntryNoConflict_def TLBEntryConflictSet_def)
  

text "The Conflict set and the conflict set with extended range must be equal"
    
lemma TLBEntryConflictSetEq :
  assumes nz: "VASize \<noteq> 0" 
      and wf: "\<forall>i<(capacity tlb). TLBENTRYWellFormed (entries tlb i)"
      and wf2: "\<And>e. TLBENTRYWellFormed e"
    shows "\<And>e. TLBEntryConflictSet e tlb = TLBEntryConflictSetER e tlb"
  by(simp add:TLBEntryConflictSet_def TLBEntryConflictSetER_def EntryMatchEqualsEntryMatchER nz wf wf2)    

lemma TLBEntryConflictSetEq3:
  assumes nz: "VASize \<noteq> 0" 
      and wf: "\<And>i. TLBENTRYWellFormed (entries tlb i)"
    shows "TLBEntryConflictSet (entries tlb i) tlb = TLBEntryConflictSetER (entries tlb i) tlb"
  by(simp add:TLBEntryConflictSet_def TLBEntryConflictSetER_def EntryMatchEqualsEntryMatchER nz wf)        
    
lemma TLBEntryConflictSetEq2 :
  assumes nz: "VASize \<noteq> 0" 
      and wf: "\<forall>x < (capacity tlb). TLBENTRYWellFormed (entries tlb x)"
      and inrange: "\<And>i. i < (capacity tlb)"
    shows "TLBEntryConflictSet (entries tlb i) tlb = TLBEntryConflictSetER (entries tlb i) tlb"
  by(simp add: TLBEntryConflictSet_def TLBEntryConflictSetER_def EntryMatchEqualsEntryMatchER nz wf inrange)
  
    
(* ------------------------------------------------------------------------- *) 
subsection "TLB Valid"  
(* ------------------------------------------------------------------------- *) 
  
text "The TLB is in a valid state if all entries are valid with respect to
      their values and for any two entries, they are either the same
      or they won't match to the same genaddress range. For any state 
      modification of the TLB, this must hold. "
  
definition TLBValid_orig :: "MIPSTLB \<Rightarrow> bool"
  where "TLBValid_orig tlb = (((wired tlb) \<le> (capacity tlb)  \<and> (wired tlb) < TLBMaximumWired ) \<and> (\<forall>i < (capacity tlb). \<forall>j < (capacity tlb). 
                        (TLBEntryWellFormed tlb i) \<and> (
                        (i = j) \<or> \<not> EntryMatch ((entries tlb) i) ((entries tlb j)))))"    

definition TLBValid:: "MIPSTLB \<Rightarrow> bool"
  where "TLBValid tlb = (((wired tlb) \<le> (capacity tlb)  \<and> (wired tlb) < TLBMaximumWired  ) \<and> (\<forall>i < (capacity tlb).  
                        (TLBEntryWellFormed tlb i) \<and> ((TLBEntryConflictSet (entries tlb i) tlb) \<subseteq> {i})))"    

definition TLBValidER :: "MIPSTLB \<Rightarrow> bool"
  where "TLBValidER tlb = (((wired tlb) \<le> (capacity tlb) \<and> (wired tlb) < TLBMaximumWired ) \<and> (\<forall>i < (capacity tlb).  
                        (TLBEntryWellFormed tlb i) \<and> ((TLBEntryConflictSetER (entries tlb i) tlb) \<subseteq> {i})))"      
    
    
text "The TLBValid using conflict sets must be equal to the original TLBValid definition"    
  
lemma TLBValid_orig_isTLBValid:
  "TLBValid tlb = TLBValid_orig tlb"
  by(auto simp add:TLBValid_def TLBValid_orig_def TLBEntryConflictSet_def)
        

lemma TLBValidImpliesWired :
  "TLBValid t \<longrightarrow> (wired t) \<le> TLBMaximumWired"
  by(simp add:TLBMaximumWired_def TLBValid_def)
    
lemma TLBValidImpliesEntriesValid :
  "TLBValid tlb \<longrightarrow> (\<forall>i < (capacity tlb). (TLBEntryWellFormed tlb i))"
  by(simp add:TLBValid_def)
    
lemma TLBValidImpliesWellFormed:  
  "TLBValid tlb \<Longrightarrow> \<forall>i < (capacity tlb). TLBENTRYWellFormed (entries tlb i)"
  by(simp add:TLBValid_def TLBEntryWellFormed_def)
     
lemma TLBValidERImpliesWellFormed:  
  "TLBValidER tlb \<Longrightarrow> \<forall>i < (capacity tlb). TLBENTRYWellFormed (entries tlb i)"
  by(simp add:TLBValidER_def TLBEntryWellFormed_def)    


text "If the TLB is well formed, then for all entries, they do not overlap"
  
lemma TLBValidImpliesNotOverlap :
  "\<And>i. \<And>j. i < (capacity tlb) \<Longrightarrow> j < (capacity tlb) \<Longrightarrow> i \<noteq> j \<Longrightarrow> TLBValidER tlb \<Longrightarrow> 
   EntryExtendedRange (entries tlb i) \<inter> EntryExtendedRange (entries tlb j) = {}"
proof -
  fix i j
  assume valid : "TLBValidER tlb"
  
  from valid have wired: "wired tlb < TLBMaximumWired \<and>  wired tlb \<le> capacity tlb" 
     by(simp add:TLBValidER_def valid)
  from valid have wellformed : " \<forall>j<(capacity tlb). TLBEntryWellFormed tlb j"
     by(simp add:TLBValidER_def valid)    
    
   have X0: "TLBValidER tlb = (wired tlb < TLBMaximumWired \<and> wired tlb \<le> capacity tlb \<and> (\<forall>i<(capacity tlb). 
                  TLBEntryWellFormed tlb i \<and> TLBEntryConflictSetER (entries tlb i) tlb \<subseteq> {i}))"
    by(auto simp add:TLBValidER_def) 

  hence X2:  "... =  (\<forall>i<(capacity tlb). {ia. ia < (capacity tlb) \<and> 
                          EntryExtendedRange (entries tlb ia) \<inter>
                          EntryExtendedRange (entries tlb i) \<noteq> {}} \<subseteq> {i})"
    by(simp add:TLBEntryConflictSetER_def EntryMatchER_def wired wellformed)
  
  with X0 X2 show "\<And>i j. i < (capacity tlb) \<Longrightarrow> j < (capacity tlb) \<Longrightarrow> i \<noteq> j \<Longrightarrow> TLBValidER tlb \<Longrightarrow> 
                  EntryExtendedRange (entries tlb i) \<inter> EntryExtendedRange (entries tlb j) = {}"
    by(auto)        
qed  

  
  
  
text "TLBValid is the same as TLBValidER"  

lemma TLBValidIsTLBValidER :
  shows "TLBValid tlb = TLBValidER tlb"
proof 
  show "TLBValid tlb \<Longrightarrow> TLBValidER tlb" 
  proof - 
    assume valid: "TLBValid tlb"
      
    have X0: "TLBValidER tlb = (((wired tlb) < TLBMaximumWired \<and>  wired tlb \<le> capacity tlb ) \<and> (\<forall>i < (capacity tlb). \<forall>j < (capacity tlb). 
                           (TLBEntryWellFormed tlb i) \<and> (
                           (i = j) \<or> \<not> EntryMatchER ((entries tlb) i) ((entries tlb j)))))"
      by(auto simp add:TLBValidER_def TLBEntryConflictSetER_def)
    
    also  have X1: "TLBValid tlb =  (((wired tlb) < TLBMaximumWired  \<and>  wired tlb \<le> capacity tlb ) \<and> (\<forall>i < (capacity tlb). \<forall>j < (capacity tlb). 
                                (TLBEntryWellFormed tlb i) \<and> (
                                (i = j) \<or> \<not> EntryMatch ((entries tlb) i) ((entries tlb j)))))"
      by(auto simp add:TLBValid_def TLBEntryConflictSet_def)
                
    have nz: "VASize \<noteq> 0" by(simp add:VASize_def)
    with valid have wf: "\<forall>i < (capacity tlb). TLBENTRYWellFormed (entries tlb i)"
      by(auto simp add:TLBValidImpliesWellFormed)
    
    with valid wf nz have X2: "TLBValidER tlb = (((wired tlb) < TLBMaximumWired  \<and>  wired tlb \<le> capacity tlb ) \<and> (\<forall>i < (capacity tlb). \<forall>j < (capacity tlb). 
                           (TLBEntryWellFormed tlb i) \<and> (
                           (i = j) \<or> \<not> EntryMatch ((entries tlb) i) ((entries tlb j)))))"
      by(simp add:X0 EntryMatchEqualsEntryMatchER)
    
    with valid wf nz X2 show ?thesis 
      by(simp add:TLBValidER_def X0 X1)
       
    qed
  next     
  show "TLBValidER tlb \<Longrightarrow> TLBValid tlb" 
  proof - 
    fix i
    assume valid: "TLBValidER tlb"
    have X0: "TLBValidER tlb = (((wired tlb) < TLBMaximumWired  \<and>  wired tlb \<le> capacity tlb ) \<and> (\<forall>i < (capacity tlb). \<forall>j < (capacity tlb). 
                           (TLBEntryWellFormed tlb i) \<and> (
                           (i = j) \<or> \<not> EntryMatchER ((entries tlb) i) ((entries tlb j)))))"
      by(auto simp add:TLBValidER_def TLBEntryConflictSetER_def)
    
    also  have X1: "TLBValid tlb =  (((wired tlb) < TLBMaximumWired  \<and>  wired tlb \<le> capacity tlb ) \<and> (\<forall>i < (capacity tlb). \<forall>j < (capacity tlb). 
                                (TLBEntryWellFormed tlb i) \<and> (
                                (i = j) \<or> \<not> EntryMatch ((entries tlb) i) ((entries tlb j)))))"
      by(auto simp add:TLBValid_def TLBEntryConflictSet_def)
                
    have nz: "VASize \<noteq> 0" by(simp add:VASize_def)
    with valid have wf: "\<forall>i < (capacity tlb). TLBENTRYWellFormed (entries tlb i)"
      by(auto simp add:TLBValidERImpliesWellFormed)
    
    with valid wf nz have X2: "TLBValidER tlb = (((wired tlb) < TLBMaximumWired ) \<and> (\<forall>i < (capacity tlb). \<forall>j < (capacity tlb). 
                           (TLBEntryWellFormed tlb i) \<and> (
                           (i = j) \<or> \<not> EntryMatch ((entries tlb) i) ((entries tlb j)))))"
      by(simp add:X0 EntryMatchEqualsEntryMatchER)
    
    with valid wf nz X2 show ?thesis 
      by(simp add:TLBValidER_def X0 X1)    
  qed        
qed    
    
  
lemma even_vpn_compare:  
  assumes aeven: "even (a::nat)"
      and eeven: " even (vpn::nat)"
      and prec: "a \<le> vpn \<and> vpn \<le> Suc a"
    shows "vpn = a"
proof -
  from aeven have X0: "odd (Suc a)"
    by(auto)
      
  from X0 eeven have X1: "vpn \<noteq> (Suc a)"
    by(auto)
      
  from X1 eeven have X3: "(a \<le> vpn \<and> vpn \<le> Suc a) = (a \<le> vpn \<and> vpn < Suc a)"
    by(auto)
      
  from X3 have X4: " ... =  (a \<le> vpn \<and> vpn \<le> a)"
    by(auto)
      
  from X4 have X5: "(a \<le> vpn \<and> vpn \<le> a) \<longrightarrow> vpn = a"
    by(auto)

  from prec aeven eeven X0 X1 X3 X4 X5  show "vpn = a"
    by(auto)      
qed  

lemma TLBValid_implies_no_other_match :
  assumes valid : "TLBValid tlb"
     and inrange: "j < (capacity tlb)"
      and inrange2: "i < (capacity tlb)" 
      and mask4k : "\<forall>idx < (capacity tlb). mask ((entries tlb) idx) = MASK4K" 
      and match : "EntryMatchVPNASID vpn as (entries tlb i)" 
    shows "i = j \<longleftrightarrow> EntryMatchVPNASID vpn as (entries tlb j)"
proof cases
  assume eq: "i = j"
  then show ?thesis 
  proof -
    from eq have X0: "(entries tlb i) = (entries tlb j)"
      by(auto)
        
    from eq match X0 show ?thesis 
      by(auto)
  qed
next
  assume neq: "i \<noteq> j"
  then show ?thesis 
  proof -
    from valid have X0: 
      "(((wired tlb) \<le> (capacity tlb)  \<and> (wired tlb) < TLBMaximumWired ) \<and> (\<forall>i < (capacity tlb). \<forall>j < (capacity tlb). 
                        (TLBEntryWellFormed tlb i) \<and> (
                        (i = j) \<or> \<not> EntryMatch ((entries tlb) i) ((entries tlb j)))))"
      by(auto simp add:TLBValid_def TLBValid_orig_def TLBEntryConflictSet_def)
    
    from X0 neq inrange inrange2 have X1:
      "\<not> EntryMatch ((entries tlb) i) ((entries tlb j))"
      by(auto)
    
    from X1 have X2: "\<not>((EntryVPNMatch ((entries tlb) i)  ((entries tlb j))) 
                        \<and> (EntryASIDMatch ((entries tlb) i)  ((entries tlb j))))" 
      by(simp add:EntryMatch_def)
    
    from valid have vpn2even:
      "\<forall>x < (capacity tlb). even (vpn2 (hi (entries tlb x)))"
      by(simp add:TLBValid_def TLBEntryWellFormed_def TLBENTRYWellFormed_def
                     TLBENTRYHIWellFormed_def VPN2Valid_def)
        
    show ?thesis
    proof cases
      assume vpnmatch : "EntryVPNMatch ((entries tlb) i)  ((entries tlb j))"
      then show ?thesis 
      proof -
        from vpnmatch X2 have Y0:
          "\<not>(EntryASIDMatch ((entries tlb) i)  ((entries tlb j)))"
          by(auto)
            
        from Y0 have Y1: "\<not> EntryIsGlobal ((entries tlb) i)"
          by(simp add:EntryASIDMatch_def)
            
        from Y1 match have Y2: "(asid (hi ((entries tlb) i))) = as"
          by(simp add:EntryMatchVPNASID_def EntryASIDMatchA_def)
        
        from Y0 have Y3:
          "\<not>EntryASIDMatchA (asid (hi ((entries tlb) i))) ((entries tlb j))"
          by(simp add:EntryASIDMatch_def EntryASIDMatchA_def)
        
        from Y3 Y2 have Y4: "\<not>EntryASIDMatchA as ((entries tlb j))"
          by(auto)
            
        from Y4 have Y5: "\<not>EntryMatchVPNASID vpn as (entries tlb j)"
          by(simp add:EntryMatchVPNASID_def)
          
        from neq Y5 show ?thesis
          by(auto)
      qed
    next
      assume nvpnmatch : "\<not>EntryVPNMatch ((entries tlb) i)  ((entries tlb j))"
      then show ?thesis
      proof cases
        assume veven: "even vpn"
        then show ?thesis
        proof -
          from nvpnmatch vpn2even mask4k inrange2 inrange veven have Y0:
            "\<not>EntryVPNMatchV (vpn2 (hi (entries tlb i))) (entries tlb j)"
            apply(simp add:EntryVPNMatch_def EntryRange_def EntryMinVA_def EntryMaxVA_def KB_def EntrySize_def page_size_def)
            apply(simp add:EntryVPNMatchV_def EntryMin4KVPN_def EntryMax4KVPN_def num_4k_pages_def)
            apply(auto)
            done
          
          from inrange2 veven match vpn2even mask4k have Y1: 
            "(vpn2 (hi (entries tlb i))) = vpn"
            apply(simp add:EntryMatchVPNASID_def EntryVPNMatchV_def EntryMin4KVPN_def 
                           EntryMax4KVPN_def num_4k_pages_def)
            apply(auto simp:even_vpn_compare)          
            done
          
          from Y1 Y0 have Y3:
           "\<not>EntryVPNMatchV vpn (entries tlb j)"
            by(auto)
           
          from Y3 have Y4:
            "\<not>EntryMatchVPNASID vpn as (entries tlb j)"
            by(auto simp:EntryMatchVPNASID_def)
          from neq Y4 show ?thesis 
            by(auto)
        qed
      next
        assume vodd: "odd vpn"
        then show ?thesis
        proof -
          from nvpnmatch vpn2even mask4k inrange2 inrange vodd have Y0:
            "\<not>EntryVPNMatchV (vpn2 (hi (entries tlb i))) (entries tlb j)"
            apply(simp add:EntryVPNMatch_def EntryRange_def EntryMinVA_def EntryMaxVA_def KB_def EntrySize_def page_size_def)
            apply(simp add:EntryVPNMatchV_def EntryMin4KVPN_def EntryMax4KVPN_def num_4k_pages_def)
            apply(auto)
            done
              
          from inrange2 vodd match vpn2even mask4k have Y1: 
            "(vpn2 (hi (entries tlb i))) = vpn - 1"
            apply(simp add:EntryMatchVPNASID_def EntryVPNMatchV_def EntryMin4KVPN_def 
                           EntryMax4KVPN_def num_4k_pages_def)
            apply(auto simp:even_vpn_compare)          
            done              
          
          from Y1 Y0 have Y3:
           "\<not>EntryVPNMatchV (vpn - 1) (entries tlb j)"
            by(auto)
          
          from Y3 have Y4:
            "\<not>EntryMatchVPNASID (vpn - 1) as (entries tlb j)"
            by(auto simp:EntryMatchVPNASID_def)
          
          from inrange valid have vpn2even:
            "(even (vpn2 (hi (entries tlb j))))"
            by(simp add:TLBValid_def TLBEntryWellFormed_def TLBENTRYWellFormed_def 
                        TLBENTRYHIWellFormed_def VPN2Valid_def)

          from inrange mask4k have Y6:
            " (mask ( (entries tlb j))) = MASK4K"
            by(auto)
                      
          from Y4 vpn2even vodd Y6 have  Y5:
           "(\<not>EntryMatchVPNASID (vpn) as (entries tlb j))
               = (\<not>EntryMatchVPNASID (vpn - 1) as (entries tlb j))"
             by(auto simp add:EntryMatch_equals_odd)
                
          from neq Y4 Y5 show ?thesis 
            by(auto)
        qed          
      qed
        
    qed
  qed
qed

 
    
(* ========================================================================= *)
section "TLB Initialization"
(* ========================================================================= *)    
    
text "There are two functions that can be used to initialize the TLB. First
      the reset function will put the TLB into the state after reset. The 
      initialize function will put the TLB into a known valid state"  

  
(* ------------------------------------------------------------------------- *)  
subsection "TLB Reset"
(* ------------------------------------------------------------------------- *)  

text "After reset, the initial state of the entries is undefined"  

text "The TLBReset function initializes a new TLB at reset state. 
      Number of wired entries is set to zero, the TLB entries
      are undefined."
    
definition TLB_in_reset :: "MIPSTLB \<Rightarrow> bool" where
  "TLB_in_reset tlb \<longleftrightarrow> wired tlb = 0 \<and> (random tlb = (capacity tlb - 1))"

text "The invalid TLB satisfies the reset"
  
lemma InvalidTLBInReset :  "TLB_in_reset invalid_tlb"
  by (simp add:TLB_in_reset_def invalid_tlb_def)  

    
(* ------------------------------------------------------------------------- *)  
subsection "TLB Initialization"
(* ------------------------------------------------------------------------- *)     
   
text "The MIPSTLBinit function initializes the TLB into a valid state"    
    
definition MIPSTLBInit :: "nat \<Rightarrow> nat \<Rightarrow> MIPSTLB \<Rightarrow> MIPSTLB"
  where "MIPSTLBInit c w tlb = \<lparr> 
              capacity = c ,
              wired = w,
              random = c - 1,
              entries = (\<lambda>n. if n < c then TLBEntryReset (n) else entries tlb n) \<rparr>"

definition MIPSR4600TLBinit :: "nat \<Rightarrow> MIPSTLB \<Rightarrow> MIPSTLB"
  where "MIPSR4600TLBinit w tlb = MIPSTLBInit MIPSR4600Capacity w tlb"
    
lemma TLBInit_entry_is:
  "\<And>tlb n c w. n < (capacity (MIPSTLBInit c w tlb)) \<Longrightarrow> 
                entries (MIPSTLBInit c w tlb) n = TLBEntryReset  n"
  by(simp add: MIPSTLBInit_def)
    
    
text "If we reset the TLB and initialize it with a valid number of wired entries,
      then the TLB will end up in a valid state"    
    
lemma InitializedTLBIsValid : 
  "\<And>tlb w c. TLB_in_reset tlb \<Longrightarrow> w < c \<and> (2 * c) < VPN2Max MASK4K \<Longrightarrow>
         w < TLBMaximumWired \<Longrightarrow> TLBValid (MIPSTLBInit c w tlb)"
  apply(simp add:TLBValid_def TLBEntryWellFormed_def)
  apply(simp add:TLBEntryConflictSet_def)
  apply(simp add:TLBInit_entry_is MIPSTLBInit_def TLBEntryResetWellFormed)
  apply(simp add:EntryMatch_def TLBEntryResetASID_match)
  apply(simp add:EntryVPNMatch_def EntryRange_def)
  apply(simp add:EntryMinVA_def EntryMaxVA_def EntrySize_def)
  apply(simp add:TLBEntryResetVPN2_is TLBEntryResetMask_is KB_def)
  apply(auto)
  done    

text "The Initialized TLB has all invalid entries, i.e. they don't map"

lemma InitialidezAllInvalid :
  "\<And>idx. idx < c \<Longrightarrow> w < TLBMaximumWired \<Longrightarrow>  
        \<not>(EntryIsValid ((entries (MIPSTLBInit c w tlb)) idx))"
  by(simp add:MIPSTLBInit_def TLBEntryResetNotValid_id )

    
    
(* ------------------------------------------------------------------------- *)  
subsection "Not all reset states are valid"
(* ------------------------------------------------------------------------- *)  

text "we now show that there exists a TLB state which satisfies the reset
      property and at the same time the TLB has an invalid state.
      For this we use the Invalid TLB we defined before."
    
lemma "\<exists>t. TLB_in_reset t"
  apply(rule exI[where x = invalid_tlb])
  apply(simp add:InvalidTLBInReset)   
  done  
    
text "We define helper Lemmas that show that the invalid  TLB has
     all nullentries and that therefore all entries are valid."
  
lemma InvalidTLBAllNullEntries :
  "(entries invalid_tlb) i = null_entry"
  by(simp add:invalid_tlb_def)

lemma InvalidTLBAllValidEntries :
  "\<forall>i < (capacity tlb) . TLBEntryWellFormed invalid_tlb i"
  by(auto simp: TLBEntryWellFormed_def InvalidTLBAllNullEntries NullEntryIsValid)

text "Next we show that two null entries always match, by having matching ASID
      and VPN numbers"
        
lemma NullEntriesASIDMatch :
  "EntryASIDMatch null_entry null_entry"
  by(simp add: EntryASIDMatch_def)
    
lemma NullEntriesVPNMatch :
  "EntryVPNMatch null_entry null_entry"
  by(auto simp: EntryVPNMatch_def EntryRange_def MinVANullEntry)

lemma NullEntriesMatch :
  "EntryMatch null_entry null_entry"
  by(auto simp:EntryMatch_def NullEntriesVPNMatch NullEntriesASIDMatch)

text "We can now show that the invalid TLB does in fact not satisfy the TLBValid
      predicate by using the knowledge, that all the entries are nullentries
      and thus are valid and match"

lemma InvalidTLBWired0 : " wired invalid_tlb = 0"
  by(auto simp:invalid_tlb_def)
    
lemma InvalidTLBNotValid : 
  "(TLBValid invalid_tlb) = False"
proof -

  have wired: "wired invalid_tlb \<le> capacity invalid_tlb"
    by(simp add:invalid_tlb_def MIPSR4600Capacity_def)
      
  have v: "TLBValid invalid_tlb = 
      (((wired invalid_tlb) < TLBMaximumWired ) \<and> 
      (\<forall>i < (capacity invalid_tlb). 
          \<forall>j < (capacity invalid_tlb). 
            (TLBEntryWellFormed invalid_tlb i) \<and> (
           (i = j) \<or> \<not> EntryMatch ((entries invalid_tlb) i) ((entries invalid_tlb j)))))"
     by(auto simp add:TLBValid_def TLBValid_orig_def TLBEntryConflictSet_def wired)
  
   have X0: " ... =  
        (wired invalid_tlb < TLBMaximumWired  \<and> 
        (\<forall>i<(capacity invalid_tlb). 
          \<forall>j<(capacity invalid_tlb). 
            TLBEntryWellFormed invalid_tlb i \<and> 
            (i = j \<or> \<not> EntryMatch null_entry null_entry)))"
     by(auto simp add:InvalidTLBAllNullEntries)
  
   have X1: "... =  (wired invalid_tlb < TLBMaximumWired  \<and> 
                (\<forall>i<(capacity invalid_tlb).
                   \<forall>j<(capacity invalid_tlb). 
                    TLBEntryWellFormed invalid_tlb i \<and> (i = j)))"
     by(auto simp add:NullEntriesMatch)
   
   have X2: "... =  (\<forall>i<(capacity invalid_tlb). 
                      \<forall>j<(capacity invalid_tlb). 
                        TLBEntryWellFormed invalid_tlb i \<and> (i = j)) "
     by(auto simp add:InvalidTLBWired0 TLBMaximumWired_def)
    
   have X3: "... = (\<forall>i<(capacity invalid_tlb). \<forall>j<(capacity invalid_tlb). (i = j))" 
     by(simp add:InvalidTLBAllValidEntries) 

    show ?thesis
      apply(simp only:v) 
      apply(simp only:X0) 
      apply(simp only:X1) 
      apply(simp only:X2) 
      apply(simp only:X3) 
      apply(simp add:invalid_tlb_def MIPSR4600Capacity_def)
      apply(rule exI[where x = 0], auto)
      apply(rule exI[where x = 1], auto)
      done
qed
 
       
text "We can use the lemmas to prove our theorem, that there exist a TLB state
      that satisfies the reset condition and that is invalid at the same time."
    
  
theorem " \<exists>t. TLB_in_reset t \<and> \<not>(TLBValid t)"
  apply(rule exI[where x = invalid_tlb])
  apply(simp add:InvalidTLBInReset InvalidTLBNotValid)
done
  
  
             
(* ========================================================================= *)
section "TLB Operations"
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)   
subsection "TLB Read Entry"
(* ------------------------------------------------------------------------- *)   

text "We now define the TLB read operation. This operation will return whats
      in the requested entry. After reset this content may not be defined."  
 

definition tlbr :: "nat \<Rightarrow> MIPSTLB \<Rightarrow> TLBENTRY set" 
  where "tlbr idx tlb = (if idx < (capacity tlb) then  {((entries tlb) idx)}
                         else  UNIV)"
 
text "The behavior of this function is undefined if it's being called with
      and index that is outside of the defined range, otherwise it
      returns what's in there."
  
lemma "\<And>idx. idx \<ge> (capacity tlb) \<Longrightarrow> tlbr idx tlb = UNIV"
  by (auto simp: tlbr_def)

lemma "\<And>idx. idx < (capacity tlb) \<Longrightarrow> tlbr idx tlb = {entries tlb idx}"
  by(simp add:tlbr_def)
         
    
(* ------------------------------------------------------------------------- *)   
subsection "TLB Probe"
(* ------------------------------------------------------------------------- *)       

text "The probe function returns an entry which matches the EntryHi (ASID and VPN).
      There is at most one entry that matches, or nothing"
  
definition tlbp :: "TLBENTRYHI \<Rightarrow> MIPSTLB \<Rightarrow> nat set" where
  "tlbp reg tlb = (if (\<exists>i. (EntryMatchVPNASID (vpn2 reg) (asid reg) ((entries tlb) i) )) 
                   then {(SOME i. (EntryMatchVPNASID (vpn2 reg) (asid reg) ((entries tlb) i) ))} 
                   else UNIV)"
  

lemma 
  assumes inrange: "\<And>idx. idx < (capacity tlb)"
    and   valid : "TLBValid tlb"
  shows "\<And>idx e. tlbr idx tlb = {e} \<Longrightarrow> tlbp (hi e) tlb = {idx}"
proof -
  fix idx
  
  obtain e where E: "e = (entries tlb idx)" by(simp add:tlbr_def inrange)
    
  with E have X0: "tlbp (hi e) tlb = tlbp (hi (entries tlb idx)) tlb"
    by(auto)
  
  with inrange valid E X0 show "\<And>idx e. tlbr idx tlb = {e} \<Longrightarrow> tlbp (hi e) tlb = {idx}" 
    by(auto)
qed
    
   
  
    
(* ------------------------------------------------------------------------- *)   
subsection "TLB Write Index"  
(* ------------------------------------------------------------------------- *)   
  
  definition tlbwi :: "nat \<Rightarrow> TLBENTRY \<Rightarrow> MIPSTLB \<Rightarrow> MIPSTLB set"
    where "tlbwi idx e tlb = (if idx < (capacity tlb) then 
                                 {\<lparr> capacity = (capacity tlb),
                                    wired = (wired tlb),  
                                    random = random tlb,
                                    entries = (entries tlb)(idx :=  e) \<rparr>}
                              else 
                                 UNIV)"

  
  definition tlbwi2 :: "nat \<Rightarrow> TLBENTRY \<Rightarrow> MIPSTLB \<Rightarrow> MIPSTLB set"
    where "tlbwi2 idx e tlb = (if idx < (capacity tlb) then 
                                 {\<lparr> capacity = (capacity tlb),
                                    wired = (wired tlb),  
                                    random = random tlb,
                                    entries = (entries tlb)(idx :=  e) \<rparr>}
                              else 
                                 UNIV)"
    
lemma "\<And>tlb e.  (capacity tlb) > 0 \<Longrightarrow> tlbwi ((vpn2 (hi (e))) mod (capacity tlb)) e tlb =
           {\<lparr> capacity = (capacity tlb), 
             wired = (wired tlb), 
             random = random tlb,
             entries = (entries tlb)(((vpn2 (hi (e))) mod (capacity tlb)) :=  e) \<rparr>}"
  by(simp add:tlbwi_def)
  
    
definition TLBEntryWriteable :: "nat \<Rightarrow> TLBENTRY \<Rightarrow> MIPSTLB \<Rightarrow> bool"
  where "TLBEntryWriteable idx e tlb = ((TLBEntryConflictSet e tlb \<subseteq> {idx}))"

lemma NoConflictsImpliesWriteable :
  "\<And>e idx. (TLBEntryConflictSet e tlb = {}) \<Longrightarrow> TLBEntryWriteable idx e tlb"
  by(simp add: TLBEntryNoConflict_def TLBEntryWriteable_def)
    
    
lemma TLBUpdateValid :
  assumes tlbvalid: "TLBValid tlb"
    and wf: "\<And>e.  TLBENTRYWellFormed e"
    and wr: "\<And>e idx.  TLBEntryWriteable idx e tlb"
    and ir: "\<And>idx. idx < (capacity tlb)"
  shows 
   "\<And>idx e. \<forall>t \<in> tlbwi idx e tlb. TLBValid t"
proof
  
  have X0:  "\<And>idx e. \<forall>t \<in> tlbwi idx e tlb. TLBValid t = 
                          TLBValid \<lparr>capacity = capacity tlb,
                                    wired = wired tlb, 
                                    random = random tlb,
                                    entries = (entries tlb)(idx := e) \<rparr>"
     by(simp add:tlbwi_def ir)
      
   have X1:  "TLBValid tlb \<Longrightarrow>(wired tlb) \<le> (capacity tlb) \<and> (wired tlb) < TLBMaximumWired "
     by(simp add: TLBValid_def)
       
   have X2:  "(wired  \<lparr>capacity = capacity tlb, 
                     wired = wired tlb, 
                     random = random tlb,
                     entries = (entries tlb)(idx := e)\<rparr>) \<le> (capacity  \<lparr>capacity = capacity tlb, 
                     wired = wired tlb, 
                     random = random tlb,
                     entries = (entries tlb)(idx := e)\<rparr>) \<and> (wired \<lparr>capacity = capacity tlb, 
                     wired = wired tlb, 
                     random = random tlb,
                     entries = (entries tlb)(idx := e)\<rparr> < TLBMaximumWired)"
     by(simp add:  X1 tlbvalid )
       
   have X3: "\<And>i. (TLBEntryWellFormed  \<lparr> capacity = capacity tlb, 
                                        wired = wired tlb, 
                                        random = random tlb,
                                        entries = (entries tlb)(idx := e)\<rparr> i) =
            (TLBEntryWellFormed tlb i) \<and> TLBENTRYWellFormed e"
     by(simp add:TLBEntryWellFormed_def wf)
       
   have X4: "\<And>i. (TLBEntryWellFormed tlb i) \<and> TLBENTRYWellFormed e = True"
     by(simp add: wf tlbvalid TLBValidImpliesEntriesValid ir)
  
   have X5: "TLBValid \<lparr> capacity = capacity tlb, 
                        wired = wired tlb, 
                        random = random tlb,
                        entries = (entries tlb)(idx := e)\<rparr> = 
         (\<forall>i<(capacity tlb).
         TLBEntryWellFormed \<lparr>capacity = capacity tlb, 
                            wired = wired tlb, 
                            random = random tlb,
                            entries = (entries tlb)(idx := e)\<rparr> i \<and>
         TLBEntryConflictSet (
                  entries \<lparr> capacity = capacity tlb, 
                           wired = wired tlb, 
                           random = random tlb,
                           entries = (entries tlb)(idx := e)\<rparr> i)
                  \<lparr> capacity = capacity tlb, 
                    wired = wired tlb, 
                    random = random tlb,
                    entries = (entries tlb)(idx := e)\<rparr> \<subseteq> {i})"
     by(simp only:TLBValid_def tlbvalid X2 X1, auto)
   
   have X6 : "... = (\<forall>i<(capacity tlb).
         (TLBEntryWellFormed tlb i) \<and> TLBENTRYWellFormed e \<and>
         TLBEntryConflictSet (entries
           \<lparr> capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(idx := e)\<rparr> i)
           \<lparr> capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(idx := e)\<rparr> \<subseteq> {i})"
     by(simp add:wf X3 )
   
   have X7:  "... =  (\<forall>i<(capacity tlb).
         TLBEntryConflictSet (entries 
          \<lparr>capacity = capacity tlb, wired = wired tlb,random = random tlb, entries = (entries tlb)(idx := e)\<rparr> i) 
          \<lparr>capacity = capacity tlb, wired = wired tlb,random = random tlb, entries = (entries tlb)(idx := e)\<rparr> \<subseteq> {i})"
     by(simp add:X4)
       
   with wf wr ir X0 X1 X2 X3 X4 X5 X6 X7 show " \<And>idx e t. t \<in> tlbwi idx e tlb \<Longrightarrow> TLBValid t"
     by(auto)          
 qed
  
   

lemma "\<And>idx. idx < (capacity tlb) \<Longrightarrow> \<exists>t \<in> (tlbwi idx e tlb) . tlbr idx t ={e}"
  by(simp add:tlbwi_def tlbr_def)

(* ------------------------------------------------------------------------- *)       
subsection "TLB Write Random"    
(* ------------------------------------------------------------------------- *)   

text "The MIPS TLB supports a random replacement."

definition tlbwr :: "TLBENTRY \<Rightarrow> MIPSTLB \<Rightarrow> MIPSTLB set" where
   "tlbwr e tlb = { t2  |t2  i. t2 \<in> {\<lparr> capacity = (capacity tlb),
                                  wired = (wired tlb),  
                                  random = random tlb,
                                  entries = (entries tlb)(i :=  e) \<rparr>} \<and> i \<in> (RandomIndexRange tlb)}"   

definition tlbwr2 :: "TLBENTRY \<Rightarrow> MIPSTLB \<Rightarrow> MIPSTLB set" where
   "tlbwr2 r t = { t2  |t2  i. t2 \<in> (tlbwi i r t) \<and> i \<in> (RandomIndexRange t)}"      
   
   
lemma MIPSTLB_randwr:
   "capacity tlb > 0 \<Longrightarrow> tlbwr e tlb = tlbwr2 e tlb"
  by(simp add:tlbwr_def tlbwr2_def RandomIndexRange_def tlbwi_def, auto)
         
   
text "If the TLB is in a valid state, and the entry to be inserted does not conflict
      with any of the existing entries, then the TLBWR operation returns a set of
      valid TLBs"
  
  
lemma TLBRandomUpdateValid :
  assumes tlbvalid: "TLBValid tlb"
    and wf: "TLBENTRYWellFormed e"
    and nc: "TLBEntryNoConflict e tlb"
  shows "(\<forall>t \<in> (tlbwr e tlb). TLBValid t)"
proof -
  
  from nc have NoConflictSet :
    "\<forall>i < capacity tlb. TLBEntryConflictSet e \<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(i := e)\<rparr> \<subseteq> {i}"
    by(simp add:TLBEntryNoConflict_def TLBEntryConflictSet_def, auto)
  
  from nc have nomatch: "\<forall>j<capacity tlb. \<not>EntryMatch e (entries tlb j)"
    by(simp add:TLBEntryNoConflict_def EntryMatch_commute)      
  
  have X0: "(\<forall>t \<in> (tlbwr e tlb). TLBValid t) = 
             (\<forall>i \<in> RandomIndexRange tlb. \<forall>t \<in>  {\<lparr> capacity = (capacity tlb),
                                  wired = (wired tlb),  
                                  random = random tlb,
                                  entries = (entries tlb)(i :=  e) \<rparr>}. TLBValid t )"
    by(simp add:tlbwr_def, auto)
    
  from tlbvalid have X1 : " ... =  (\<forall>i\<in>RandomIndexRange tlb.
        \<forall>t\<in>{\<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(i := e)\<rparr>}.
            (\<forall>i<capacity t. TLBEntryWellFormed t i \<and> TLBEntryConflictSet (entries t i) t \<subseteq> {i}))"
    by(simp only:TLBValid_def, auto)

  
  have X2 : " ... =  (\<forall>i\<in>RandomIndexRange tlb. \<forall>j<capacity tlb. 
        \<forall>t\<in>{\<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(i := e)\<rparr>}.
            (TLBEntryWellFormed t j \<and> TLBEntryConflictSet (entries t j) t \<subseteq> {j}))"
    by(auto)      
        
  have X3: " ... =  (\<forall>i\<in>RandomIndexRange tlb. \<forall>j<capacity tlb. 
            (TLBEntryWellFormed \<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(i := e)\<rparr> j 
          \<and> TLBEntryConflictSet (entries \<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(i := e)\<rparr> j) \<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(i := e)\<rparr> \<subseteq> {j}))"
    by(auto)
      
      
  have X4: " ... = (\<forall>i\<in>RandomIndexRange tlb. \<forall>j<capacity tlb. 
          (i = j \<longrightarrow>  (TLBEntryWellFormed \<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(i := e)\<rparr> j 
          \<and> TLBEntryConflictSet (entries \<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(i := e)\<rparr> i) \<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(i := e)\<rparr> \<subseteq> {i}) ) \<and>
          (i \<noteq> j \<longrightarrow>   (TLBEntryWellFormed \<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(i := e)\<rparr> j 
          \<and> TLBEntryConflictSet (entries \<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)\<rparr> j) \<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(i := e)\<rparr> \<subseteq> {j})))"
    by(auto)    
            
   from wf tlbvalid have X6: " ... =  (\<forall>i\<in>RandomIndexRange tlb.
        \<forall>j<capacity tlb.
           (i = j \<longrightarrow> TLBEntryConflictSet e \<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(i := e)\<rparr> \<subseteq> {i}) \<and>
           (i \<noteq> j \<longrightarrow> TLBEntryConflictSet (entries tlb j) \<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(i := e)\<rparr> \<subseteq> {j}))"
    by(simp add:TLBEntryWellFormed_def TLBValid_def)


  from NoConflictSet have X7 :  " ... =  (\<forall>i\<in>RandomIndexRange tlb.
        \<forall>j<capacity tlb.
           (i \<noteq> j \<longrightarrow> TLBEntryConflictSet (entries tlb j) \<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(i := e)\<rparr> \<subseteq> {j}))"
    by(auto)
      
  have X8: " ... =  (\<forall>i\<in>RandomIndexRange tlb.
        \<forall>j<capacity tlb.
           i \<noteq> j \<longrightarrow> {ia. (ia = i \<longrightarrow> i < capacity tlb \<and> EntryMatch e (entries tlb j)) \<and> 
                          (ia \<noteq> i \<longrightarrow> ia < capacity tlb \<and> EntryMatch (entries tlb ia) (entries tlb j))} \<subseteq> {j})"
    by(simp add:TLBEntryConflictSet_def)
  
  from nomatch have X9: " ... =  (\<forall>i\<in>RandomIndexRange tlb.
        \<forall>j<capacity tlb.
           i \<noteq> j \<longrightarrow> {ia. (ia = i \<longrightarrow> False) \<and> 
                          (ia \<noteq> i \<longrightarrow> ia < capacity tlb \<and> EntryMatch (entries tlb ia) (entries tlb j))} \<subseteq> {j})"
    by(auto)
      
  from tlbvalid have X10: " ... = True"
    by(simp add:TLBValid_def TLBEntryConflictSet_def, auto)


  from wf nomatch NoConflictSet nc tlbvalid X0 X1 X2 X3 X4 X6 X7 X8 X9 X10 show ?thesis 
    by(auto)
      
qed  
  

(* ========================================================================= *)  
section "Create a Decoding Net Node"
(* ========================================================================= *)  
  
text "Create the decoding net node. Each TLB entry has either zero, one or two mappings"
    
(* ------------------------------------------------------------------------- *) 
subsection "Helper Functions"
(* ------------------------------------------------------------------------- *) 
  
text{* Creates a mapspec list from the odd and even entries. We currently deal with two
       properties. If the write permissions dirty are set, then read and write requests
       can be handled. If it's not set then writes are not allowed *}

definition EntryPropertyMatch :: "TLBENTRYLO \<Rightarrow> addr \<Rightarrow> bool"
  where "EntryPropertyMatch e a = (if (d e) then 
                                     True  
                                   else 
                                     PWRITE \<notin> (snd a))"


    
definition EntryToMap :: "nodeid \<Rightarrow> TLBENTRY \<Rightarrow> addr \<Rightarrow> name set"
  where
    "EntryToMap nd e va =
      (if EntryIsValid0 e \<and> (EntryPropertyMatch (lo0 e) va) \<and> (fst va) \<in> EntryExtendedRange0 e then 
          {(nd, (EntryPA0 e + (((fst va) mod VASize) - EntryMinVA0 e)), (snd va))} else {}) \<union>
      (if EntryIsValid1 e \<and> (EntryPropertyMatch (lo1 e) va) \<and> (fst va) \<in> EntryExtendedRange1 e then
           {(nd, (EntryPA1 e + (((fst va) mod VASize) - EntryMinVA1 e)), (snd va))} else {})"      
    

(* ------------------------------------------------------------------------- *)  
subsection "Convert a TLB record to a node record"
(* ------------------------------------------------------------------------- *) 
  
text "For a successful conversion of all the TLB entries, we need to know the current valid
      ASID and to which node the translations should be carried out on."  
  

definition ConvertToNode :: "nodeid \<Rightarrow> MIPSTLB \<Rightarrow> node" where
  "ConvertToNode nid tlb =
    \<lparr> accept = {},
      translate = (\<lambda> a. \<Union>i<(capacity tlb). EntryToMap nid (entries tlb i) a) \<rparr>"

definition ConvertFromNode :: "nat \<Rightarrow> node \<Rightarrow> MIPSTLB set" where
  "ConvertFromNode nid n = (if (\<exists>tlb. ConvertToNode nid tlb = n) then 
        {SOME tlb. ConvertToNode nid tlb = n }  else {})"




  
(* ========================================================================= *)  
section "Proofs"
(* ========================================================================= *)  

(* ------------------------------------------------------------------------- *)  
subsection "TLB Write Order"
(* ------------------------------------------------------------------------- *)         

    
lemma NestedIfExchange : "\<And> i j. i \<noteq> j \<Longrightarrow>(if x = j then e else if x = i then
                                                  f else entries tlb x) =
                                           (if x = i then f else if x = j then
                                                  e else entries tlb x)"
  by(auto)
    
lemma
  assumes inrange: "i < (capacity tlb)" "j < (capacity tlb)"
      and notequal: "\<not>EntryMatch e f"
      and distinct : "i \<noteq> j"
      and notconflict: "\<not>TLBEntryNoConflict f tlb" "\<not>TLBEntryNoConflict e tlb"
  shows "{ConvertToNode nd tlb'' |tlb''. tlb'' \<in> \<Union>{tlbwi j e tlb' | tlb'. tlb' \<in> tlbwi i f tlb }} =
         {ConvertToNode nd tlb'' |tlb''. tlb'' \<in> \<Union>{tlbwi i f tlb' | tlb'. tlb' \<in> tlbwi j e tlb }}"
  apply(simp add:tlbwi_def inrange ConvertToNode_def)   
  apply(subst fun_upd_apply)
  apply(subst fun_upd_apply)    
  apply(simp add: NestedIfExchange distinct)      
  done
    
  
(* ------------------------------------------------------------------------- *)  
subsection "The TLB after initialization does not map anything"
(* ------------------------------------------------------------------------- *)  
            
lemma "ConvertToNode nd  (MIPSTLBInit c w tlb) = empty_node"
  by(simp add:empty_node_def ConvertToNode_def MIPSTLBInit_def EntryToMap_def 
              TLBEntryReset_def EntryIsValid0_def EntryIsValid1_def null_entry_lo_def 
              TLBENTRYLO.make_def TLBENTRY.make_def)
    
    
(* ------------------------------------------------------------------------- *)  
subsection "Lifting Result"
(* ------------------------------------------------------------------------- *)   

text "We now show that writing an entry in the TLB is equal to replace the map in 
      the model node."

definition replace_entry :: "nat \<Rightarrow> TLBENTRY \<Rightarrow> TLBENTRY \<Rightarrow> node \<Rightarrow> node"
  where
    "replace_entry nid e1 e2 n = n \<lparr>
      accept := accept n,
      translate := (\<lambda>va. (translate n va - (EntryToMap nid e1 va)) \<union> EntryToMap nid e2 va) \<rparr>"

    
lemma NonOverlapImpliesEntryToMap :
    "EntryExtendedRange (entries tlb i) \<inter> EntryExtendedRange (entries tlb j) = {} \<Longrightarrow> 
     ((EntryToMap nd (entries tlb i) va) \<inter>  (EntryToMap nd (entries tlb j) va)) = {}"
  by(auto simp:entry_extended_range_union EntryToMap_def)  

    
lemma NotEq:
  "\<And>i. \<And>j. i < (capacity tlb) \<Longrightarrow> j < (capacity tlb) \<Longrightarrow> i \<noteq> j \<Longrightarrow> TLBValidER tlb \<Longrightarrow> 
  ((EntryToMap nd (entries tlb j) va) \<inter>  (EntryToMap nd (entries tlb i) va)) = {}"
  by(simp add:TLBValidImpliesNotOverlap NonOverlapImpliesEntryToMap)


lemma TLB_to_node_lift :
  assumes inrange: "i < (capacity tlb)"
      and noconflict: "TLBEntryWriteable i e tlb"
      and valid : "TLBValidER tlb"
    shows "ConvertToNode nd ` (tlbwi i e tlb) = {replace_entry nd ((entries tlb) i) e (ConvertToNode nd tlb)}"
proof -
  from inrange
  have "tlbwi i e tlb = {\<lparr>capacity = capacity tlb, wired = wired tlb, random = random tlb, entries = (entries tlb)(i := e)\<rparr>}"
    by(simp add:tlbwi_def)
  hence "ConvertToNode nd ` (tlbwi i e tlb) =
         {\<lparr>accept = {}, translate = \<lambda>a. \<Union>x<(capacity tlb). EntryToMap nd (if x = i then e else entries tlb x) a\<rparr>}"
    by(simp add:ConvertToNode_def)
  also have "... = {\<lparr>accept = {},
          translate =
              \<lambda>va. (\<Union>i<(capacity tlb). EntryToMap nd (entries tlb i) va) -
                                    EntryToMap nd (entries tlb i) va \<union>
                                    EntryToMap nd e va\<rparr>}"
  proof -
    have "\<And>va. (\<Union>x<(capacity tlb). EntryToMap nd (if x = i then e else entries tlb x) va) =
               (\<Union>x<(capacity tlb). EntryToMap nd (entries tlb x) va) - EntryToMap nd (entries tlb i) va \<union>
               EntryToMap nd e va"
    proof -
      fix va
      from inrange
      have splitrange: "{..<(capacity tlb)} = {..<i} \<union> {i} \<union> {Suc i..<(capacity tlb)}"
        by(auto)
      hence "(\<Union>x<(capacity tlb). EntryToMap nd (if x = i then e else entries tlb x) va) =
             ((\<Union>x<i. EntryToMap nd (entries tlb x) va) \<union>
              (\<Union>x\<in>{Suc i..<(capacity tlb)}. EntryToMap nd (entries tlb x) va)) \<union> EntryToMap nd e va"
        by(simp add:ac_simps)
      also {
        have X: "\<And>i S. i \<notin> S \<Longrightarrow> i < (capacity tlb) \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> x < (capacity tlb)) \<Longrightarrow>
                 (\<Union>x\<in>S. EntryToMap nd (entries tlb x) va) \<inter> EntryToMap nd (entries tlb i) va = {}"
        proof -
          fix i::nat and S
          assume notin: "i \<notin> S"
             and iless: "i < (capacity tlb)"
             and Sless: "\<And>x. x \<in> S \<Longrightarrow> x < (capacity tlb)"
          {
            fix x
            assume xin: "x \<in> S"
            with notin Sless have "i \<noteq> x" "x < (capacity tlb)" by(auto)
            with iless valid
            have "EntryToMap nd (entries tlb x) va \<inter> EntryToMap nd (entries tlb i) va = {}"
              by(intro NotEq, auto)
          }
          thus "?thesis i S" by(auto)
        qed
        from inrange
        have "(\<Union>x<i. EntryToMap nd (entries tlb x) va) \<inter> EntryToMap nd (entries tlb i) va = {}"
          by(intro X, auto)
        moreover from inrange
        have "(\<Union>x\<in>{Suc i..<(capacity tlb)}. EntryToMap nd (entries tlb x) va) \<inter> EntryToMap nd (entries tlb i) va = {}"
          by(intro X, auto)
        moreover note splitrange
        ultimately
        have "(\<Union>x<i. EntryToMap nd (entries tlb x) va) \<union>
              (\<Union>x\<in>{Suc i..<(capacity tlb)}. EntryToMap nd (entries tlb x) va) =
              (\<Union>x<(capacity tlb). EntryToMap nd (entries tlb x) va) - EntryToMap nd (entries tlb i) va"
          by(simp add:Un_Diff Diff_triv)
      }
      finally
      show "(\<Union>x<(capacity tlb). EntryToMap nd (if x = i then e else entries tlb x) va) =
            (\<Union>x<(capacity tlb). EntryToMap nd (entries tlb x) va) - EntryToMap nd (entries tlb i) va \<union>
             EntryToMap nd e va" .
    qed
    thus ?thesis by(simp)
  qed
  also have "... = {replace_entry nd ((entries tlb) i) e (ConvertToNode nd tlb)}"
    by(simp add:ConvertToNode_def replace_entry_def)
  finally show ?thesis .
qed


lemma WellFormed :
  assumes valid : "TLBValid tlb"
  shows "wf_node (ConvertToNode nid tlb)"
  by(simp add:ConvertToNode_def EntryToMap_def wf_node_def)


(* ========================================================================= *)  
section "TLB Exceptions"
(* ========================================================================= *)   

text "An attempt to translate a mapped genaddress can result into one of four
      states: no entry present (REFILL), entry is invalid (INVALID) those
      won't translate the genaddress. The genaddress will be translated if
      the entry is in the modified state or there is no exception."  
  
datatype MIPSTLBEXN = EXNREFILL | EXNINVALID | EXNMOD | EXNOK

definition MIPSTLB_try_translate2 :: "MIPSTLB \<Rightarrow> ASID \<Rightarrow> VPN \<Rightarrow> MIPSTLBEXN"
  where "MIPSTLB_try_translate2 tlb as vpn =
    (if even vpn then 
      (if (\<exists>i < (capacity tlb). (EntryMatchVPNASID0 vpn as ((entries tlb) i) )) then
          (if (\<exists>i < (capacity tlb). (EntryMatchVPNASID0 vpn as ((entries tlb) i) ) 
                    \<and> EntryIsValid0 ((entries tlb) i))
           then EXNOK
           else EXNINVALID )
       else
       EXNREFILL)
    else (if (\<exists>i < (capacity tlb). (EntryMatchVPNASID1 vpn as ((entries tlb) i) )) then
      (if (\<exists>i < (capacity tlb). (EntryMatchVPNASID1 vpn as ((entries tlb) i) ) 
                    \<and> EntryIsValid1 ((entries tlb) i))
           then EXNOK
           else EXNINVALID )
       else
        EXNREFILL))"
    
definition MIPSTLB_try_translate :: "MIPSTLB \<Rightarrow> ASID \<Rightarrow> VPN \<Rightarrow> MIPSTLBEXN"
  where "MIPSTLB_try_translate tlb as vpn =
   (if (\<exists>i < (capacity tlb). (EntryMatchVPNASID vpn as ((entries tlb) i) )) then
     (if (\<exists>i < (capacity tlb). (EntryMatchVPNASID0 vpn as ((entries tlb) i) ) 
                                  \<and> EntryIsValid0 ((entries tlb) i)) then
      EXNOK
    else 
       (if (\<exists>i < (capacity tlb). (EntryMatchVPNASID1 vpn as ((entries tlb) i) ) 
                                   \<and> EntryIsValid1 ((entries tlb) i)) then 
       EXNOK 
       else EXNINVALID )
    )
    else EXNREFILL)"
    
 
    
lemma "\<forall>vpn as tlb. MIPSTLB_try_translate (MIPSR4600TLBinit w tlb) as vpn \<noteq>  EXNOK"    
  apply(simp add:MIPSTLB_try_translate_def)
  apply(simp add:MIPSR4600TLBinit_def MIPSTLBInit_def)
  apply(simp add:EntryIsValid0_def EntryIsValid1_def)
  apply(simp add:TLBEntryReset_def null_entry_lo_def TLBENTRY.make_def)
  done

lemma "\<And>as . \<forall>vpn tlb. as \<noteq> 0 \<Longrightarrow>  
             MIPSTLB_try_translate (MIPSR4600TLBinit w tlb) as vpn =  EXNREFILL"
  apply(simp add:MIPSTLB_try_translate_def)
  apply(simp add:MIPSR4600TLBinit_def MIPSTLBInit_def)
  apply(simp add:EntryIsValid0_def EntryIsValid1_def)
  apply(simp add:TLBEntryReset_def null_entry_lo_def TLBENTRY.make_def)
  apply(simp add:EntryMatchVPNASID_def EntryMatchVPNASID1_def EntryASIDMatchA_def 
                 EntryIsGlobal_def)
  done
    
lemma MIPSTLB_try_translate_exist_match :
    assumes translates:  "MIPSTLB_try_translate tlb as vpn \<noteq> EXNREFILL"
    shows "(\<exists>i<capacity tlb. EntryMatchVPNASID vpn as (entries tlb i))"
proof cases
  assume exist : "(\<exists>i<capacity tlb. EntryMatchVPNASID vpn as (entries tlb i))"
  then show ?thesis
  proof -
    from exist have X0: "MIPSTLB_try_translate tlb as vpn \<noteq> EXNREFILL"
      by(simp add:MIPSTLB_try_translate_def)
    from exist translates X0 show ?thesis 
      by(auto)
   qed
next
   assume nexist : "\<not>(\<exists>i<capacity tlb. EntryMatchVPNASID vpn as (entries tlb i))"
   then show ?thesis 
   proof -
     from nexist have X0: "MIPSTLB_try_translate tlb as vpn = EXNREFILL"
       by(simp add:MIPSTLB_try_translate_def)
     from nexist translates X0 show ?thesis 
       by(auto)
   qed
 qed
   
   
lemma MIPSTLB_fault_no_match :
  assumes fault: "MIPSTLB_try_translate tlb as vpn = EXNREFILL"
    shows "(\<forall>i<capacity tlb. \<not>EntryMatchVPNASID vpn as (entries tlb i))"
proof cases
  assume exist : "(\<exists>i<capacity tlb. EntryMatchVPNASID vpn as (entries tlb i))"
  then show ?thesis 
  proof -
    from exist have X0: "MIPSTLB_try_translate tlb as vpn \<noteq> EXNREFILL"
      by(simp add:MIPSTLB_try_translate_def)
    from exist fault X0 show ?thesis 
      by(auto)
  qed
next
  assume nexist : "\<not>(\<exists>i<capacity tlb. EntryMatchVPNASID vpn as (entries tlb i))"
  then show ?thesis 
  proof -
    from nexist have X0: "(\<forall>i<capacity tlb. \<not>EntryMatchVPNASID vpn as (entries tlb i))"
      by(auto)
    from nexist have X1: "MIPSTLB_try_translate tlb as vpn = EXNREFILL"
      by(auto simp add:MIPSTLB_try_translate_def)
    from nexist fault X0 X1 show ?thesis 
      by(auto)
  qed
qed
  
      
  
(* ========================================================================= *)  
section "Translate Function"
(* ========================================================================= *) 
  
definition TLBENTRY_translate_va :: "TLBENTRY \<Rightarrow> genaddr \<Rightarrow> nat set"
  where
    "TLBENTRY_translate_va e va =
      (if EntryIsValid0 e \<and> va \<in> EntryExtendedRange0 e then 
          {EntryPA0 e + ((va mod VASize) - EntryMinVA0 e)} else {}) \<union>
      (if EntryIsValid1 e \<and> va \<in> EntryExtendedRange1 e then
           {EntryPA1 e + ((va mod VASize) - EntryMinVA1 e)} else {})"  

definition TLBENTRY_translate2 :: "TLBENTRY \<Rightarrow> ASID \<Rightarrow> VPN \<Rightarrow> PFN set"
  where
    "TLBENTRY_translate2 e as vpn =
      (if EntryIsValid0 e \<and> EntryMatchVPNASID0 vpn as e then 
          {(pfn (lo0 e)) + (vpn - EntryMin4KVPN e)} else {}) \<union>
      (if EntryIsValid1 e \<and> EntryMatchVPNASID1 vpn as e then
           {(pfn (lo1 e)) +  (vpn - EntryMin4KVPN1 e)} else {})"      

    
definition TLBENTRY_translate :: "TLBENTRY \<Rightarrow> ASID \<Rightarrow> VPN \<Rightarrow> PFN set"
  where
    "TLBENTRY_translate e as vpn =
      (if EntryMatchVPNASID vpn as e then
       (if even vpn \<and> EntryIsValid0 e then
          {(pfn (lo0 e)) + (vpn - EntryMin4KVPN e)}
        else 
          (if odd vpn \<and> EntryIsValid1 e then
            {(pfn (lo1 e)) + (vpn - EntryMin4KVPN1 e)} 
           else {}) )
       else {})"    

    
text "The translate function of a reset entry is  always emtpy"
  
lemma TLBENTRY_translate_empty:
  "\<forall>i vpn as. TLBENTRY_translate (TLBEntryReset (i)) as vpn = {}"
  by(simp add:TLBEntryReset_def TLBENTRY.make_def null_entry_lo_def 
              TLBENTRY_translate_def EntryIsValid0_def EntryIsValid1_def)
    
    
definition MIPSTLB_translate :: "MIPSTLB \<Rightarrow> ASID \<Rightarrow> VPN \<Rightarrow> PFN set"
  where "MIPSTLB_translate tlb as vpn = {pa | i pa . 
                                                pa \<in> TLBENTRY_translate ((entries tlb) i) as vpn 
                                                \<and> i < (capacity tlb) }"  

text "The translate function of an initialized TLB is always emtpy"
  
lemma "MIPSTLB_translate (MIPSTLBInit c w tlb) as vpn = {}"
  by(simp add:MIPSTLB_translate_def MIPSTLBInit_def TLBENTRY_translate_empty)
  
    

lemma MIPSTLB_fault_no_translate:
  assumes fault: "MIPSTLB_try_translate t as vpn = EXNREFILL"
    and inrange : "i < (capacity t)"
    shows " (TLBENTRY_translate (entries t i) as vpn) = {}"
proof -
  from fault inrange have X0: "\<not>EntryMatchVPNASID vpn as (entries t i)"
    by(auto simp add:MIPSTLB_fault_no_match)
    
  from X0 show ?thesis by(simp add:TLBENTRY_translate_def)    
qed
      
    
    
(*<*)
end
(*>*)
