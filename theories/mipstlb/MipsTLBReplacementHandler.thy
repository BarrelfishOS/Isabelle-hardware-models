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
chapter "Exception Handler for the MIPS R4600"
(* ######################################################################### *)


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
  
    
definition MipsTLBPT_is_instance2 :: "MipsTLBPT \<Rightarrow> bool"
  where "MipsTLBPT_is_instance2 mt = (\<forall>i <  (capacity (tlb mt)). 
        MIPSPT_read (TLBENTRYHI.asid (hi (entries (tlb mt) i))) 
                    (vpn2 (hi (entries (tlb mt) i)))
                    (pte mt)       = (lo0(entries (tlb mt) i)) \<and> 
        MIPSPT_read (TLBENTRYHI.asid (hi (entries (tlb mt) i)))
                    (vpn2 (hi (entries (tlb mt) i)) + 1) 
                    (pte mt) = (lo1(entries (tlb mt) i)))"
    
definition MipsTLBPT_is_instance ::  "MipsTLBPT \<Rightarrow> bool"
  where "MipsTLBPT_is_instance mt = (\<forall>i <  (capacity (tlb mt)).
        entries (tlb mt) i = MIPSPT_mk_tlbentry (pte mt) (asid (hi (entries (tlb mt) i) ))  
                                                         (vpn2 (hi (entries (tlb mt) i) )))"


  
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
  
definition MipsTLBPT_fault2 :: "MipsTLBPT \<Rightarrow> ASID \<Rightarrow> VPN \<Rightarrow> MipsTLBPT set"
  where "MipsTLBPT_fault2  mtlb as vpn = 
      (if MIPSTLB_translate (tlb mtlb) vpn as  = {} then 
          MipsTLBPT_update_tlb mtlb as vpn
      else {mtlb})"      
    
definition MipsTLBPT_fault :: "MipsTLBPT \<Rightarrow> ASID \<Rightarrow> VPN \<Rightarrow> MipsTLBPT set"
  where "MipsTLBPT_fault  mtlb as vpn = 
      (if MIPSTLB_try_translate (tlb mtlb) as vpn = EXNREFILL then 
          MipsTLBPT_update_tlb mtlb as vpn
      else {mtlb})"      
    
    
lemma "\<forall>vpn as. MIPSTLB_try_translate (tlb m) as vpn \<noteq> EXNREFILL \<Longrightarrow>
            (\<forall>m2 \<in> MipsTLBPT_fault m as vpn. m = m2)"
  by(simp add: MipsTLBPT_fault_def)
        


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
 assumes valid: " MipsTLBPT_valid mpt "
    and inrange: "vpn < MIPSPT_EntriesMax"
    and inrange2: " ASIDValid as"
  shows "\<forall>m \<in> (MipsTLBPT_fault mpt as vpn).  MipsTLBPT_is_instance m" 
proof cases
  assume nfault: "MIPSTLB_try_translate (tlb mpt) as vpn = EXNREFILL"
  then show ?thesis 
  proof -
    from valid have isinstance:
      "MipsTLBPT_is_instance mpt"
      by(simp add:MipsTLBPT_valid_def)
        
        
    have  Z1: "(\<And>m i. i <  (capacity (tlb mpt)) \<Longrightarrow>
           (m = \<lparr>tlb = \<lparr>capacity = capacity (tlb mpt), 
                   wired = wired (tlb mpt), 
                   entries = (entries (tlb mpt))(i := MIPSPT_mk_tlbentry (pte mpt) as vpn) \<rparr>,
                  pte = (pte mpt) \<rparr> ) 
        \<Longrightarrow> ((entries (tlb m) i = MIPSPT_mk_tlbentry (pte m) (asid (hi (entries (tlb m) i) ))  
                                                           (vpn2 (hi (entries (tlb m) i) ))))

)"
      by(auto simp add:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)
      
    from nfault have X0:  "(\<forall>m \<in> (MipsTLBPT_fault mpt as vpn).  MipsTLBPT_is_instance m) =
                      (\<forall>m \<in> MipsTLBPT_update_tlb mpt as vpn .  MipsTLBPT_is_instance m)"
      by(simp add:MipsTLBPT_fault_def)
    
    have X1:  " ... = (\<forall>m\<in>{\<lparr>tlb = t, pte = pte mpt\<rparr> |t. t \<in> tlbwr (MIPSPT_mk_tlbentry (pte mpt) as vpn) (tlb mpt)}. MipsTLBPT_is_instance m)"
      by(simp only:MipsTLBPT_update_tlb_def)
    
    have X2:  " ... = (\<forall>m\<in>{\<lparr>tlb = t, pte = pte mpt\<rparr> |t.
                  t \<in> {t2 | t2 i. t2= \<lparr>capacity = capacity (tlb mpt), 
                                       wired = wired (tlb mpt), 
                                       entries = (entries (tlb mpt))(i := MIPSPT_mk_tlbentry (pte mpt) as vpn)\<rparr> \<and>
                            i \<in> RandomIndexRange (tlb mpt)}}.
        MipsTLBPT_is_instance m)"
      by(auto simp add:tlbwr_def)
        
    have X3:  " ... = (\<forall>i \<in> RandomIndexRange (tlb mpt). MipsTLBPT_is_instance (\<lparr>tlb = \<lparr>capacity = capacity (tlb mpt), 
                                       wired = wired (tlb mpt), 
                                       entries = (entries (tlb mpt))(i := MIPSPT_mk_tlbentry (pte mpt) as vpn)\<rparr>, pte = pte mpt\<rparr>))"
      by(auto)
        
        
    from isinstance X0 X1 X2 X3 Z1 show ?thesis 
        by(auto simp add:MipsTLBPT_is_instance_def)

  qed
next
 assume nfault: "MIPSTLB_try_translate (tlb mpt) as vpn \<noteq> EXNREFILL"
  then show ?thesis 
  proof -
    from valid have isinstance:
      "MipsTLBPT_is_instance mpt"
      by(simp add:MipsTLBPT_valid_def)
    
    from nfault have X1: "\<forall>m \<in> (MipsTLBPT_fault mpt as vpn). m = mpt"
      by(simp add:MipsTLBPT_fault_def)
    
    from isinstance X1 show ?thesis 
      by(auto)       
  qed   
qed 

  
  

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
      by(simp add:MIPSPT_TLBENTRY_wellformed)
        
  from inrange X3 X0 X5 have X4: "\<And>vpn as. \<forall>i<(capacity (tlb mpt)).
       \<forall>m \<in> MipsTLBPT_update_tlb mpt as vpn . TLBEntryWellFormed (tlb (m)) i"
    by(simp add:MipsTLBPT_update_tlb_def, auto)
  
  from valid inrange inrange2 alleven X0 X2 X3 X4 X5 
  show "\<And>vpn as.  \<forall>m \<in> MipsTLBPT_fault mpt as vpn .  TLBValid (tlb m)"
    by(simp add:MipsTLBPT_fault_def TLBValid_def, auto)
qed
  
lemma MipsTLBPT_keeps_valid :
    assumes valid: "\<And>mpt. MipsTLBPT_valid mpt "
    and inrange: "\<And>vpn. vpn < MIPSPT_EntriesMax"
    and inrange2: "\<And>as. ASIDValid as"
  shows "\<And>vpn mpt as.  \<forall>m \<in> MipsTLBPT_fault mpt as vpn .  MipsTLBPT_valid m"
  apply(subst MipsTLBPT_valid_def)
  apply(simp add:ball_conj_distrib)
  apply(simp add:MipsTLBT_keeps_ptvalid valid inrange inrange2 )
  apply(simp add:MipsTLBT_keeps_instance valid inrange inrange2)
  apply(simp add:MipsTLBT_keeps_TLBValid valid inrange inrange2 )
  done

lemma MipsTLBPT_instance_no_global:
  assumes  valid: "MipsTLBPT_valid m"
    and inrange : "i < (capacity (tlb m))"
  shows "\<not> EntryIsGlobal (entries (tlb m) i)"  
proof -
  from valid have inst :
      "MipsTLBPT_is_instance (m)"
    by(simp add:MipsTLBPT_valid_def)           
      
  from inst inrange have X0:  "
        entries (tlb m) i = MIPSPT_mk_tlbentry (pte m) (asid (hi (entries (tlb m) i) ))  
                                                       (vpn2 (hi (entries (tlb m) i) ))"
    by(simp add:MipsTLBPT_is_instance_def)
  
  from valid have X1: "\<not> EntryIsGlobal (MIPSPT_mk_tlbentry (pte m) (asid (hi (entries (tlb m) i) ))  
                                                     (vpn2 (hi (entries (tlb m) i) )))"      
    by(simp add:MIPSPT_TLBENTRY_not_global MipsTLBPT_valid_def )

  from X0 X1 show ?thesis
    by(auto)
qed
    
lemma MipsTLBPT_instance_entry_is_4k:
  assumes  valid: "MipsTLBPT_valid m"
     and inrange : "i < (capacity (tlb m))"
   shows "(mask (entries (tlb m) i)) = MASK4K" 
proof -
  from valid inrange have X0:
    "entries (tlb m) i = MIPSPT_mk_tlbentry (pte m) (asid (hi (entries (tlb m) i) ))  
                                                    (vpn2 (hi (entries (tlb m) i) ))"
    by(simp add: MipsTLBPT_valid_def MipsTLBPT_is_instance_def)
  
  have X1:
    "(mask (MIPSPT_mk_tlbentry (pte m) (asid (hi (entries (tlb m) i) ))  
                                       (vpn2 (hi (entries (tlb m) i))))) = MASK4K"
    by(simp add:MIPSPT_TLBENTRY_mask_is)    
  
  from X0 X1 show ?thesis 
    by(auto)
qed
      


  

   
lemma MipsTLBPT_match_is_equlas_even: 
  assumes inrange:  "i < capacity (tlb mtlb)"
    and match: "EntryMatchVPNASID vpn as (entries (tlb mtlb) i) "
    and  valid: "MipsTLBPT_valid mtlb"
    and veven : "even vpn"
  shows "entries (tlb mtlb) i = MIPSPT_mk_tlbentry (pte mtlb) as vpn"
proof -
    
  from valid have ptvalid :
    "MIPSPT_valid (pte mtlb)"
    by(simp add:MipsTLBPT_valid_def)       
  
  from valid have isinstance :
    "MipsTLBPT_is_instance (mtlb)"
    by(simp add:MipsTLBPT_valid_def)            

  from valid have tlbvalid :
    "TLBValid (tlb mtlb)"
    by(simp add:MipsTLBPT_valid_def)       
        
  from valid inrange match isinstance have X0: "(asid (hi (entries (tlb mtlb) i))) = as"
    by(simp add:EntryMatchVPNASID_def
                EntryASIDMatchA_def 
                MipsTLBPT_instance_no_global)
              
  from inrange tlbvalid have vpne2ven :
    "even (vpn2 (hi (entries (tlb mtlb) i)))"
    by(simp add:TLBValid_def TLBEntryWellFormed_def TLBENTRYWellFormed_def 
                TLBENTRYHIWellFormed_def VPN2Valid_def)
      
  from veven vpne2ven inrange valid match isinstance have  X1:
              "(vpn2 (hi (entries (tlb mtlb) i))) = vpn"
    by(auto simp add:EntryMatchVPNASID_def EntryVPNMatchV_def EntryMin4KVPN_def 
                     EntryMax4KVPN_def MipsTLBPT_instance_entry_is_4k num_4k_pages_def
                     even_vpn_compare)
           
   from isinstance have X3:
     "(\<forall>i <  (capacity (tlb mtlb)).
        entries (tlb mtlb) i = 
            MIPSPT_mk_tlbentry (pte mtlb) (asid (hi (entries (tlb mtlb) i) ))  
                                          (vpn2 (hi (entries (tlb mtlb) i) )))"
     by(simp add:MipsTLBPT_is_instance_def)
      
   from X3 inrange have X4 : 
     "entries (tlb mtlb) i = 
            MIPSPT_mk_tlbentry (pte mtlb) (asid (hi (entries (tlb mtlb) i) ))  
                                          (vpn2 (hi (entries (tlb mtlb) i) ))"
     by(auto)
       
   from X0 X1 X3 X4 show ?thesis
     by(auto)
qed

lemma MipsTLBPT_match_is_equlas_odd: 
  assumes inrange:  "i < capacity (tlb mtlb)"
    and match: "EntryMatchVPNASID vpn as (entries (tlb mtlb) i) "
    and  valid: "MipsTLBPT_valid mtlb"
    and vodd : "odd vpn"
  shows "entries (tlb mtlb) i = MIPSPT_mk_tlbentry (pte mtlb) as vpn"
proof -
    
  from valid have ptvalid :
    "MIPSPT_valid (pte mtlb)"
    by(simp add:MipsTLBPT_valid_def)       
  
  from valid have isinstance :
    "MipsTLBPT_is_instance (mtlb)"
    by(simp add:MipsTLBPT_valid_def)            

  from valid have tlbvalid :
    "TLBValid (tlb mtlb)"
    by(simp add:MipsTLBPT_valid_def)       
        
  from valid inrange match isinstance have X0: "(asid (hi (entries (tlb mtlb) i))) = as"
    by(simp add:EntryMatchVPNASID_def
                EntryASIDMatchA_def 
                MipsTLBPT_instance_no_global)
              
  from inrange tlbvalid have vpne2ven :
    "even (vpn2 (hi (entries (tlb mtlb) i)))"
    by(simp add:TLBValid_def TLBEntryWellFormed_def TLBENTRYWellFormed_def 
                TLBENTRYHIWellFormed_def VPN2Valid_def)
      
  from vodd vpne2ven inrange valid match isinstance have  X1:
              "(vpn2 (hi (entries (tlb mtlb) i))) = (vpn - 1)"
    by(auto simp add:EntryMatchVPNASID_def EntryVPNMatchV_def EntryMin4KVPN_def 
                     EntryMax4KVPN_def MipsTLBPT_instance_entry_is_4k num_4k_pages_def
                     even_vpn_compare)
           
   from inrange isinstance have X3:
     "entries (tlb mtlb) i = 
           MIPSPT_mk_tlbentry (pte mtlb) (asid (hi (entries (tlb mtlb) i) ))  
                                         (vpn2 (hi (entries (tlb mtlb) i) ))"
     by(simp add:MipsTLBPT_is_instance_def)

   from vodd have X4:  "MIPSPT_mk_tlbentry (pte mtlb) as (vpn - 1) = MIPSPT_mk_tlbentry (pte mtlb) as vpn"
     by(simp add:MIPSPT_mk_tlbentry_def)
       
   from X0 X1 X3 X4 show ?thesis
     by(auto)
qed  
  
  
lemma MipsTLBPT_match_is_equlas: 
  assumes inrange:  "i < capacity (tlb mtlb)"
    and match: "EntryMatchVPNASID vpn as (entries (tlb mtlb) i) "
    and  valid: "MipsTLBPT_valid mtlb"
  shows "entries (tlb mtlb) i = MIPSPT_mk_tlbentry (pte mtlb) as vpn"
proof cases
  assume veven: "even vpn"
  then show ?thesis 
    by(simp add:MipsTLBPT_match_is_equlas_even inrange match valid)
next
  assume vodd: "odd vpn"
  then show ?thesis
    by(simp add:MipsTLBPT_match_is_equlas_odd inrange match valid)
qed
  
lemma MipsTLBPT_no_fault_entry_exist :
assumes  valid: "MipsTLBPT_valid mtlb"
    and translates : "MIPSTLB_try_translate (tlb mtlb) as vpn \<noteq> EXNREFILL"
  shows  "(\<exists>i < (capacity (tlb mtlb)). (entries (tlb mtlb) i) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn))"
proof -
  from valid have inst:
    "MipsTLBPT_is_instance mtlb"
    by(simp add:MipsTLBPT_valid_def)
  from valid have ptvalid :
    "MIPSPT_valid (pte mtlb)"
    by(simp add:MipsTLBPT_valid_def)
  from valid have tlbvalid:
    "TLBValid (tlb mtlb)"
    by(simp add:MipsTLBPT_valid_def)
   
  from inst have inst2: 
    "(\<forall>i<capacity (tlb mtlb). 
        entries (tlb mtlb) i = MIPSPT_mk_tlbentry (pte mtlb) 
                                                  (asid (hi (entries (tlb mtlb) i))) 
                                                  (vpn2 (hi (entries (tlb mtlb) i))))"
    by(simp add:MipsTLBPT_is_instance_def)
  
  have doesmatch: "EntryMatchVPNASID vpn as  (MIPSPT_mk_tlbentry (pte mtlb) as vpn)"
    by(simp add:MIPSPT_TLBENTRY_match)      
      
  from translates have matchexist:
     "(\<exists>i<capacity (tlb mtlb). EntryMatchVPNASID vpn as (entries (tlb mtlb) i))"
    by(simp add:MIPSTLB_try_translate_exist_match)
       
      
  from valid have X0: "\<And>i as vpn. i < capacity (tlb mtlb) 
          \<and> EntryMatchVPNASID vpn as (entries (tlb mtlb) i) \<longrightarrow>  entries (tlb mtlb) i = MIPSPT_mk_tlbentry (pte mtlb) as vpn"
    by(simp add:MipsTLBPT_match_is_equlas)
      
  from matchexist X0 show ?thesis by(auto)  
qed
  

lemma  XYZ:
  assumes inrange: " i < capacity (tlb mtlb)"
    and  valid: "MipsTLBPT_valid mtlb"
    and  inotmatch: " i \<noteq> (SOME j. j < (capacity (tlb mtlb)) 
                \<and> ((entries (tlb mtlb) j)) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn))"
  shows "TLBENTRY_translate (entries (tlb mtlb) i) as vpn = {}"
proof cases
  assume fault: "MIPSTLB_try_translate (tlb mtlb) as vpn = EXNREFILL"
  then show ?thesis 
  proof -
    from fault inrange have nomatch:
      "\<not>EntryMatchVPNASID vpn as (entries (tlb mtlb) i)"
      by(simp add:MIPSTLB_fault_no_match)
    from nomatch show ?thesis
      by(simp add:TLBENTRY_translate_def)
  qed      
next
  assume nofault: "MIPSTLB_try_translate (tlb mtlb) as vpn \<noteq> EXNREFILL"
  then show ?thesis 
  proof -
    
    from valid have tlbvalid:
      "TLBValid (tlb mtlb)"
      by(simp add:MipsTLBPT_valid_def)

    from valid have inst:
      "MipsTLBPT_is_instance mtlb"        
      by(simp add:MipsTLBPT_valid_def)
            
    have mask4k2: 
       "(\<forall>i < (capacity (tlb mtlb)). mask ((entries (tlb mtlb)) i) = MASK4K)"
    proof -
      from inst have Z0:
        "(\<forall>i < (capacity (tlb mtlb)). mask ((entries (tlb mtlb)) i) = MASK4K) = 
            (\<forall>i < (capacity (tlb mtlb)). mask (MIPSPT_mk_tlbentry (pte mtlb) (asid (hi (entries (tlb mtlb) i))) (vpn2 (hi (entries (tlb mtlb) i)))) = MASK4K)"
        by(simp add:MipsTLBPT_is_instance_def)
          
      from Z0 show ?thesis 
        by(auto simp:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)
    qed
    
    from nofault  valid have exist:
      "(\<exists>j. j < (capacity (tlb mtlb)) \<and>
          (entries (tlb mtlb) j) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn))"     
      by(simp add:MipsTLBPT_no_fault_entry_exist)        
        
    from exist have match: "
        entries (tlb mtlb) 
            (SOME j. j < (capacity (tlb mtlb)) 
                \<and> ((entries (tlb mtlb) j)) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn))
           = (MIPSPT_mk_tlbentry (pte mtlb) as vpn)"
       by(simp add:some_eq_ex[symmetric])
    
    from exist have ir2: " (SOME j. j < (capacity (tlb mtlb)) 
                \<and> ((entries (tlb mtlb) j)) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn)) <  (capacity (tlb mtlb)) "
      by(simp add:some_eq_ex[symmetric])
          
    have  X0: "EntryMatchVPNASID vpn as (entries (tlb mtlb) (SOME j. j < (capacity (tlb mtlb)) 
                \<and> ((entries (tlb mtlb) j)) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn)))"
      by(simp add:match MIPSPT_TLBENTRY_match)
    
    have X1: "(SOME j. j < capacity (tlb mtlb) \<and> entries (tlb mtlb) j = MIPSPT_mk_tlbentry (pte mtlb) as vpn) \<noteq> i"
      by(auto simp add:inotmatch)
        
    from tlbvalid inrange ir2 mask4k2 X0 X1 have nomatch :
      "\<not> EntryMatchVPNASID vpn as (entries (tlb mtlb) i)"
      by(simp add:TLBValid_implies_no_other_match)
  
  from nomatch show ?thesis 
    by(auto simp:TLBENTRY_translate_def)  
  qed
qed


  
lemma MipsTLBPT_translate_is:
  assumes inrange: "vpn < MIPSPT_EntriesMax"
    and inrange2: "as < ASIDMax"
    and  valid: "MipsTLBPT_valid mtlb"
  shows "MipsTLBPT_translate mtlb as vpn = 
           (if (v ((entry (pte mtlb)) vpn as)) then {(pfn ((entry  (pte mtlb)) vpn as))} else {})" 
proof cases
  assume fault: "MIPSTLB_try_translate (tlb mtlb) as vpn = EXNREFILL"
  then show ?thesis 
  proof -
    from valid have tlbvalid : "TLBValid (tlb mtlb)"
      by(simp add:MipsTLBPT_valid_def)
        
    from fault have X0: "MipsTLBPT_translate mtlb as vpn = 
      \<Union>{MIPSTLB_translate (tlb m) as vpn |m. m \<in> MipsTLBPT_update_tlb mtlb as vpn}"
      by(simp add:MipsTLBPT_translate_def MipsTLBPT_fault_def)

    have X1: " ... = \<Union>{MIPSTLB_translate (tlb m) as vpn |m. m \<in> {\<lparr>tlb = t, pte = pte mtlb\<rparr> |t. t \<in> tlbwr (MIPSPT_mk_tlbentry (pte mtlb) as vpn) (tlb mtlb)}}"
      by(simp only:MipsTLBPT_update_tlb_def)
    
    have X2: " ... = \<Union>{MIPSTLB_translate (tlb m) as vpn |m.
       \<exists>t. m = \<lparr>tlb = t, pte = pte mtlb\<rparr> \<and>
           (\<exists>i. t = \<lparr>capacity = capacity (tlb mtlb), wired = wired (tlb mtlb), entries = (entries (tlb mtlb))(i := MIPSPT_mk_tlbentry (pte mtlb) as vpn)\<rparr> \<and> i \<in> RandomIndexRange (tlb mtlb))}"
      by(simp add:tlbwr_def)
    
    have X3: " ... = \<Union>{MIPSTLB_translate (tlb m) as vpn |m.
       \<exists>i. m = \<lparr>tlb = \<lparr>capacity = capacity (tlb mtlb), wired = wired (tlb mtlb), entries = (entries (tlb mtlb))(i := MIPSPT_mk_tlbentry (pte mtlb) as vpn)\<rparr>, pte = pte mtlb\<rparr> 
            \<and> i \<in> RandomIndexRange (tlb mtlb)}"
      by(auto)
    
    have X4: " ... =  \<Union>{{pa| pa j. pa \<in> TLBENTRY_translate (entries (tlb m) j) as vpn \<and> j < capacity (tlb m)} |m i.
       m = \<lparr>tlb = \<lparr>capacity = capacity (tlb mtlb), wired = wired (tlb mtlb), entries = (entries (tlb mtlb))(i := MIPSPT_mk_tlbentry (pte mtlb) as vpn)\<rparr>, pte = pte mtlb\<rparr> \<and>
           i \<in> RandomIndexRange (tlb mtlb)}"
      by(simp add:MIPSTLB_translate_def)
        
    have X5: "... = \<Union>{ {pa| pa j. pa \<in> TLBENTRY_translate (entries (tlb m) j) as vpn \<and> j < capacity (tlb m) \<and> i = j} \<union> {pa| pa j. pa \<in> TLBENTRY_translate (entries (tlb m) j) as vpn \<and> j < capacity (tlb m) \<and> i \<noteq> j} |m i.
       m = \<lparr>tlb = \<lparr>capacity = capacity (tlb mtlb), wired = wired (tlb mtlb), entries = (entries (tlb mtlb))(i := MIPSPT_mk_tlbentry (pte mtlb) as vpn)\<rparr>, pte = pte mtlb\<rparr> \<and>
           i \<in> RandomIndexRange (tlb mtlb)}"
      by(blast)
    
    have X6:  " ... = \<Union>{ {pa| pa j. pa \<in> TLBENTRY_translate (MIPSPT_mk_tlbentry (pte mtlb) as vpn) as vpn \<and> j < capacity (tlb m) \<and> i = j}
       \<union> {pa| pa j. pa \<in> TLBENTRY_translate (entries (tlb m) j) as vpn \<and> j < capacity (tlb m) \<and> i \<noteq> j} |m i.
       m = \<lparr>tlb = \<lparr>capacity = capacity (tlb mtlb), wired = wired (tlb mtlb), entries = (entries (tlb mtlb))(i := MIPSPT_mk_tlbentry (pte mtlb) as vpn)\<rparr>, pte = pte mtlb\<rparr> \<and>
           i \<in> RandomIndexRange (tlb mtlb)}"
      by(auto)

    have X7:   " ... = \<Union>{{pa \<in> TLBENTRY_translate (MIPSPT_mk_tlbentry (pte mtlb) as vpn) as vpn. i < capacity (tlb mtlb)} \<union>
       {pa | pa j. j \<noteq> i \<and>  j < capacity (tlb mtlb) \<and> pa \<in> TLBENTRY_translate (entries (tlb mtlb) j) as vpn} |
       i. i \<in> RandomIndexRange (tlb mtlb)}"
      by(auto)

     have X8:  " ... = {pa | pa i. pa \<in> TLBENTRY_translate (MIPSPT_mk_tlbentry (pte mtlb) as vpn) as vpn \<and>  i \<in> RandomIndexRange (tlb mtlb) \<and> i<capacity (tlb mtlb)} \<union>
    {pa. \<exists>j i. i \<in> RandomIndexRange (tlb mtlb) \<and> j \<noteq> i \<and> j < capacity (tlb mtlb) \<and> pa \<in> TLBENTRY_translate (entries (tlb mtlb) j) as vpn}"
       by(auto)
         
    from fault have X9:  " ... =  {pa | pa i. pa \<in> TLBENTRY_translate (MIPSPT_mk_tlbentry (pte mtlb) as vpn) as vpn \<and>  i \<in> RandomIndexRange (tlb mtlb) \<and> i<capacity (tlb mtlb)}"
      by(auto simp add:MIPSTLB_fault_no_translate)
        
    have X10: " ... =  {pa | pa i. pa \<in> TLBENTRY_translate (MIPSPT_mk_tlbentry (pte mtlb) as vpn) as vpn \<and> i \<in> RandomIndexRange (tlb mtlb)}"
      by(auto simp:RandomIndex_in_capacity)
    
     from tlbvalid have X11 : " ... =   (if (v ((entry  (pte mtlb)) vpn as)) then {(pfn ((entry   (pte mtlb)) vpn as))} else {})"
       by(auto simp add:MIPSPT_TLBENTRY_translate_is RandomIndexRange_def TLBValid_def)
   
   from fault X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 show ?thesis
     by(auto)
  qed
next
  assume nofault: "MIPSTLB_try_translate (tlb mtlb) as vpn \<noteq> EXNREFILL"
  then show ?thesis 
  proof -

    from nofault inrange inrange2 valid have exist:
          "(\<exists>j. j < (capacity (tlb mtlb)) \<and>
              (entries (tlb mtlb) j) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn))"     
      by(simp add:MipsTLBPT_no_fault_entry_exist)
     
    from exist have match: "
        entries (tlb mtlb) 
            (SOME j. j < (capacity (tlb mtlb)) 
                \<and> ((entries (tlb mtlb) j)) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn))
           = (MIPSPT_mk_tlbentry (pte mtlb) as vpn)"
       by(simp add:some_eq_ex[symmetric])
    
    from exist have ir2: " (SOME j. j < (capacity (tlb mtlb)) 
                \<and> ((entries (tlb mtlb) j)) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn)) <  (capacity (tlb mtlb)) "
      by(simp add:some_eq_ex[symmetric])
    
    
    from nofault have X0:  "MipsTLBPT_translate mtlb as vpn =  MIPSTLB_translate (tlb mtlb) as vpn"
      by(simp add:MipsTLBPT_translate_def MipsTLBPT_fault_def)

    have X1 : " ... =  {pa | pa i.  i < capacity (tlb mtlb) 
                          \<and> pa \<in> TLBENTRY_translate (entries (tlb mtlb) i) as vpn}"
      by(auto simp add:MIPSTLB_translate_def)
        
    have X2 : " ... = {pa | pa i.  i < capacity (tlb mtlb) \<and> i = (SOME j. j < (capacity (tlb mtlb)) 
                \<and> ((entries (tlb mtlb) j)) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn))
                          \<and> pa \<in> TLBENTRY_translate (entries (tlb mtlb) i) as vpn}  \<union>
                      {pa | pa i.  i < capacity (tlb mtlb) \<and> i \<noteq> (SOME j. j < (capacity (tlb mtlb)) 
                \<and> ((entries (tlb mtlb) j)) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn))
                          \<and> pa \<in> TLBENTRY_translate (entries (tlb mtlb) i) as vpn}"
      by(auto)
        
    
    
     from match have X3: " ... =  {pa | pa i.  i < capacity (tlb mtlb) \<and> i = (SOME j. j < (capacity (tlb mtlb)) 
                \<and> ((entries (tlb mtlb) j)) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn))
                          \<and> pa \<in> TLBENTRY_translate  (MIPSPT_mk_tlbentry (pte mtlb) as vpn) as vpn}  \<union>
                      {pa | pa i.  i < capacity (tlb mtlb) \<and> i \<noteq> (SOME j. j < (capacity (tlb mtlb)) 
                \<and> ((entries (tlb mtlb) j)) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn))
                          \<and> pa \<in> TLBENTRY_translate (entries (tlb mtlb) i) as vpn}"
      by(auto)
    
    from ir2 have X4:  " ... =  {pa | pa i. i = (SOME j. j < (capacity (tlb mtlb)) 
                \<and> ((entries (tlb mtlb) j)) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn))
                          \<and> pa \<in> TLBENTRY_translate  (MIPSPT_mk_tlbentry (pte mtlb) as vpn) as vpn}  \<union>
                      {pa | pa i.  i < capacity (tlb mtlb) \<and> i \<noteq> (SOME j. j < (capacity (tlb mtlb)) 
                \<and> ((entries (tlb mtlb) j)) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn))
                          \<and> pa \<in> TLBENTRY_translate (entries (tlb mtlb) i) as vpn}"
      by(auto)
        
     from valid have X5:  " ... =  {pa | pa i. i = (SOME j. j < (capacity (tlb mtlb)) 
                \<and> ((entries (tlb mtlb) j)) = (MIPSPT_mk_tlbentry (pte mtlb) as vpn))
                          \<and> pa \<in> TLBENTRY_translate  (MIPSPT_mk_tlbentry (pte mtlb) as vpn) as vpn}"
       by(auto simp add:XYZ)
         
     have X6: " ... =   (if (v ((entry (pte mtlb)) vpn as)) then {(pfn ((entry  (pte mtlb)) vpn as))} else {})"
       by(simp add:MIPSPT_TLBENTRY_translate_is)
    
    
     from X0 X1 X2 X3 X4 X5 X6 match show ?thesis
       by(auto)
  qed
qed    
    
end 