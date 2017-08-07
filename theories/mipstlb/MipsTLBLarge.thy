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
theory MipsTLBLarge
  imports Main Set MipsTLB MipsTLBPageTable MipsTLBReplacementHandler
begin
(*>*)

  
(* ========================================================================= *)  
section "A large TLB"
(* ========================================================================= *) 

text "The number of TLB entries for the large TLB"  

text "Each page table entry will be in one entry pair of the large TLB.
      Thus for each ASID there are MIPSPT_EntriesMax / 2 entries."    
  
definition MipsTLBLarge_EntryPairs :: nat
  where "MipsTLBLarge_EntryPairs = MIPSPT_EntriesMax div 2"
  
definition MipsTLBLarge_Entries :: nat
  where "MipsTLBLarge_Entries = MipsTLBLarge_EntryPairs * ASIDMax"
        
    
definition MipsTLBLarge_mk_idx :: "ASID \<Rightarrow> VPN \<Rightarrow> nat"
  where "MipsTLBLarge_mk_idx as vpn = (as * MipsTLBLarge_EntryPairs) + (vpn div 2)"

  
definition MipsTLBLarge_create :: "MIPSPT \<Rightarrow> MIPSTLB"
  where "MipsTLBLarge_create pt =  \<lparr> 
        capacity = MipsTLBLarge_Entries, 
        wired    = 0, 
        entries  = (\<lambda>n. MIPSPT_mk_tlbentry pt (n div MipsTLBLarge_EntryPairs)
                                              ((n mod MipsTLBLarge_EntryPairs) * 2))\<rparr>"

    
    
lemma "\<forall>x < MipsTLBLarge_Entries. (x mod 256) \<le> ASIDMax"
  by(auto simp:ASIDMax_def)

lemma "\<forall>x < MipsTLBLarge_Entries. (x div 256) \<le> MIPSPT_EntriesMax"
  by(auto simp:ASIDMax_def MipsTLBLarge_Entries_def MIPSPT_EntriesMax_def 
               MipsTLBLarge_EntryPairs_def)

lemma "\<forall>x < MipsTLBLarge_Entries. (x div MipsTLBLarge_EntryPairs) < ASIDMax"
  by(auto simp:ASIDMax_def MipsTLBLarge_EntryPairs_def MipsTLBLarge_Entries_def
               MIPSPT_EntriesMax_def)

lemma "\<forall>x < MipsTLBLarge_Entries. (x mod MipsTLBLarge_EntryPairs) < MIPSPT_EntriesMax"
  by(auto simp:ASIDMax_def MipsTLBLarge_Entries_def MIPSPT_EntriesMax_def 
               MipsTLBLarge_EntryPairs_def)
             
             
    
(* ========================================================================= *)  
section "Valid"
(* ========================================================================= *)     

lemma MipsTLBLarge_vpn_even: 
  "\<forall>n. even  (n mod MipsTLBLarge_EntryPairs * 2)"  
  by(auto)
  
lemma MipsTLBLarge_asid_valid :
  "\<forall>x < MipsTLBLarge_Entries. 
     ASIDValid (x div MipsTLBLarge_EntryPairs)"
  by(auto simp:ASIDValid_def MipsTLBLarge_mk_idx_def ASIDMin_def ASIDMax_def 
              MipsTLBLarge_Entries_def MipsTLBLarge_EntryPairs_def 
              MIPSPT_EntriesMax_def)
     
lemma MipsTLBLarge_vpn_valid :
  "\<forall>x < MipsTLBLarge_Entries.  
   (x mod MipsTLBLarge_EntryPairs) * 2 < MIPSPT_EntriesMax"
  by(auto simp:MIPSPT_EntriesMax_def MipsTLBLarge_Entries_def
    MipsTLBLarge_EntryPairs_def ASIDMax_def)

lemma MipsTLBLarge_entry_wellformed :    
  assumes ptvalid : "\<And>pt. MIPSPT_valid pt"                  
  shows "\<And>pt. \<forall>x < MipsTLBLarge_Entries.   
        TLBENTRYWellFormed (MIPSPT_mk_tlbentry pt (x div MipsTLBLarge_EntryPairs)
                                              (((x mod (MipsTLBLarge_EntryPairs)) * 2)))"
  by(simp add:MIPSPT_TLBENTRYWellFormed MipsTLBLarge_asid_valid 
              MipsTLBLarge_vpn_valid ptvalid)

lemma foo :
  shows "\<And>i. i <MipsTLBLarge_Entries \<Longrightarrow> (i div MipsTLBLarge_EntryPairs) < ASIDMax"
  by(auto simp: MipsTLBLarge_EntryPairs_def MipsTLBLarge_Entries_def MIPSPT_EntriesMax_def 
                ASIDMax_def)
                        
lemma 
  assumes inrangei : "\<And>i. i <MipsTLBLarge_Entries"
     and  inrangej : "\<And>j. j <MipsTLBLarge_Entries"
     and ptvalid : "\<And>pt. MIPSPT_valid pt"
   shows "\<And>i j. j <MipsTLBLarge_Entries \<Longrightarrow> i <MipsTLBLarge_Entries \<Longrightarrow> i = j \<longleftrightarrow> 
       EntryASIDMatch (MIPSPT_mk_tlbentry pt (j div MipsTLBLarge_EntryPairs) (j mod MipsTLBLarge_EntryPairs * 2))
                      (MIPSPT_mk_tlbentry pt (i div MipsTLBLarge_EntryPairs) (i mod MipsTLBLarge_EntryPairs * 2))"
  apply(simp add:EntryASIDMatch_def MIPSPT_asid_is MIPSPT_valid_entries_not_global ptvalid)
  apply(simp add:MipsTLBLarge_Entries_def)
  apply(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def)
  apply(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def MipsTLBLarge_Entries_def ASIDMax_def)
  apply(auto)  
  oops  
    
lemma 
  assumes inrangei : "\<And>i. i <MipsTLBLarge_Entries"
     and  inrangej : "\<And>j. j <MipsTLBLarge_Entries"
     and ptvalid : "\<And>pt. MIPSPT_valid pt"
   shows "\<And>i j. i = j \<Longrightarrow> 
       EntryASIDMatch (MIPSPT_mk_tlbentry pt (i) (vpn))
                      (MIPSPT_mk_tlbentry pt (j) (vpn'))"
  by(simp add:EntryASIDMatch_def MIPSPT_asid_is)
  
            
    
lemma XY :
  assumes inrangei : "\<And>i. i <MipsTLBLarge_Entries"
     and  inrangej : "\<And>j. j <MipsTLBLarge_Entries"
     and ptvalid : "\<And>pt. MIPSPT_valid pt"
   shows "\<And>i j. i = j \<longleftrightarrow> 
       EntryVPNMatch (MIPSPT_mk_tlbentry pt (as) (j * 2))
                     (MIPSPT_mk_tlbentry pt (as2) (i * 2))"
  by(simp add:EntryVPNMatch_def EntryRange_def EntryMinVA_def EntryMaxVA_def 
              EntrySize_def MIPSPT_VPN2_is MIPSPT_EntryMask_is KB_def,
              auto)  
    
  
lemma MipsTLBLarge_valid :
  assumes ptvalid : "\<And>pt. MIPSPT_valid pt"
  shows "\<And>pt. TLBValid (MipsTLBLarge_create pt)"
  apply(simp add:TLBValid_def MipsTLBLarge_create_def TLBMaximumWired_def)
  apply(simp add:TLBEntryWellFormed_def)
  apply(simp add:MipsTLBLarge_entry_wellformed ptvalid)
  apply(simp add:TLBEntryConflictSet_def)
  apply(simp add:EntryMatch_def EntryASIDMatch_def MIPSPT_valid_entries_not_global ptvalid)
  apply(simp add:MIPSPT_asid_is)
  apply(simp add:EntryVPNMatch_def MIPSPT_TLBENTRY_Range)
  apply(simp add:MipsTLBLarge_Entries_def)
  
  apply(auto)
    oops

(* ========================================================================= *)  
section "No faults"
(* ========================================================================= *)     

  
text "For the VPN and ASID in the valid range, there won't be any faults
      occurring in the large TLB."
  
lemma MipsTLBLarge_match_exists_even:
  assumes inrange: " vpn < MIPSPT_EntriesMax"
      and inrange2: "ASIDValid as"
      and valid: "MIPSPT_valid pt"
      and evenvpn: "even vpn"
  shows "\<exists>i<MipsTLBLarge_Entries. EntryMatchVPNASID0 vpn as (entries (MipsTLBLarge_create pt) i)"  
proof -

  obtain i
    where idx: "i =  (as * MipsTLBLarge_EntryPairs + (vpn div 2 ))" 
    by(auto)
    
  from inrange inrange2 idx have  ir2 : "i <  MipsTLBLarge_Entries"
  proof -
    have X0: "i < MipsTLBLarge_Entries = (i < MipsTLBLarge_EntryPairs * ASIDMax)"
      by(simp add:MipsTLBLarge_Entries_def)
    
    from inrange2 have X1: "as < ASIDMax"
      by(simp add:ASIDValid_def)
    
    from X1 inrange have X2:
      "((as::nat) * MipsTLBLarge_EntryPairs + ((vpn::nat) div 2))
            <  (MipsTLBLarge_EntryPairs * ASIDMax) "
      by(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def ASIDMax_def)

    show ?thesis
      apply(simp add:idx)
      apply(simp add:MipsTLBLarge_Entries_def)
      apply(simp add:X1 inrange X2)
      done   
  qed
  
  show ?thesis
  proof (rule exI[where x = i])
    
    from inrange inrange2 have X0 :
       "as * MipsTLBLarge_EntryPairs + vpn div 2 < MipsTLBLarge_Entries"
      by(simp add:MipsTLBLarge_EntryPairs_def MipsTLBLarge_Entries_def 
                  MIPSPT_EntriesMax_def ASIDMax_def ASIDValid_def ASIDMin_def)
      
    
    have X1:  
   "(i < MipsTLBLarge_Entries \<and> EntryMatchVPNASID0 vpn as (entries (MipsTLBLarge_create pt) i)) = 
     ((as * MipsTLBLarge_EntryPairs + vpn div 2) < MipsTLBLarge_Entries \<and>
             EntryMatchVPNASID0 vpn as 
            (entries (MipsTLBLarge_create pt) (as * MipsTLBLarge_EntryPairs + vpn div 2)))"
      by(simp add:idx)
        
    have X2:
     "... = EntryMatchVPNASID0 vpn as 
           (entries (MipsTLBLarge_create pt) (as * MipsTLBLarge_EntryPairs + vpn div 2))"
      by(simp add:X0)
        
    from valid have X3: 
     "... = (EntryVPNMatchV0 vpn (MIPSPT_mk_tlbentry pt 
             ((as * MipsTLBLarge_EntryPairs + vpn div 2) div MipsTLBLarge_EntryPairs)
             (vpn div 2 mod MipsTLBLarge_EntryPairs * 2)) \<and>
                (as * MipsTLBLarge_EntryPairs + vpn div 2) div MipsTLBLarge_EntryPairs = as)"
      apply(simp add:EntryMatchVPNASID0_def MipsTLBLarge_create_def EntryASIDMatchA_def)
      apply(simp add:MIPSPT_valid_entries_not_global MIPSPT_asid_is)
      done
    
    have X4:
     "... = (vpn div 2 mod MipsTLBLarge_EntryPairs * 2 \<le> vpn \<and> 
            vpn < Suc (vpn div 2 mod MipsTLBLarge_EntryPairs * 2) \<and> 
            (as * MipsTLBLarge_EntryPairs + vpn div 2) div MipsTLBLarge_EntryPairs = as)"
      apply(simp add:EntryVPNMatchV0_def EntryMin4KVPN_def num_4k_pages_def EntryMin4KVPN1_def)
      apply(simp add:MIPSPT_VPN2_is MIPSPT_EntryMask_is)
      done
 
        
    from inrange inrange2 evenvpn have X5:  "... = True"
      by(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def)
          
    from X0 X1 X2 X3 X4 X5
    show " i < MipsTLBLarge_Entries \<and> EntryMatchVPNASID0 vpn as (entries (MipsTLBLarge_create pt) i)"
      by(auto)
  qed
qed


  
lemma MipsTLBLarge_match_exists_odd:
  assumes inrange: " vpn < MIPSPT_EntriesMax"
      and inrange2: "ASIDValid as"
      and valid: "MIPSPT_valid pt"
      and oddvpn: "odd vpn"
  shows "\<exists>i<MipsTLBLarge_Entries. EntryMatchVPNASID1 vpn as (entries (MipsTLBLarge_create pt) i)"  
proof -

  obtain i
    where idx: "i =  (as * MipsTLBLarge_EntryPairs + ((vpn - 1) div 2 ))" 
    by(auto)
    
  from inrange inrange2 idx have  ir2 : "i <  MipsTLBLarge_Entries"
  proof -
    have X0: "i < MipsTLBLarge_Entries = (i < MipsTLBLarge_EntryPairs * ASIDMax)"
      by(simp add:MipsTLBLarge_Entries_def)
    
    from inrange2 have X1: "as < ASIDMax"
      by(simp add:ASIDValid_def)
    
    from X1 inrange have X2:
      "((as::nat) * MipsTLBLarge_EntryPairs + (((vpn::nat) - Suc 0) div 2)) 
           <  (MipsTLBLarge_EntryPairs * ASIDMax) "
      by(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def ASIDMax_def)
        
    show ?thesis
      apply(simp add:idx)
      apply(simp add:MipsTLBLarge_Entries_def)
      apply(simp add:X1 inrange X2)
      done   
  qed
  
  show ?thesis
  proof (rule exI[where x = i])
    
    from inrange inrange2 have X0 :
     "as * MipsTLBLarge_EntryPairs + (vpn - Suc 0) div 2 < MipsTLBLarge_Entries"
      by(simp add:MipsTLBLarge_EntryPairs_def MipsTLBLarge_Entries_def
                  MIPSPT_EntriesMax_def ASIDMax_def ASIDValid_def ASIDMin_def)
      
    
    have X1: 
    "(i < MipsTLBLarge_Entries \<and> EntryMatchVPNASID1 vpn as (entries (MipsTLBLarge_create pt) i)) = 
         ((as * MipsTLBLarge_EntryPairs + (vpn -1) div 2) <  MipsTLBLarge_Entries 
            \<and> EntryMatchVPNASID1 vpn as (entries (MipsTLBLarge_create pt) 
                      (as * MipsTLBLarge_EntryPairs + (vpn - 1) div 2)))"
      by(simp add:idx)
        
    have X2: 
      "... = EntryMatchVPNASID1 vpn as (entries (MipsTLBLarge_create pt) 
                  (as * MipsTLBLarge_EntryPairs + (vpn - 1) div 2))"
      by(simp add:X0)
        
    from valid have X3:
      "... = (EntryVPNMatchV1 vpn (MIPSPT_mk_tlbentry pt 
              ((as * MipsTLBLarge_EntryPairs + (vpn - Suc 0) div 2) div MipsTLBLarge_EntryPairs) 
              ((vpn - Suc 0) div 2 mod MipsTLBLarge_EntryPairs * 2)) \<and>
     (as * MipsTLBLarge_EntryPairs + (vpn -1) div 2) div MipsTLBLarge_EntryPairs = as)"
      apply(simp add:EntryMatchVPNASID1_def MipsTLBLarge_create_def EntryASIDMatchA_def)
      apply(simp add:MIPSPT_valid_entries_not_global MIPSPT_asid_is)
      done
    
    have X4: 
    "... = (Suc ((vpn - Suc 0) div 2 mod MipsTLBLarge_EntryPairs * 2) \<le> vpn \<and>
      vpn \<le> Suc ((vpn - Suc 0) div 2 mod MipsTLBLarge_EntryPairs * 2) \<and>
      (as * MipsTLBLarge_EntryPairs + (vpn - Suc 0) div 2) div MipsTLBLarge_EntryPairs = as) "
      apply(simp add:EntryVPNMatchV1_def EntryMax4KVPN_def num_4k_pages_def EntryMin4KVPN1_def)
      apply(simp add:MIPSPT_VPN2_is MIPSPT_EntryMask_is)
      done
        
    from inrange inrange2 oddvpn have X5:  "... = True"
      by(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def)
          
    from X0 X1 X2 X3 X4 X5
    show " i < MipsTLBLarge_Entries \<and> EntryMatchVPNASID1 vpn as (entries (MipsTLBLarge_create pt) i)"
      by(auto)
  qed
qed


  
lemma MipsTLBLarge_no_faults:
assumes valid: "MIPSPT_valid pt"
    and inrange: " vpn < MIPSPT_EntriesMax"
    and inrange2: "ASIDValid as"
  shows "MIPSTLB_try_translate (MipsTLBLarge_create pt) as vpn \<noteq> EXNREFILL"
proof (cases)
  assume vpneven : "even vpn"
  show ?thesis
  proof -
            
    have capacity: "capacity (MipsTLBLarge_create pt) = MipsTLBLarge_Entries"
      by(simp add:MipsTLBLarge_create_def)    
        
    from vpneven capacity have X1: "MIPSTLB_try_translate (MipsTLBLarge_create pt) as vpn = 
      ( if \<exists>i<MipsTLBLarge_Entries. EntryMatchVPNASID0 vpn as (entries (MipsTLBLarge_create pt) i)
        then if \<exists>i<MipsTLBLarge_Entries. EntryMatchVPNASID0 vpn as (entries (MipsTLBLarge_create pt) i) 
                  \<and> EntryIsValid0 (entries (MipsTLBLarge_create pt) i) then EXNOK
             else EXNINVALID
        else EXNREFILL)"
      by(simp add:MIPSTLB_try_translate_def)
    
     from inrange inrange2 valid vpneven have  X2: "... = 
       (if \<exists>i<MipsTLBLarge_Entries. EntryMatchVPNASID0 vpn as (entries (MipsTLBLarge_create pt) i) 
                  \<and> EntryIsValid0 (entries (MipsTLBLarge_create pt) i) then EXNOK
             else EXNINVALID)"
      by(auto simp:MipsTLBLarge_match_exists_even)
    
    have X3: "... \<noteq> EXNREFILL"
      by(auto)
        
    from X1 X2 X3 show ?thesis
      by(auto)
         
  qed
next 
  assume vpnodd: "odd vpn"
  show ?thesis 
  proof -
     have capacity: "capacity (MipsTLBLarge_create pt) = MipsTLBLarge_Entries"
       by(simp add:MipsTLBLarge_create_def)
                   
  from vpnodd capacity have X1: "MIPSTLB_try_translate (MipsTLBLarge_create pt) as vpn = 
      ( if \<exists>i<MipsTLBLarge_Entries. EntryMatchVPNASID1 vpn as (entries (MipsTLBLarge_create pt) i)
        then if \<exists>i<MipsTLBLarge_Entries. EntryMatchVPNASID1 vpn as (entries (MipsTLBLarge_create pt) i) 
                  \<and> EntryIsValid1 (entries (MipsTLBLarge_create pt) i) then EXNOK
             else EXNINVALID
        else EXNREFILL)"
      by(simp add:MIPSTLB_try_translate_def)
                
     from inrange inrange2 valid vpnodd have X2: "... = 
        (if \<exists>i<MipsTLBLarge_Entries. EntryMatchVPNASID1 vpn as (entries (MipsTLBLarge_create pt) i)
                 \<and> EntryIsValid1 (entries (MipsTLBLarge_create pt) i) then EXNOK else EXNINVALID)"
       by(auto simp:MipsTLBLarge_match_exists_odd)    
    
    have X3: "... \<noteq> EXNREFILL"
      by(auto)
        
    from X1 X2 X3 show ?thesis
      by(auto)
  qed   
qed


    

end