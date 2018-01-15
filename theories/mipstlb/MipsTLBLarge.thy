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
chapter "A large, software-loaded TLB"
(* ######################################################################### *)
  
(*<*)  
theory MipsTLBLarge
  imports Main Set MipsTLB MipsTLBPageTable
begin
(*>*)
  
text "The TLB model presented in this Theory is based on the MIPS R4600 TLB
      model presented in the MIPSTLB theory. "
  


(* ========================================================================= *)  
section "The Large TLB: A tlb with as many entries as there are pages"
(* ========================================================================= *) 
  
text "For each ASID and VPN there will be an entry in this TLB. Because the
      MIPS TLB has entry pairs, there will be MIPSPTEntriesMax / 2 entries.
      Therefore, the Large TLB will have MIPSPTEntriesMax / 2 * ASIDMax entries"
  
definition MipsTLBLarge_EntryPairs :: nat
  where "MipsTLBLarge_EntryPairs = MIPSPT_EntriesMax div 2"
  
definition MipsTLBLarge_Entries :: nat
  where "MipsTLBLarge_Entries = MipsTLBLarge_EntryPairs * ASIDMax"
        
 
(* ------------------------------------------------------------------------- *)
subsection "Index calculation"    
(* ------------------------------------------------------------------------- *)    

text "When populating the large TLB, each entry is being put into a particular
      position depending on its ASID an VPN. The index consists of the
      concatenation ASID|VPN."
  
definition MipsTLBLarge_mk_idx :: "ASID \<Rightarrow> VPN \<Rightarrow> nat"
  where "MipsTLBLarge_mk_idx as vpn = (as * MipsTLBLarge_EntryPairs) + (vpn div 2)"    

definition MipsTLBLarge_mk_idx2 :: "ASID \<times> VPN \<Rightarrow> nat"
  where "MipsTLBLarge_mk_idx2 asvpn = 
      ((fst asvpn) * MipsTLBLarge_EntryPairs)  + ((snd asvpn) div 2)"

definition MipsTLBLarge_idx2asid :: "nat \<Rightarrow> ASID"
  where "MipsTLBLarge_idx2asid idx = (idx div MipsTLBLarge_EntryPairs)"

definition MipsTLBLarge_idx2vpn :: "nat \<Rightarrow> ASID"
  where "MipsTLBLarge_idx2vpn idx = (idx mod MipsTLBLarge_EntryPairs) * 2"

definition MipsTLBLarge_idx2vpnasid :: "nat \<Rightarrow> ASID \<times> VPN"
  where "MipsTLBLarge_idx2vpnasid idx = (MipsTLBLarge_idx2asid idx, 
                                         MipsTLBLarge_idx2vpn idx)"

    
text "We show that for all valid indices there will be valid ASID and VPN
      and vice versa."

lemma MipsTLBLarge_mk_idx_in_num_entries:
   "\<forall>as < ASIDMax. \<forall>vpn < MIPSPT_EntriesMax. 
      MipsTLBLarge_mk_idx as vpn < MipsTLBLarge_Entries"
  by(simp add:MIPSPT_EntriesMax_def ASIDMax_def MipsTLBLarge_mk_idx_def 
              MipsTLBLarge_EntryPairs_def MipsTLBLarge_Entries_def, auto)
    
lemma MipsTLBLarge_asid_valid:
   "\<forall>x < MipsTLBLarge_Entries. ASIDValid (MipsTLBLarge_idx2asid x)"
  by(auto simp:MipsTLBLarge_Entries_def ASIDValid_def ASIDMax_def ASIDMin_def
               MipsTLBLarge_idx2asid_def MipsTLBLarge_EntryPairs_def 
               MIPSPT_EntriesMax_def)

lemma MipsTLBLarge_vpn_valid :
   "\<forall>x < MipsTLBLarge_Entries. (MipsTLBLarge_idx2vpn x) < MIPSPT_EntriesMax"
  by(auto simp:MipsTLBLarge_idx2vpn_def MipsTLBLarge_Entries_def 
               MIPSPT_EntriesMax_def MipsTLBLarge_EntryPairs_def)

text "Given we deal with entry pairs, the VPN of the index will always be even.
"
lemma MipsTLBLarge_vpn_even:
  "\<forall>x < MipsTLBLarge_Entries. even (MipsTLBLarge_idx2vpn x)"
  by(simp add:MipsTLBLarge_idx2vpn_def)

    
lemma MipsTLBLarge_index_differ :
  assumes inrangei : "i < MipsTLBLarge_Entries"
      and inrangej : "j < MipsTLBLarge_Entries"
    shows " (i \<noteq> j) \<longleftrightarrow> \<not>( (MipsTLBLarge_idx2asid i = MipsTLBLarge_idx2asid j) \<and>
                          ( MipsTLBLarge_idx2vpn i = MipsTLBLarge_idx2vpn j))"
proof 
  assume noteq: "i \<noteq> j"

  obtain vpn as vpn2 as2 
    where AS:  "as = MipsTLBLarge_idx2asid i" 
      and VPN: "vpn = MipsTLBLarge_idx2vpn i"
      and AS2:  "as2 = MipsTLBLarge_idx2asid j" 
      and VPN2: "vpn2 = MipsTLBLarge_idx2vpn j"
    by(auto)    
    
  from AS VPN AS2 VPN2 noteq have X0:
      "(\<not> (MipsTLBLarge_idx2asid i = MipsTLBLarge_idx2asid j
               \<and> MipsTLBLarge_idx2vpn i = MipsTLBLarge_idx2vpn j)) = 
       (\<not> (as = as2 \<and> vpn = vpn2))"
    by(auto)

  have X1:  " ... = (as \<noteq> as2) \<or> (vpn \<noteq> vpn2)"
    by(auto)
      
  from VPN inrangei have IR: "vpn < MIPSPT_EntriesMax"
    by(simp add:MIPSPT_EntriesMax_def MipsTLBLarge_idx2vpn_def 
                MipsTLBLarge_EntryPairs_def)
      
  from VPN2 inrangej have IR2:  "vpn2 < MIPSPT_EntriesMax"
    by(simp add:MIPSPT_EntriesMax_def MipsTLBLarge_idx2vpn_def 
                MipsTLBLarge_EntryPairs_def)
    
  from VPN AS have X2: "i = MipsTLBLarge_mk_idx as vpn"
    by(simp add:MipsTLBLarge_mk_idx_def MipsTLBLarge_idx2asid_def 
                MipsTLBLarge_idx2vpn_def)
  
  from VPN2 AS2 have X3: "j = MipsTLBLarge_mk_idx as2 vpn2"
    by(simp add:MipsTLBLarge_mk_idx_def MipsTLBLarge_idx2asid_def 
                MipsTLBLarge_idx2vpn_def)
  
  from IR IR2 VPN VPN2 AS AS2 have  X4: 
    "(as \<noteq> as2) \<Longrightarrow> (MipsTLBLarge_mk_idx as vpn \<noteq> MipsTLBLarge_mk_idx as2 vpn2)"
    by(simp add:MipsTLBLarge_mk_idx_def MipsTLBLarge_EntryPairs_def
                MIPSPT_EntriesMax_def)
      
  from noteq X0 X1 X2 X3 X4 show 
    " \<not> (MipsTLBLarge_idx2asid i = MipsTLBLarge_idx2asid j
             \<and> MipsTLBLarge_idx2vpn i = MipsTLBLarge_idx2vpn j)"
    by(auto)
next
  assume noteq2: "\<not> (MipsTLBLarge_idx2asid i = MipsTLBLarge_idx2asid j 
                    \<and> MipsTLBLarge_idx2vpn i = MipsTLBLarge_idx2vpn j)"
  
  obtain vpn as vpn2 as2
    where AS:  "as = MipsTLBLarge_idx2asid i" 
      and VPN: "vpn = MipsTLBLarge_idx2vpn i"
      and AS2:  "as2 = MipsTLBLarge_idx2asid j" 
      and VPN2: "vpn2 = MipsTLBLarge_idx2vpn j"
    by(auto)
  
  from AS VPN AS2 VPN2 noteq2 have X0:
      "(\<not> (MipsTLBLarge_idx2asid i = MipsTLBLarge_idx2asid j
            \<and> MipsTLBLarge_idx2vpn i = MipsTLBLarge_idx2vpn j)) = 
       (\<not> (as = as2 \<and> vpn = vpn2))"
    by(auto)

  have X1:  " ... = (as \<noteq> as2) \<or> (vpn \<noteq> vpn2)"
    by(auto)
      
  from VPN inrangei have IR: "vpn < MIPSPT_EntriesMax"
    by(simp add:MIPSPT_EntriesMax_def MipsTLBLarge_idx2vpn_def 
                MipsTLBLarge_EntryPairs_def)
      
  from VPN2 inrangej have IR2:  "vpn2 < MIPSPT_EntriesMax"
    by(simp add:MIPSPT_EntriesMax_def MipsTLBLarge_idx2vpn_def 
                MipsTLBLarge_EntryPairs_def)
    
  from VPN AS have X2: "i = MipsTLBLarge_mk_idx as vpn"
    by(simp add:MipsTLBLarge_mk_idx_def MipsTLBLarge_idx2asid_def 
                MipsTLBLarge_idx2vpn_def)
  
  from VPN2 AS2 have X3: "j = MipsTLBLarge_mk_idx as2 vpn2"
    by(simp add:MipsTLBLarge_mk_idx_def MipsTLBLarge_idx2asid_def 
                MipsTLBLarge_idx2vpn_def)
  
  from IR IR2 VPN VPN2 AS AS2 have  X4: 
    "(as \<noteq> as2) \<Longrightarrow> (MipsTLBLarge_mk_idx as vpn \<noteq> MipsTLBLarge_mk_idx as2 vpn2)"
    by(simp add:MipsTLBLarge_mk_idx_def MipsTLBLarge_EntryPairs_def 
                MIPSPT_EntriesMax_def)
  
  from noteq2 X0 X1 X2 X3 X4 show "i \<noteq> j" 
    by(auto)  
qed
 
    
(* ------------------------------------------------------------------------- *)
subsection "TLB Definition"    
(* ------------------------------------------------------------------------- *)      

text "We create and initialize the large TLB based on the MIPS model with
      enough entries to hold all pages. We use the index to VPN/ASID 
      conversion functions from above. Additinally, we set the number of
      wired entries to the number of entries the TLB has "
  
definition MipsTLBLarge_create :: "MIPSPT \<Rightarrow> MIPSTLB"
  where "MipsTLBLarge_create pt =  \<lparr> 
        capacity = MipsTLBLarge_Entries, 
        wired    = 0, 
        random = MipsTLBLarge_Entries - 1,
        entries  = (\<lambda>n. MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid n)
                                              (MipsTLBLarge_idx2vpn n))\<rparr>"

    
(* ========================================================================= *)  
section "Matching of Large TLB Entries"
(* ========================================================================= *)    
  
text "In order for an entry to match, it must match with the VPN and ASID. 
      For this we provide a set of lemmas on when the they match."  
  
(* ------------------------------------------------------------------------- *)
subsection "ASIDs of Two Entries"    
(* ------------------------------------------------------------------------- *)                 
                
text "If the two indices are equal, then the two ASID parts must be equal."  
  
lemma MipsTLBLarge_idx_asid_equal:
  "\<And>i j.  (i = j)  \<Longrightarrow> MipsTLBLarge_idx2asid i = MipsTLBLarge_idx2asid j"
  by(auto)

    
text "If the ASID parts of the indices patch, then their created entry
      must match on the ASID."    
    
lemma MipsTLBLarge_idx_asid_match :
  assumes inrangei : "i <MipsTLBLarge_Entries"
     and  inrangej : "j <MipsTLBLarge_Entries"
     and ptvalid : "MIPSPT_valid pt"
   shows " MipsTLBLarge_idx2asid j = MipsTLBLarge_idx2asid i \<longleftrightarrow> 
       EntryASIDMatch (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid j) 
                                             (MipsTLBLarge_idx2vpn j))
                      (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid i) 
                                             (MipsTLBLarge_idx2vpn i))"
proof -
  from ptvalid have X0:
    "\<And>i j. EntryASIDMatch (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid j) 
                                                 (MipsTLBLarge_idx2vpn j))
                          (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid i)
                                                 (MipsTLBLarge_idx2vpn i)) = 
     (asid (hi (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid j)
                                      (MipsTLBLarge_idx2vpn j))) = 
      asid (hi (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid i) 
                                      (MipsTLBLarge_idx2vpn i))))"
    by(simp add:EntryASIDMatch_def MIPSPT_TLBENTRY_not_global)
  
  have X1: 
    "\<And>i j.  (asid (hi (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid j) 
                                             (MipsTLBLarge_idx2vpn j))) = 
              asid (hi (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid i)
                                             (MipsTLBLarge_idx2vpn i)))) 
                      = ((MipsTLBLarge_idx2asid j) = (MipsTLBLarge_idx2asid i))"
    by(simp add:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)
  
  from X0 X1 show 
    "\<And>i j. MipsTLBLarge_idx2asid j = MipsTLBLarge_idx2asid i \<longleftrightarrow> 
       EntryASIDMatch (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid j) 
                                             (MipsTLBLarge_idx2vpn j))
                      (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid i) 
                                             (MipsTLBLarge_idx2vpn i))"
     by(auto)
  qed 

    
text "Likewise if the two indices are the same then the entry must match on the ASID"
    
lemma MipsTLBLarge_idx_equal_asid_match :
  assumes inrangei : "\<And>i. i <MipsTLBLarge_Entries"
     and  inrangej : "\<And>j. j <MipsTLBLarge_Entries"
     and ptvalid : "\<And>pt. MIPSPT_valid pt"
     shows "\<And>i j pt. (i = j) \<Longrightarrow>
            EntryASIDMatch (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid j) 
                                                  (MipsTLBLarge_idx2vpn j))
                           (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid i)
                                                  (MipsTLBLarge_idx2vpn i))"
proof -
  have X0: "\<And>i j. (i = j) \<Longrightarrow> (MipsTLBLarge_idx2asid i = MipsTLBLarge_idx2asid j)"
    by(auto)
  
  from inrangei inrangej ptvalid X0 show 
     "\<And>i j pt. (i = j) \<Longrightarrow>
       EntryASIDMatch (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid j)
                                             (MipsTLBLarge_idx2vpn j))
                      (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid i)
                                             (MipsTLBLarge_idx2vpn i))"
    by(auto)
qed


lemma 
   shows "\<And>i j. i = j \<Longrightarrow> 
       EntryASIDMatch (MIPSPT_mk_tlbentry pt (i) (vpn))
                      (MIPSPT_mk_tlbentry pt (j) (vpn'))"
  by(simp add:EntryASIDMatch_def MIPSPT_TLBENTRY_asid_is)  
  

(* ------------------------------------------------------------------------- *)
subsection "VPNs of Two Entries"    
(* ------------------------------------------------------------------------- *)       

lemma MipsTLBLarge_idx_vpn_equal:
  "\<And>i j.  i <MipsTLBLarge_Entries \<and>  j <MipsTLBLarge_Entries \<and>  (i = j)  \<Longrightarrow>
              MipsTLBLarge_idx2vpn i = MipsTLBLarge_idx2vpn j"
  by(auto)
  
lemma MipsTLBLarge_idx_vpn_match :
  assumes inrangei : "i <MipsTLBLarge_Entries"
     and  inrangej : "j <MipsTLBLarge_Entries"
   shows " 
       MipsTLBLarge_idx2vpn j = MipsTLBLarge_idx2vpn i = 
       EntryVPNMatch (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid j) 
                                            (MipsTLBLarge_idx2vpn j))
                     (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid i) 
                                            (MipsTLBLarge_idx2vpn i))"
proof
  assume eq: "MipsTLBLarge_idx2vpn j = MipsTLBLarge_idx2vpn i"
  show "EntryVPNMatch (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid j) 
                                             (MipsTLBLarge_idx2vpn j))
                      (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid i) 
                                             (MipsTLBLarge_idx2vpn i))"
  proof -
    from eq have X0:
      "EntryVPNMatch (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid j)
                                            (MipsTLBLarge_idx2vpn j))
                     (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid i) 
                                            (MipsTLBLarge_idx2vpn i)) =
       EntryVPNMatch (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid j) 
                                            (MipsTLBLarge_idx2vpn j))
                     (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid i) 
                                            (MipsTLBLarge_idx2vpn j))"
      by(auto)
      
   from inrangej have X1:" ... = True"
     by(auto simp add:EntryVPNMatch_def MIPSPT_TLBENTRY_range_even
                      MipsTLBLarge_vpn_even)
      
   from  X0 X1 show ?thesis
      by(auto)

  qed
next
  assume eq2: "EntryVPNMatch (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid j) 
                                                    (MipsTLBLarge_idx2vpn j))
                             (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid i) 
                                                    (MipsTLBLarge_idx2vpn i))"
  show "MipsTLBLarge_idx2vpn j = MipsTLBLarge_idx2vpn i"
  proof -
    from eq2 inrangei inrangej have X0: "
      EntryVPNMatch (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid j) 
                                           (MipsTLBLarge_idx2vpn j))
                    (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid i) 
                                           (MipsTLBLarge_idx2vpn i)) = 
      ({x. MipsTLBLarge_idx2vpn j * 4096 \<le> x 
          \<and> x < 8192 + MipsTLBLarge_idx2vpn j * 4096} 
        \<inter> {x. MipsTLBLarge_idx2vpn i * 4096 \<le> x 
          \<and> x < 8192 + MipsTLBLarge_idx2vpn i * 4096} \<noteq> {})"
      by(simp add:EntryVPNMatch_def MIPSPT_TLBENTRY_range_even MipsTLBLarge_vpn_even)

    have X1:
      " ... = ({x. MipsTLBLarge_idx2vpn j * 4096 \<le> x 
                  \<and> MipsTLBLarge_idx2vpn i * 4096 \<le> x
                  \<and> x < 8192 + MipsTLBLarge_idx2vpn j * 4096 
                  \<and> x < 8192 + MipsTLBLarge_idx2vpn i * 4096} \<noteq> {})"
              by(auto)
        
    from inrangei inrangej X0 X1 eq2 show ?thesis 
      by(auto simp:MipsTLBLarge_vpn_even MipsTLBLarge_idx2vpn_def)
    qed
qed
  

lemma XY :
  assumes inrangei : "\<And>i. i <MipsTLBLarge_Entries"
     and  inrangej : "\<And>j. j <MipsTLBLarge_Entries"
     and ptvalid : "\<And>pt. MIPSPT_valid pt"
   shows "\<And>i j. i = j \<longleftrightarrow> 
       EntryVPNMatch (MIPSPT_mk_tlbentry pt (as) (j * 2))
                     (MIPSPT_mk_tlbentry pt (as2) (i * 2))"
  by(simp add:EntryVPNMatch_def EntryRange_def EntryMinVA_def EntryMaxVA_def 
              EntrySize_def MIPSPT_TLBENTRY_vpn2_is_even MIPSPT_TLBENTRY_mask_is KB_def,
              auto)    
    
(* ------------------------------------------------------------------------- *)
subsection "Two different entries do not match"    
(* ------------------------------------------------------------------------- *)  
            
            
lemma MipsTLBLarge_idx_no_match :
  assumes inrangei : "i <MipsTLBLarge_Entries"
     and  inrangej : "j <MipsTLBLarge_Entries" 
     and valid : "MIPSPT_valid pt"
     and noteq: "i \<noteq> j"
   shows   "EntryMatch (entries (MipsTLBLarge_create pt) j) 
                       (entries (MipsTLBLarge_create pt) i) = False"            
proof -
  
  from inrangei inrangej noteq have X0: 
      "((MipsTLBLarge_idx2asid i \<noteq> MipsTLBLarge_idx2asid j) \<or>
        (MipsTLBLarge_idx2vpn i \<noteq> MipsTLBLarge_idx2vpn j))"
    by(simp add:MipsTLBLarge_index_differ)
  
  from inrangei inrangej valid have X1:
    "(MipsTLBLarge_idx2asid j \<noteq> MipsTLBLarge_idx2asid i) \<longrightarrow>
        \<not> EntryASIDMatch (entries (MipsTLBLarge_create pt) j) 
                         (entries (MipsTLBLarge_create pt) i)"
    by(simp add:MipsTLBLarge_create_def MipsTLBLarge_idx_asid_match)
      
  from inrangei inrangej have X2:
    "(MipsTLBLarge_idx2vpn j \<noteq> MipsTLBLarge_idx2vpn i) \<longleftrightarrow>
        \<not> EntryVPNMatch (entries (MipsTLBLarge_create pt) j)
                        (entries (MipsTLBLarge_create pt) i) "
    by(simp add:MipsTLBLarge_create_def MipsTLBLarge_idx_vpn_match)
      
  have X3:  "EntryMatch (entries (MipsTLBLarge_create pt) j) 
                        (entries (MipsTLBLarge_create pt) i) = 
         (EntryVPNMatch (entries (MipsTLBLarge_create pt) j) 
                        (entries (MipsTLBLarge_create pt) i) 
            \<and> EntryASIDMatch (entries (MipsTLBLarge_create pt) j) 
                             (entries (MipsTLBLarge_create pt) i))"
    by(simp add:EntryMatch_def)
  
  from X0 X1 X2 X3 show ?thesis
    by(auto)   
qed
    

    
(* ========================================================================= *)  
section "No faults"
(* ========================================================================= *)     

  
text "For the VPN and ASID in the valid range, there won't be any faults
      occurring in the large TLB. We show that for each valid ASID/VPN
      combination there is an entry in the large TLB. For this purpose
      we first show that for all valid ASID/VPN there is a matching entry
      in the large TLB in general, and then we perform the same for
      even/odd VPNs."

lemma MipsTLBLarge_entry_match_exists:
  assumes inrange: " vpn < MIPSPT_EntriesMax"
      and inrange2: "ASIDValid as"
      and valid: "MIPSPT_valid pt"
    shows "\<exists>i<MipsTLBLarge_Entries. 
             EntryMatchVPNASID vpn as (entries (MipsTLBLarge_create pt) i)"  
proof -
  
  obtain i
    where idx: "i =  MipsTLBLarge_mk_idx as vpn" 
    by(auto)
    
  from inrange inrange2 idx have  ir2 : "i <  MipsTLBLarge_Entries"
  proof -
    have X0: "i < MipsTLBLarge_Entries = (i < MipsTLBLarge_EntryPairs * ASIDMax)"
      by(simp add:MipsTLBLarge_Entries_def)
    
    from inrange2 have X1: "as < ASIDMax"
      by(simp add:ASIDValid_def)
    
    from X1 inrange have X2:
      "MipsTLBLarge_mk_idx as vpn <  (MipsTLBLarge_EntryPairs * ASIDMax) "
      by(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def
                  ASIDMax_def MipsTLBLarge_mk_idx_def)

    show ?thesis
      by(simp add:idx MipsTLBLarge_Entries_def X1 inrange X2)
  qed
  
  show ?thesis
  proof (rule exI[where x = i])
    
    from inrange inrange2 have X0 :
      "MipsTLBLarge_mk_idx as vpn < MipsTLBLarge_Entries"
      by(simp add:MipsTLBLarge_EntryPairs_def MipsTLBLarge_Entries_def 
                  MipsTLBLarge_mk_idx_def MIPSPT_EntriesMax_def 
                  ASIDMax_def ASIDValid_def ASIDMin_def)
      
    have X1:  
      "(i < MipsTLBLarge_Entries 
          \<and> EntryMatchVPNASID vpn as (entries (MipsTLBLarge_create pt) i)) = 
     (MipsTLBLarge_mk_idx as vpn < MipsTLBLarge_Entries \<and>
            EntryMatchVPNASID vpn as 
                (entries (MipsTLBLarge_create pt) (MipsTLBLarge_mk_idx as vpn)))"
      by(simp add:idx)
        
    have X2:
     "... = EntryMatchVPNASID vpn as 
                  (entries (MipsTLBLarge_create pt) (MipsTLBLarge_mk_idx as vpn))"
      by(simp add:X0)
        
    from valid have X3: 
     "... = (EntryVPNMatchV vpn (MIPSPT_mk_tlbentry pt 
             ((MipsTLBLarge_mk_idx as vpn) div MipsTLBLarge_EntryPairs)
             ((MipsTLBLarge_mk_idx as vpn) mod MipsTLBLarge_EntryPairs * 2)) \<and>
                ((MipsTLBLarge_mk_idx as vpn)) div MipsTLBLarge_EntryPairs = as)"
      by(simp add:EntryMatchVPNASID_def MipsTLBLarge_create_def EntryASIDMatchA_def
                  MIPSPT_TLBENTRY_not_global MIPSPT_TLBENTRY_asid_is 
                  MipsTLBLarge_idx2asid_def  MipsTLBLarge_idx2vpn_def)
    
    have X4:
     "... = (vpn div 2 mod MipsTLBLarge_EntryPairs * 2 \<le> vpn \<and> 
            vpn \<le> Suc (vpn div 2 mod MipsTLBLarge_EntryPairs * 2) \<and> 
            (as * MipsTLBLarge_EntryPairs + vpn div 2) div MipsTLBLarge_EntryPairs = as)"
      by(simp add:EntryVPNMatchV_def EntryMin4KVPN_def num_4k_pages_def 
                  EntryMax4KVPN_def MIPSPT_TLBENTRY_vpn2_is_even MIPSPT_TLBENTRY_mask_is 
                  MipsTLBLarge_mk_idx_def)
        
    from inrange inrange2 have X5:  "... = True"
      by(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def, auto)
          
    from X0 X1 X2 X3 X4 X5
    show " i < MipsTLBLarge_Entries \<and> 
             EntryMatchVPNASID vpn as (entries (MipsTLBLarge_create pt) i)"
      by(auto)
  qed
qed

lemma MipsTLBLarge_match_exists_even:
  assumes inrange: " vpn < MIPSPT_EntriesMax"
      and inrange2: "ASIDValid as"
      and valid: "MIPSPT_valid pt"
      and evenvpn: "even vpn"
    shows "\<exists>i<MipsTLBLarge_Entries. 
              EntryMatchVPNASID0 vpn as (entries (MipsTLBLarge_create pt) i)"  
proof -

  from inrange inrange2 valid have X0: "\<exists>i<MipsTLBLarge_Entries. 
             EntryMatchVPNASID vpn as (entries (MipsTLBLarge_create pt) i)"
    by(simp add:MipsTLBLarge_entry_match_exists)
      
  obtain i
    where idx: "i =  MipsTLBLarge_mk_idx as vpn" 
    by(auto)
    
  from inrange inrange2 idx have  ir2 : "i <  MipsTLBLarge_Entries"
  proof -
    have X0: "i < MipsTLBLarge_Entries = (i < MipsTLBLarge_EntryPairs * ASIDMax)"
      by(simp add:MipsTLBLarge_Entries_def)
    
    from inrange2 have X1: "as < ASIDMax"
      by(simp add:ASIDValid_def)
    
    from X1 inrange have X2:
      "(MipsTLBLarge_mk_idx as vpn) <  (MipsTLBLarge_EntryPairs * ASIDMax) "
      by(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def ASIDMax_def 
                  MipsTLBLarge_mk_idx_def)

    show ?thesis
      by(simp add:idx MipsTLBLarge_Entries_def X1 inrange X2) 
  qed
  
  show ?thesis
  proof (rule exI[where x = i])
    
    from inrange inrange2 have X0 :
       "MipsTLBLarge_mk_idx as vpn < MipsTLBLarge_Entries"
      by(simp add:MipsTLBLarge_EntryPairs_def MipsTLBLarge_Entries_def 
                  MIPSPT_EntriesMax_def ASIDMax_def ASIDValid_def ASIDMin_def
                  MipsTLBLarge_mk_idx_def)
      
    have X1:  
      "(i < MipsTLBLarge_Entries \<and> 
          EntryMatchVPNASID0 vpn as (entries (MipsTLBLarge_create pt) i)) = 
       ((MipsTLBLarge_mk_idx as vpn) < MipsTLBLarge_Entries \<and>
             EntryMatchVPNASID0 vpn as  (entries (MipsTLBLarge_create pt) 
                                          (MipsTLBLarge_mk_idx as vpn)))"
      by(simp add:idx)
        
    have X2:
     "... = EntryMatchVPNASID0 vpn as 
             (entries (MipsTLBLarge_create pt) (MipsTLBLarge_mk_idx as vpn))"
      by(simp add:X0)
        
    from valid have X3: 
     "... = (EntryVPNMatchV0 vpn (MIPSPT_mk_tlbentry pt 
             ((MipsTLBLarge_mk_idx as vpn) div MipsTLBLarge_EntryPairs)
             (MipsTLBLarge_mk_idx as vpn mod MipsTLBLarge_EntryPairs * 2)) \<and>
                (MipsTLBLarge_mk_idx as vpn) div MipsTLBLarge_EntryPairs = as)"
      by(simp add:EntryMatchVPNASID0_def MipsTLBLarge_create_def 
                     EntryASIDMatchA_def MIPSPT_TLBENTRY_not_global
                     MIPSPT_TLBENTRY_asid_is  MipsTLBLarge_idx2asid_def 
                     MipsTLBLarge_idx2vpn_def)
                   
    have X4:
     "... = (MipsTLBLarge_mk_idx as vpn mod MipsTLBLarge_EntryPairs * 2 \<le> vpn \<and> 
            vpn < Suc (MipsTLBLarge_mk_idx as vpn mod MipsTLBLarge_EntryPairs * 2) \<and> 
            (MipsTLBLarge_mk_idx as vpn) div MipsTLBLarge_EntryPairs = as)"
      by(simp add:EntryVPNMatchV0_def EntryMin4KVPN_def num_4k_pages_def 
                     EntryMin4KVPN1_def MIPSPT_TLBENTRY_vpn2_is_even MIPSPT_TLBENTRY_mask_is)
        
    from inrange inrange2 evenvpn have X5:  "... = True"
      by(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def
                  MipsTLBLarge_mk_idx_def)
          
    from X0 X1 X2 X3 X4 X5
    show " i < MipsTLBLarge_Entries 
                \<and> EntryMatchVPNASID0 vpn as (entries (MipsTLBLarge_create pt) i)"
      by(auto)
  qed
qed


lemma MipsTLBLarge_match_exists_odd:
  assumes inrange: " vpn < MIPSPT_EntriesMax"
      and inrange2: "ASIDValid as"
      and valid: "MIPSPT_valid pt"
      and oddvpn: "odd vpn"
    shows "\<exists>i<MipsTLBLarge_Entries. 
            EntryMatchVPNASID1 vpn as (entries (MipsTLBLarge_create pt) i)"  
proof -

  obtain i
    where idx: "i =   MipsTLBLarge_mk_idx as (vpn - 1)" 
    by(auto)
    
  from inrange inrange2 idx have  ir2 : "i <  MipsTLBLarge_Entries"
  proof -
    have X0: "i < MipsTLBLarge_Entries = (i < MipsTLBLarge_EntryPairs * ASIDMax)"
      by(simp add:MipsTLBLarge_Entries_def)
    
    from inrange2 have X1: "as < ASIDMax"
      by(simp add:ASIDValid_def)
    
    from X1 inrange have X2:
      " MipsTLBLarge_mk_idx as (vpn - 1) 
           <  (MipsTLBLarge_EntryPairs * ASIDMax) "
      by(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def ASIDMax_def 
                  MipsTLBLarge_mk_idx_def)
        
    show ?thesis
      apply(simp only:idx MipsTLBLarge_Entries_def)
      apply(simp only:X1 inrange X2)
      done   
  qed
  
  show ?thesis
  proof (rule exI[where x = i])
    
    from inrange inrange2 have X0 :
      "MipsTLBLarge_mk_idx as (vpn - 1) < MipsTLBLarge_Entries"
      by(simp add:MipsTLBLarge_EntryPairs_def MipsTLBLarge_Entries_def
                  MIPSPT_EntriesMax_def ASIDMax_def ASIDValid_def ASIDMin_def
                  MipsTLBLarge_mk_idx_def)
      
    have X1: 
    "(i < MipsTLBLarge_Entries \<and> 
        EntryMatchVPNASID1 vpn as (entries (MipsTLBLarge_create pt) i)) = 
         (MipsTLBLarge_mk_idx as (vpn - 1) <  MipsTLBLarge_Entries 
            \<and> EntryMatchVPNASID1 vpn as (entries (MipsTLBLarge_create pt) 
                      (MipsTLBLarge_mk_idx as (vpn - 1))))"
      by(simp only:idx)
        
    have X2: 
      "... = EntryMatchVPNASID1 vpn as (entries (MipsTLBLarge_create pt) 
                  (MipsTLBLarge_mk_idx as (vpn - 1)))"
      by(simp only:X0, auto)
        
    from valid have X3:
      "... = (EntryVPNMatchV1 vpn (MIPSPT_mk_tlbentry pt 
              (MipsTLBLarge_mk_idx as (vpn - 1) div MipsTLBLarge_EntryPairs) 
              (MipsTLBLarge_mk_idx as (vpn - 1) mod MipsTLBLarge_EntryPairs * 2)) \<and>
     (MipsTLBLarge_mk_idx as (vpn - 1)) div MipsTLBLarge_EntryPairs = as)"
      apply(simp only:EntryMatchVPNASID1_def MipsTLBLarge_create_def 
                      EntryASIDMatchA_def)
      apply(simp add:MIPSPT_TLBENTRY_not_global MIPSPT_TLBENTRY_asid_is 
                     MipsTLBLarge_idx2asid_def MipsTLBLarge_idx2vpn_def)
      done
    
    have X4: 
    "... = (Suc (MipsTLBLarge_mk_idx as (vpn - 1) mod MipsTLBLarge_EntryPairs * 2) \<le> vpn \<and>
      vpn \<le> Suc (MipsTLBLarge_mk_idx as (vpn - 1) mod MipsTLBLarge_EntryPairs * 2) \<and>
      (MipsTLBLarge_mk_idx as (vpn - 1)) div MipsTLBLarge_EntryPairs = as) "
      by(simp add:EntryVPNMatchV1_def EntryMax4KVPN_def num_4k_pages_def 
                     EntryMin4KVPN1_def MIPSPT_TLBENTRY_vpn2_is_even MIPSPT_TLBENTRY_mask_is)
        
    from inrange inrange2 oddvpn have X5:  "... = True"
      by(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def 
                  MipsTLBLarge_mk_idx_def)
          
    from X0 X1 X2 X3 X4 X5
    show " i < MipsTLBLarge_Entries
               \<and> EntryMatchVPNASID1 vpn as (entries (MipsTLBLarge_create pt) i)"
      by(auto)
  qed
qed


text "Now we can use the existence of the corresponding entries to show
      that for all valid ASID/VPN combinations, there won't be a refill
      exception thrown. "  
  
lemma MipsTLBLarge_no_faults:
assumes valid: "MIPSPT_valid pt"
    and inrange: " vpn < MIPSPT_EntriesMax"
    and inrange2: "ASIDValid as"
  shows "MIPSTLB_try_translate (MipsTLBLarge_create pt) as vpn \<noteq> EXNREFILL"
proof -
    have capacity: "capacity (MipsTLBLarge_create pt) = MipsTLBLarge_Entries"
      by(simp add:MipsTLBLarge_create_def)    
    
    from valid inrange inrange2 have X1:
     "MIPSTLB_try_translate (MipsTLBLarge_create pt) as vpn = 
      (if \<exists>i<capacity (MipsTLBLarge_create pt). 
              EntryMatchVPNASID0 vpn as (entries (MipsTLBLarge_create pt) i) 
                 \<and> EntryIsValid0 (entries (MipsTLBLarge_create pt) i) then EXNOK
          else if \<exists>i<capacity (MipsTLBLarge_create pt). 
               EntryMatchVPNASID1 vpn as (entries (MipsTLBLarge_create pt) i) 
                 \<and> EntryIsValid1 (entries (MipsTLBLarge_create pt) i) then EXNOK
               else EXNINVALID)"
      by(simp add:MIPSTLB_try_translate_def MipsTLBLarge_entry_match_exists capacity)

    have X3: "... \<noteq> EXNREFILL"
      by(auto)
    
    from X1 X3 show ?thesis
      by(auto)        
  qed

    

(* ========================================================================= *)  
section "Large TLB translate function"
(* ========================================================================= *)          
      
text "Next we obtain a simplified translation function for the large TLB
      This will be a direct look up in the Large TLB. For this we provide
      helper lemmas "
  
(* ------------------------------------------------------------------------- *)
subsection "Entry at Index"    
(* ------------------------------------------------------------------------- *)  

text "If the index is calcuated based on a valid ASID/VPN combination, then
      the entry of the TLB at this index is the created TLB entry."  
  
  
lemma MipsTLBLarge_entry_is:
  assumes inrange: "vpn < MIPSPT_EntriesMax"
  assumes inrange2: "as < ASIDMax"
  shows "(entries (MipsTLBLarge_create pt) (MipsTLBLarge_mk_idx as vpn)) 
            = MIPSPT_mk_tlbentry pt as vpn"
proof cases
  assume veven: "even vpn"
  from inrange veven show ?thesis
    by(simp add:MipsTLBLarge_create_def MipsTLBLarge_EntryPairs_def 
              MIPSPT_EntriesMax_def MipsTLBLarge_idx2vpn_def 
              MipsTLBLarge_idx2asid_def MipsTLBLarge_mk_idx_def)
next
  assume vodd: "odd vpn"
  then show ?thesis 
  proof -
    
    have X0: "entries (MipsTLBLarge_create pt) (MipsTLBLarge_mk_idx as vpn) = 
          MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid (MipsTLBLarge_mk_idx as vpn)) 
                                (MipsTLBLarge_idx2vpn (MipsTLBLarge_mk_idx as vpn))"
      by(simp add:MipsTLBLarge_create_def)
        
    from inrange have X2: "(MipsTLBLarge_idx2asid (MipsTLBLarge_mk_idx as vpn)) = as"
      by(simp add:MipsTLBLarge_idx2asid_def MipsTLBLarge_mk_idx_def 
                 MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def)
        
    from vodd have X3 : "MIPSPT_mk_tlbentry pt as vpn = 
          TLBENTRY.make MASK4K \<lparr>region=0,vpn2 = vpn - Suc 0, asid = as\<rparr> 
                       (entry pt (vpn - Suc 0) as) (entry pt vpn as)"
      by(simp add:MIPSPT_mk_tlbentry_def)
    
    from inrange inrange2 have X4 :
      "MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid (MipsTLBLarge_mk_idx as vpn)) 
                             (MipsTLBLarge_idx2vpn (MipsTLBLarge_mk_idx as vpn)) = 
        TLBENTRY.make MASK4K 
          \<lparr>region=0, vpn2 = MipsTLBLarge_idx2vpn (MipsTLBLarge_mk_idx as vpn), 
          asid = MipsTLBLarge_idx2asid (MipsTLBLarge_mk_idx as vpn)\<rparr>
          (entry pt (MipsTLBLarge_idx2vpn (MipsTLBLarge_mk_idx as vpn)) 
                    (MipsTLBLarge_idx2asid (MipsTLBLarge_mk_idx as vpn)))
          (entry pt (Suc (MipsTLBLarge_idx2vpn (MipsTLBLarge_mk_idx as vpn))) 
                    (MipsTLBLarge_idx2asid (MipsTLBLarge_mk_idx as vpn)))"
      by(simp add:MIPSPT_mk_tlbentry_def MipsTLBLarge_vpn_even 
                 MipsTLBLarge_mk_idx_in_num_entries)  
    
    from X2 have X5:  " ... = TLBENTRY.make MASK4K 
          \<lparr>region=0, vpn2 = MipsTLBLarge_idx2vpn (MipsTLBLarge_mk_idx as vpn), asid = as\<rparr>
          (entry pt (MipsTLBLarge_idx2vpn (MipsTLBLarge_mk_idx as vpn)) as )
          (entry pt (Suc (MipsTLBLarge_idx2vpn (MipsTLBLarge_mk_idx as vpn))) as)"
      by(auto)
        
    from inrange vodd have eq0: 
        "MipsTLBLarge_idx2vpn (MipsTLBLarge_mk_idx as vpn) = vpn - Suc 0"
    proof -
      from inrange have Y0:
        "MipsTLBLarge_idx2vpn (MipsTLBLarge_mk_idx as vpn) = vpn div 2 * 2"
        by(auto simp add:MipsTLBLarge_idx2vpn_def MipsTLBLarge_mk_idx_def
                         MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def)
      
      have Y1: " ... = 2 * (vpn div 2)"
        by(auto)
      from vodd have Y2: " ... = vpn -1"
        by(auto)
      
      from Y0 Y1 Y2 show ?thesis 
        by(auto)
      qed
          
      from vodd inrange have eq1:  
        "Suc (MipsTLBLarge_idx2vpn (MipsTLBLarge_mk_idx as vpn)) = vpn"
      by(auto simp:eq0)
        
    from X4 X5 eq0 eq1 X2 X3 X0 show ?thesis 
      by(auto)
    qed
qed       

(* ------------------------------------------------------------------------- *)
subsection "Always Match if right index"    
(* ------------------------------------------------------------------------- *)    

text "If the entry is at the right index, then for the ASID/VPN there is always
      a match." 
  

lemma MipsTLBLarge_match_true :
   assumes inrange: "vpn < MIPSPT_EntriesMax"
       and inrange2: "as < ASIDMax"
       and ieq: "i = MipsTLBLarge_mk_idx as vpn"
     shows "((EntryMatchVPNASID vpn as (entries (MipsTLBLarge_create pt) i)) = True)"  
proof -
  from ieq have X0: 
    "(EntryMatchVPNASID vpn as (entries (MipsTLBLarge_create pt) i)) = 
        (EntryMatchVPNASID vpn as 
            (entries (MipsTLBLarge_create pt)  (MipsTLBLarge_mk_idx as vpn)))"
    by(auto)
  
  from inrange inrange2 have X1: 
    " ... = EntryMatchVPNASID vpn as (MIPSPT_mk_tlbentry pt as vpn)"
    by(simp add:MipsTLBLarge_entry_is)
  
  from X0 X1 show ?thesis 
    by(simp add:MIPSPT_TLBENTRY_match)
qed
        
  
(* ------------------------------------------------------------------------- *)
subsection "No Match if wrong index"    
(* ------------------------------------------------------------------------- *)    

text "There won't be any match for a ASID/VPN combination for an entry at
      an index which is different form the one calculated based on the
      ASID/VPN. "


lemma MipsTLBLarge_match_false :
   assumes inrange: "vpn < MIPSPT_EntriesMax"
       and inrange2: "as < ASIDMax"
       and valid : "MIPSPT_valid pt"
       and boundi: "i < capacity (MipsTLBLarge_create pt)"
       and inoteq: "i \<noteq> MipsTLBLarge_mk_idx as vpn"
     shows "((EntryMatchVPNASID vpn as (entries (MipsTLBLarge_create pt) i)) = False)"
proof -

  from valid have X1:
    "EntryASIDMatchA as (entries (MipsTLBLarge_create pt) i) = 
       (MipsTLBLarge_idx2asid i = as)"
    apply(simp add:EntryASIDMatchA_def MipsTLBLarge_create_def 
                   MIPSPT_TLBENTRY_not_global MipsTLBLarge_idx2asid_def)
    apply(simp add:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)
    done
  
  from boundi have boundi2: "i < MipsTLBLarge_Entries"
    by(simp add:MipsTLBLarge_create_def)
      
  from inrange inrange2  have X2:
    "EntryVPNMatchV vpn (entries (MipsTLBLarge_create pt) i) = 
     (MipsTLBLarge_idx2vpn i \<le> vpn \<and> vpn \<le> Suc (MipsTLBLarge_idx2vpn i))"
    by(simp add:EntryVPNMatchV_def EntryMin4KVPN_def EntryMax4KVPN_def 
                num_4k_pages_def MipsTLBLarge_create_def MIPSPT_TLBENTRY_mask_is 
                boundi2 MipsTLBLarge_vpn_even MIPSPT_TLBENTRY_vpn2_is_even)    
  
  from X1 X2 have X0: 
      "EntryMatchVPNASID vpn as (entries (MipsTLBLarge_create pt) i) =  
          (MipsTLBLarge_idx2vpn i \<le> vpn \<and> vpn \<le> Suc (MipsTLBLarge_idx2vpn i) \<and>
          (MipsTLBLarge_idx2asid i = as))"
    by(auto simp:EntryMatchVPNASID_def)
      
  from  inrange boundi inrange2 inoteq have X3:
     "\<not>(MipsTLBLarge_idx2vpn i \<le> vpn 
          \<and> vpn \<le> Suc (MipsTLBLarge_idx2vpn i)) \<or>
     \<not> (MipsTLBLarge_idx2asid i = as)"
  proof -
    from inoteq boundi inrange inrange2 have Y0:
      "(MipsTLBLarge_idx2asid i  = as) \<longrightarrow> 
       \<not>(MipsTLBLarge_idx2vpn i\<le> vpn 
           \<and> vpn \<le> Suc (MipsTLBLarge_idx2vpn i))"
     proof -
       from inoteq have Z0:
        "(MipsTLBLarge_idx2asid i = as)
             \<longrightarrow>  (MipsTLBLarge_idx2vpn i \<noteq> vpn)"
       by(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def 
                      MipsTLBLarge_idx2asid_def MipsTLBLarge_idx2vpn_def
                      MipsTLBLarge_mk_idx_def , auto)    
      
      from inoteq have Z1:
        "(MipsTLBLarge_idx2asid i = as)
             \<longrightarrow>  (Suc (MipsTLBLarge_idx2vpn i) \<noteq> vpn)"
       by(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def 
                      MipsTLBLarge_idx2asid_def MipsTLBLarge_idx2vpn_def
                      MipsTLBLarge_mk_idx_def , auto) 
      
      with Z0 inrange show "(MipsTLBLarge_idx2asid i = as) \<longrightarrow> 
         \<not>(MipsTLBLarge_idx2vpn i \<le> vpn 
            \<and> vpn \<le> Suc (MipsTLBLarge_idx2vpn i))"
        by( simp add:MipsTLBLarge_idx2vpn_def, auto)
      qed      
      
    from inoteq have Y1: 
      "(MipsTLBLarge_idx2vpn i \<le> vpn
         \<and> vpn \<le> Suc (MipsTLBLarge_idx2vpn i))
        \<longrightarrow> \<not> (MipsTLBLarge_idx2asid i  = as)"
    proof -
      from inoteq have Z0:
         "(MipsTLBLarge_idx2asid i= as) \<longrightarrow>  (MipsTLBLarge_idx2vpn i \<noteq> vpn)"
       by(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def 
                      MipsTLBLarge_idx2asid_def MipsTLBLarge_idx2vpn_def
                      MipsTLBLarge_mk_idx_def , auto) 
      
      from inoteq have Z1 :
         "(MipsTLBLarge_idx2asid i = as) \<longrightarrow>  (Suc (MipsTLBLarge_idx2vpn i) \<noteq> vpn)"
       by(simp add:MipsTLBLarge_EntryPairs_def MIPSPT_EntriesMax_def 
                      MipsTLBLarge_idx2asid_def MipsTLBLarge_idx2vpn_def
                      MipsTLBLarge_mk_idx_def , auto)  
 
       with Z0 Z1 show "(MipsTLBLarge_idx2vpn i \<le> vpn
                           \<and> vpn \<le> Suc (MipsTLBLarge_idx2vpn i))
                              \<longrightarrow> \<not> (MipsTLBLarge_idx2asid i  = as)"
        by( simp add:MipsTLBLarge_idx2vpn_def, auto)
      qed
    from Y0 Y1 show ?thesis 
      by(auto)
    qed

  from X0  X1 X2 X3 show ?thesis 
    by(auto)  
qed

  
  
(* ------------------------------------------------------------------------- *)
subsection "The Translate function"    
(* ------------------------------------------------------------------------- *)     
  
text "Next we can formulate the translate function for the large TLB."
    
lemma MipsTLBLarge_translate_is:
  assumes inrange: "vpn < MIPSPT_EntriesMax"
    and inrange2: "as < ASIDMax"
    and valid: "MIPSPT_valid pt"
  shows "MIPSTLB_translate ( (MipsTLBLarge_create pt)) as vpn = 
           (if (v ((entry pt) vpn as)) then {(pfn ((entry pt) vpn as))} else {})" 
proof -
  from inrange inrange2  have incapacity:
    "j = (MipsTLBLarge_mk_idx as vpn) \<Longrightarrow> j < capacity (MipsTLBLarge_create pt) "
    by(simp add:MipsTLBLarge_create_def MipsTLBLarge_EntryPairs_def 
                MIPSPT_EntriesMax_def  MipsTLBLarge_Entries_def ASIDMax_def 
                MipsTLBLarge_mk_idx_def)

  from inrange inrange2 valid have notranslation :
     "{pfn'. \<exists>i. pfn' \<in> 
          TLBENTRY_translate (entries (MipsTLBLarge_create pt) i) as vpn \<and> 
          i < capacity (MipsTLBLarge_create pt) \<and> i \<noteq> MipsTLBLarge_mk_idx as vpn} = {}"
  proof -
    have Y1: "{pfn'. \<exists>i. pfn' \<in> 
          TLBENTRY_translate (entries (MipsTLBLarge_create pt) i) as vpn \<and> 
          i < capacity (MipsTLBLarge_create pt) \<and> i \<noteq> MipsTLBLarge_mk_idx as vpn}  = 
          {pfn'. \<exists>i.  i \<noteq> MipsTLBLarge_mk_idx as vpn \<and>  i < capacity (MipsTLBLarge_create pt) 
          \<and> pfn' \<in> TLBENTRY_translate (entries (MipsTLBLarge_create pt) i) as vpn  } "
      by(auto)
    
    have Y2:  
      " ... = 
      {pfn'. \<exists>i. i \<noteq> MipsTLBLarge_mk_idx as vpn \<and> i < capacity (MipsTLBLarge_create pt) \<and>
             pfn' \<in> (if EntryMatchVPNASID vpn as (entries (MipsTLBLarge_create pt) i) then
                      if even vpn \<and> EntryIsValid0 (entries (MipsTLBLarge_create pt) i) then 
                       {pfn (lo0 (entries (MipsTLBLarge_create pt) i))
                           + (vpn - EntryMin4KVPN (entries (MipsTLBLarge_create pt) i))}
                      else 
                        if odd vpn \<and> EntryIsValid1 (entries (MipsTLBLarge_create pt) i) then 
                          {pfn (lo1 (entries (MipsTLBLarge_create pt) i))
                             + (vpn - EntryMin4KVPN1 (entries (MipsTLBLarge_create pt) i))}
                        else {}
                    else {})}"
      by(simp only:TLBENTRY_translate_def)
        
    from inrange inrange2 valid have Y3:  " ... = {}"
      by(auto simp add:MipsTLBLarge_match_false)
    
    from Y1 Y2 Y3 show ?thesis
      by(auto)    
  qed
      
  from inrange inrange2 have incapacityrange :
    " MipsTLBLarge_mk_idx as vpn < capacity (MipsTLBLarge_create pt)"
    by(simp add:MipsTLBLarge_mk_idx_def MipsTLBLarge_create_def MipsTLBLarge_EntryPairs_def
                MIPSPT_EntriesMax_def MipsTLBLarge_Entries_def)
              
  have X0:
    "MIPSTLB_translate ( (MipsTLBLarge_create pt)) as vpn =  
       {pfn'. \<exists>i. pfn' \<in> 
          TLBENTRY_translate (entries (MipsTLBLarge_create pt) i) as vpn \<and> 
          i < capacity (MipsTLBLarge_create pt)}"
      by(simp add:MIPSTLB_translate_def)

   have X1 : " ... =  {pfn'. \<exists>i. pfn' \<in> 
          TLBENTRY_translate (entries (MipsTLBLarge_create pt) i) as vpn \<and> 
          i < capacity (MipsTLBLarge_create pt) \<and> i \<noteq> MipsTLBLarge_mk_idx as vpn} \<union>
           {pfn'. \<exists>i. pfn' \<in> 
          TLBENTRY_translate (entries (MipsTLBLarge_create pt) i) as vpn \<and> 
          i < capacity (MipsTLBLarge_create pt) \<and> i = MipsTLBLarge_mk_idx as vpn}"
        by(auto)
   
   have X2: " ... =  {pfn'. \<exists>i. pfn' \<in> 
          TLBENTRY_translate (entries (MipsTLBLarge_create pt) i) as vpn \<and> 
          i < capacity (MipsTLBLarge_create pt) \<and> i = MipsTLBLarge_mk_idx as vpn}"
     by(simp add:notranslation)
       
   from inrange inrange2 have X3:
     " ... =  {pfn' \<in> TLBENTRY_translate (MIPSPT_mk_tlbentry pt as vpn) as vpn. 
               MipsTLBLarge_mk_idx as vpn < capacity (MipsTLBLarge_create pt)} "
     by(simp add: MipsTLBLarge_entry_is)
    
   have X4 : "... = TLBENTRY_translate (MIPSPT_mk_tlbentry pt as vpn) as vpn"
     by(simp add:incapacityrange)
   
   have X5: " ... = 
    (if even vpn \<and> EntryIsValid0 (MIPSPT_mk_tlbentry pt as vpn) then 
      {pfn (lo0 (MIPSPT_mk_tlbentry pt as vpn))
           + (vpn - EntryMin4KVPN (MIPSPT_mk_tlbentry pt as vpn))}
       else if odd vpn \<and> EntryIsValid1 (MIPSPT_mk_tlbentry pt as vpn) then 
        {pfn (lo1 (MIPSPT_mk_tlbentry pt as vpn)) 
            + (vpn - EntryMin4KVPN1 (MIPSPT_mk_tlbentry pt as vpn))} else {})"
     by(simp add:TLBENTRY_translate_def MIPSPT_TLBENTRY_match)
   
   have X6: " ... = (if even vpn \<and> EntryIsValid0 (MIPSPT_mk_tlbentry pt as vpn) then 
      {pfn (lo0 (MIPSPT_mk_tlbentry pt as vpn))}
       else if odd vpn \<and> EntryIsValid1 (MIPSPT_mk_tlbentry pt as vpn) then 
        {pfn (lo1 (MIPSPT_mk_tlbentry pt as vpn))} else {})"
     by(simp add:MIPSPT_mk_tlbentry_def TLBENTRY.make_def EntryMin4KVPN_def
                 EntryMin4KVPN1_def)
    
   have X7: " ... = (if even vpn \<and> EntryIsValid0 (MIPSPT_mk_tlbentry pt as vpn) then 
       {pfn (entry pt vpn as)}
       else if odd vpn \<and> EntryIsValid1 (MIPSPT_mk_tlbentry pt as vpn) then 
       {pfn (entry pt vpn as)} else {})"
     by(simp add:MIPSPT_mk_tlbentry_def TLBENTRY.make_def)

   have X8: 
     " ... = (if  (v (entry pt vpn as)) then {pfn (entry pt vpn as)} else {} )"
     by(simp add:EntryIsValid0_def EntryIsValid1_def MIPSPT_mk_tlbentry_def 
                 TLBENTRY.make_def)
   
   from X0 X1 X2 X3 X5 X6 X7 X8 incapacityrange show ?thesis 
     by(auto)       
qed

      
(* ========================================================================= *)  
section "The Large TLB is Valid"
(* ========================================================================= *)     

text "Next we show that the created and initialized large TLB is valid in the
      sense of the MIPS TLB definition."  

  
(* ------------------------------------------------------------------------- *)
subsection "All Entries are WellFormed"    
(* ------------------------------------------------------------------------- *)       
  
text "All entries created for the large TLB are well formed. This requires
      that the page table is valid."
  
lemma MipsTLBLarge_entry_wellformed :    
  assumes ptvalid : "MIPSPT_valid pt"                  
  shows "\<forall>x < MipsTLBLarge_Entries.   
        TLBENTRYWellFormed (MIPSPT_mk_tlbentry pt (MipsTLBLarge_idx2asid x)
                                                  (MipsTLBLarge_idx2vpn x))"
  by(simp add:MIPSPT_TLBENTRY_wellformed MipsTLBLarge_asid_valid 
              MipsTLBLarge_vpn_valid ptvalid)
 

(* ------------------------------------------------------------------------- *)
subsection "The Large TLB is Valid"    
(* ------------------------------------------------------------------------- *)               

text "Next we use the properties from above to show that the created large
      TLB is a valid in the sense of the VALID"
  
lemma MipsTLBLarge_valid :
  assumes ptvalid : "MIPSPT_valid pt"
  shows "TLBValid (MipsTLBLarge_create pt)"
proof -
  
  have capacity: "capacity (MipsTLBLarge_create pt) = MipsTLBLarge_Entries"
    by(simp add:MipsTLBLarge_create_def)
  
  have X0:  
    "TLBValid (MipsTLBLarge_create pt) =  
      (wired (MipsTLBLarge_create pt) \<le> capacity (MipsTLBLarge_create pt) \<and>
       wired (MipsTLBLarge_create pt) < TLBMaximumWired \<and>
     (\<forall>i<capacity (MipsTLBLarge_create pt). 
        TLBEntryWellFormed (MipsTLBLarge_create pt) i 
          \<and> TLBEntryConflictSet (entries (MipsTLBLarge_create pt) i) (MipsTLBLarge_create pt) \<subseteq> {i}))"
    by(simp add:TLBValid_def)
  
  have X1: 
    "(wired (MipsTLBLarge_create pt) < capacity (MipsTLBLarge_create pt)) 
          \<and> (wired (MipsTLBLarge_create pt) < TLBMaximumWired)"
    by(simp add:TLBMaximumWired_def MipsTLBLarge_create_def MipsTLBLarge_Entries_def 
                MipsTLBLarge_EntryPairs_def ASIDMax_def MIPSPT_EntriesMax_def)
      
  from ptvalid capacity have X2: 
    " (\<forall>i<capacity (MipsTLBLarge_create pt). 
            TLBEntryWellFormed (MipsTLBLarge_create pt) i)"
    by(simp add:MipsTLBLarge_create_def TLBEntryWellFormed_def 
                MipsTLBLarge_entry_wellformed)
      
  have X3: 
    "(\<forall>i<capacity (MipsTLBLarge_create pt). 
       TLBEntryConflictSet (entries (MipsTLBLarge_create pt) i) 
                           (MipsTLBLarge_create pt) \<subseteq> {i})"
  proof -
    have Y0: 
      "\<forall>i<capacity (MipsTLBLarge_create pt). 
          TLBEntryConflictSet (entries (MipsTLBLarge_create pt) i) 
                              (MipsTLBLarge_create pt) = 
             {ia. ia < MipsTLBLarge_Entries
                 \<and> EntryMatch (entries (MipsTLBLarge_create pt) ia)  
                              (entries (MipsTLBLarge_create pt) i)}"
      by(simp add:TLBEntryConflictSet_def capacity)
    
    have Y1: 
      "\<forall>i<capacity (MipsTLBLarge_create pt).  
            {ia. ia < MipsTLBLarge_Entries 
                \<and> EntryMatch (entries (MipsTLBLarge_create pt) ia) 
                             (entries (MipsTLBLarge_create pt) i)} = 
            {ia. i = ia \<and> ia < MipsTLBLarge_Entries 
                \<and> EntryMatch (entries (MipsTLBLarge_create pt) ia) 
                             (entries (MipsTLBLarge_create pt) i)} 
         \<union>  {ia. i \<noteq> ia \<and> ia < MipsTLBLarge_Entries
                \<and> EntryMatch (entries (MipsTLBLarge_create pt) ia)
                             (entries (MipsTLBLarge_create pt) i)}"
      by(auto)
        
    have Y2: 
      "\<forall>i<capacity (MipsTLBLarge_create pt).  
        {ia. ia < MipsTLBLarge_Entries 
              \<and> EntryMatch (entries (MipsTLBLarge_create pt) ia) 
                           (entries (MipsTLBLarge_create pt) i)}
        =  {ia. i = ia \<and> ia < MipsTLBLarge_Entries \<and> True} 
        \<union>  {ia. i \<noteq> ia \<and> ia < MipsTLBLarge_Entries 
              \<and> EntryMatch (entries (MipsTLBLarge_create pt) ia)
                           (entries (MipsTLBLarge_create pt) i)}"
      by(auto simp:EntryMatch_true)

    from ptvalid have Y3: 
      "\<forall>i<capacity (MipsTLBLarge_create pt).  
        {ia. i = ia \<and> ia < MipsTLBLarge_Entries \<and> True} 
      \<union>  {ia. i \<noteq> ia \<and> ia < MipsTLBLarge_Entries 
          \<and> EntryMatch (entries (MipsTLBLarge_create pt) ia) 
                       (entries (MipsTLBLarge_create pt) i)}  = 
        {ia. i = ia \<and> ia < MipsTLBLarge_Entries \<and> True} 
            \<union>  {ia. i \<noteq> ia \<and> ia < MipsTLBLarge_Entries \<and> False} "
    by(auto simp add:MipsTLBLarge_idx_no_match capacity)
     
  have  Y4: 
    "\<forall>i<capacity (MipsTLBLarge_create pt). 
       {ia. i = ia \<and> ia < MipsTLBLarge_Entries \<and> True} 
            \<union> {ia. i \<noteq> ia \<and> ia < MipsTLBLarge_Entries \<and> False}  = {i}"
    by(auto simp:MipsTLBLarge_create_def)
   
  from Y0 Y1 Y2 Y3 Y4 show ?thesis
    by(auto)
  qed
    
  from X0 X1 X2 X3 show ?thesis 
    by(auto)
qed
  
end