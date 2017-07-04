(*<*)
theory ARMv7TranslationTables
  imports Main Set Model Syntax Parity Nat PageTable
begin
(*>*)  

(* ========================================================================= *)
section "Memory Parameters"
(* ========================================================================= *)  
  
definition ARMv7MParams :: "MParams"
  where "ARMv7MParams = \<lparr>vpn_max = M 1, pfn_max = M 1, pgsize = K 4 \<rparr>"
    
lemma "VASize ARMv7MParams = VASizeBits 32"
  by(auto simp:VASize_def ARMv7MParams_def VASizeBits_def K_def M_def)

(* ========================================================================= *)
section "Page Table initialization"
(* ========================================================================= *)  

definition ARMv7PageTable_init :: PageTable
  where "ARMv7PageTable_init = PageTable_init ARMv7MParams"
  
  
(* ========================================================================= *)
section "First Level Table"
(* ========================================================================= *)

text "Holds first-level descriptors that contain the base address and
       - translation properties for a Section and Supersection
       -  translation properties and pointers to a second-level table for a 
          Large page or a Small page."  

  


  
(* ========================================================================= *)
section "Second Level Table"
(* ========================================================================= *)  

text "Hold second-level descriptors that contain the base address and 
      translation properties for a Small page or a Large page."  
  
record SecondLevelTable =
  entries :: "nat \<Rightarrow> addr set"
  

  
  
(*<*)
end
(*>*)    