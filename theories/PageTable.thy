(*<*)
theory PageTable
  imports Main Set Model Syntax Parity Power
begin
(*>*)  


(* ========================================================================= *)
section "Auxiliary Functions"
(* ========================================================================= *)  
  
text "Getting a nicer representation for kB and MB"
  
definition K :: "nat \<Rightarrow> nat" 
  where "K n = n * 1024"

definition M :: "nat \<Rightarrow> nat" 
  where "M n = n * 1048576"

definition G :: "nat \<Rightarrow> nat" 
  where "G n = n * 1073741824"  

definition T :: "nat \<Rightarrow> nat" 
  where "T n = n * 1099511627776"      
    
text "Size of the address sizes"
    
definition VASizeBits :: "nat \<Rightarrow> nat"
  where "VASizeBits b = (power 2 b)"
    
lemma "VASizeBits 32 = G 4"
  by(simp add:VASizeBits_def G_def)
    
    

(* ========================================================================= *)
section "Logical Page Table"
(* ========================================================================= *)  

text "Logically a page table is a linear array of page table entries indexed
      by Virtual Page Number (VPN). Each entry stores the Physical Frame
      Number (PFN) along with a set of attributes."



(* ------------------------------------------------------------------------- *)  
subsection "Type Declarations"  
(* ------------------------------------------------------------------------- *)  
  
text "The Virtual Page Number (VPN) is of type nat."
type_synonym VPN = nat
  
text "The Physical Frame Number (PFN) is of type nat."
type_synonym PFN = nat

  
  
(* ------------------------------------------------------------------------- *)  
subsection "Memory Parameters"  
(* ------------------------------------------------------------------------- *)   

text "The MParams define the parameters of the memory subsystem. They define
      the base page size and then maximum number of VPN and PFN. A page table
      is created for a particular configuration."

record MParams = 
  vpn_max :: nat
  pfn_max :: nat
  pgsize  :: nat

  
text "The sizes of the virtual and physical address spaces can be calculated
      from the MParams"  

definition VASize :: "MParams \<Rightarrow> nat"
  where "VASize m = (pgsize m) * (vpn_max m)"  

definition PASize :: "MParams \<Rightarrow> nat"
  where "PASize m = (pgsize m) * (pfn_max m)"    
    
definition MParams_32 :: "MParams"
  where "MParams_32 = \<lparr>vpn_max = M 1, pfn_max = M 1, pgsize = K 4 \<rparr>"

lemma "VASize MParams_32 = VASizeBits 32"
  by(auto simp:VASize_def MParams_32_def VASizeBits_def K_def M_def)
  
    
(* ------------------------------------------------------------------------- *)  
subsection "PageTable Entry"  
(* ------------------------------------------------------------------------- *)  

text "Attributes define the properties and access rights of the entry "
datatype ATTRIBUTE = ATTR_READ | ATTR_WRITE | ATTR_EXEC | ATTR_SUPERVISOR | 
                     ATTR_VALID | ATTR_NOCACHE

                     
text "The PTEntry stores the PFN it translates to and the set of attributes 
      associated with the entry."

record PTEntry =  
  pfn :: PFN
  attributes :: "ATTRIBUTE set"
  
  
definition PTEntry_is_writeable :: "PTEntry \<Rightarrow> bool"
  where "PTEntry_is_writeable e = ({ATTR_WRITE} \<inter> (attributes e) \<noteq> {})"
  
definition PTEntry_is_valid :: "PTEntry \<Rightarrow> bool"
  where "PTEntry_is_valid e = ({ATTR_VALID} \<inter> (attributes e) \<noteq> {})"
  
    
text "The ptentry_null is an all-zero entry with an empty set of attributes
      and therefore the ptentry_null is not valid"

  
definition PTEntry_null :: "PTEntry"
  where "PTEntry_null = \<lparr> pfn = 0, attributes = {} \<rparr>"      
   
lemma "PTEntry_is_valid PTEntry_null = False"
  by(auto simp:PTEntry_null_def PTEntry_is_valid_def)  
    

    
(* ------------------------------------------------------------------------- *)  
subsection "PageTable"  
(* ------------------------------------------------------------------------- *)      
    
text "The PageTable represents a logical array of PTEntries. The PageTable has 
      two fields:
      - entries: a function from VPN to a PTEntry
      - count:   the maximum number of entries "
  
record PageTable =
  entries :: "VPN \<Rightarrow> PTEntry"
  mp   :: MParams
  
(* ------------------------------------------------------------------------- *)  
subsubsection "Initialization Function"  
(* ------------------------------------------------------------------------- *)   
  
definition PageTable_init :: "MParams \<Rightarrow> PageTable"
  where "PageTable_init c = \<lparr> entries = (\<lambda>a. PTEntry_null), mp = c \<rparr>"

   
definition PageTable_init32 :: "PageTable"
  where "PageTable_init32  = PageTable_init (MParams_32)"

    
(* ------------------------------------------------------------------------- *)  
subsubsection "Predicates"  
(* ------------------------------------------------------------------------- *)     

text "The page table is valid, if for all entries, the PFN 
      is smaller than the maximum PFN"
  
definition PageTable_valid :: "PageTable \<Rightarrow> bool" 
  where "PageTable_valid pt = (\<forall>i < (vpn_max (mp pt)). 
                              (( pfn (entries pt i)) < (pfn_max (mp pt))) )"
        
lemma "PageTable_valid PageTable_init32"
  by(simp add: PageTable_valid_def PageTable_init32_def MParams_32_def 
               PageTable_init_def PTEntry_null_def)
    

             
(* ========================================================================= *)
section "Operations"
(* ========================================================================= *)              
             
(* ------------------------------------------------------------------------- *)  
subsubsection "Write PTEntry"  
(* ------------------------------------------------------------------------- *)    

definition PageTable_write_entry :: "VPN \<Rightarrow> PTEntry \<Rightarrow> PageTable \<Rightarrow> PageTable set"
  where "PageTable_write_entry vpn e pt = (if vpn < (vpn_max (mp pt)) then
                                          {\<lparr> entries = (entries pt)(vpn := e), 
                                             mp = (mp pt) \<rparr>}
                                          else UNIV )"

    
(* ------------------------------------------------------------------------- *)  
subsubsection "Read PTEntry"  
(* ------------------------------------------------------------------------- *)    

definition PageTable_read_entry :: "VPN \<Rightarrow> PageTable \<Rightarrow> PTEntry set"
  where "PageTable_read_entry vpn pt =  (if vpn < (vpn_max (mp pt)) then
                                          {(entries pt vpn)}
                                          else UNIV )"     
    
    
(* ------------------------------------------------------------------------- *)  
subsubsection "Translate"  
(* ------------------------------------------------------------------------- *)    
  
definition PageTable_translate :: "VPN \<Rightarrow> PageTable \<Rightarrow> PFN set"
  where "PageTable_translate vpn pt =  (if (vpn < (vpn_max (mp pt))) \<and>
                                           (PTEntry_is_valid (entries pt vpn))
                                        then {pfn (entries pt vpn)}
                                          else UNIV )"

(* ------------------------------------------------------------------------- *)  
subsubsection "Lookup"  
(* ------------------------------------------------------------------------- *)     
    
definition PageTable_lookup :: "PFN \<Rightarrow> PageTable \<Rightarrow> VPN set"
  where "PageTable_lookup pf pt =  (if (pf < (pfn_max (mp pt)))
                                     then { v | v e . (pfn e) = pf \<and>  
                                                      PTEntry_is_valid e \<and>  
                                                      e = (entries pt v)  }
                                     else UNIV )"  
  
(* ========================================================================= *)
section "Create a model node"
(* ========================================================================= *)              

definition PTEntry_Range :: "VPN \<Rightarrow> nat \<Rightarrow> nat set"
  where "PTEntry_Range v sz = {x. v * sz \<le> x \<and>  x < (Suc v) * sz}"
  
definition PTEntry_to_map ::  "nodeid \<Rightarrow> VPN \<Rightarrow> PageTable \<Rightarrow> nat \<Rightarrow>(nat \<times> nat) set"
  where "PTEntry_to_map nd i pt va = (if (PTEntry_is_valid (entries pt i)) \<and> 
                                     va \<in> PTEntry_Range i (pgsize (mp pt)) then {(nd, 
                                        (pfn (entries pt i)) * (pgsize (mp pt))
                                        )} else {} )"
  
definition PTEntry_map_replace :: "nat \<Rightarrow> VPN \<Rightarrow> VPN \<Rightarrow> PageTable \<Rightarrow> node \<Rightarrow> node"
  where
    "PTEntry_map_replace nid v1 v2  pt  n = n \<lparr>
      accept := accept n,
      translate := (\<lambda>va. (translate n va - (PTEntry_to_map nid v1 pt va)) \<union> PTEntry_to_map nid v2 pt va) \<rparr>"
    
    
definition PageTable_to_Node :: "nodeid \<Rightarrow> PageTable \<Rightarrow> node"
  where "PageTable_to_Node nid pt =  \<lparr> accept = {},
              translate = (\<lambda> a. \<Union>i< (vpn_max (mp pt)).  PTEntry_to_map nid i pt a) \<rparr>"


lemma "PageTable_to_Node nd PageTable_init32 = empty_node"
  by(auto simp:PageTable_to_Node_def  PageTable_init32_def  empty_node_def
               PageTable_init_def MParams_32_def PTEntry_null_def PTEntry_to_map_def
               PTEntry_is_valid_def)

             
(*<*)
end
(*>*)    