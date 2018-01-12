(*

Copyright (c) 2018, ETH Zurich
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

(*
 Based on "Intel \<registered> Virtualization Technology for Directed I/O", October 2014
*)

(*<*)
theory iommu
  imports interrupt Main Set  "../model/Model" "../model/Syntax" x86int
begin
(*>*)

(* Address word (32bit) *)
type_synonym ADDR = nat
(* Data word (32bit) *)
type_synonym DATA = nat
(* index into the interrupt remapping table *)
type_synonym IRTEINDEX = nat

(* Size, as encoded in the IRTA field *)
type_synonym IRTASIZE = nat

definition IRTASIZEWellFormed :: "IRTASIZE \<Rightarrow> bool" where 
  "IRTASIZEWellFormed x \<longleftrightarrow>  x \<le> 0xf"

(* Transform an IRTASize into number of entries *)
definition irta_size :: "IRTASIZE \<Rightarrow> nat" where
  "irta_size x = 2^(1+x)"


(* IOMMU configuration stored in 
  - Global Status Register (GSR)
  - Interrupt remapping table address register (IRTA)
 *)
record IOMMUCONF =
  ires :: bool (* (GSR) Interrupt remapping enabled *)
  cfis :: bool (* (GSR) Compatibility Format Interrupt Status *)
  eime :: bool (* (IRTA) 0=xapic mode 8bit dest IDs, 1=xapic2 32bit dest ids *)
  irtas :: IRTASIZE (* (IRTA) table size *)



definition IOMMUCONFWellFormed :: "IOMMUCONF \<Rightarrow> bool" where
  "IOMMUCONFWellFormed x = IRTASIZEWellFormed (irtas x)"

(* Is a nat binary representable with given number of bits? *) 
definition ENC :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "ENC num bits \<longleftrightarrow> num < 2^bits"

(* source id format (the iommu can check the source of the interrupt) *)
record SOURCEID =
  id :: nat

definition SOURCEIDWellFormed :: "SOURCEID \<Rightarrow> bool" where
  "SOURCEIDWellFormed f = ENC (id f) 4"

(* The destination encoding of an interrupt, the size of this field
   is dependent on the hardware and the adressing mode,
  the meaning, depends on addition on the delivery mode *)
record DESTID =
  id :: nat

definition DESTIDWellFormed :: "DESTID \<Rightarrow> bool" where
  "DESTIDWellFormed f = ENC (id f) 32"

(* Source Validation Type. SVTALL means all bit must match, the other
ignore the 1,2 or 3 lowest bits on comparison *)
datatype SVT = SVTALL | SVTIG3 | SVTIG32 | SVTIG321
(*
primrec SOURCEIDMatch :: "SVT \<Rightarrow> SOURCEID \<Rightarrow> SOURCEID \<Rightarrow>  bool" where
  "SOURCEIDMatch SVTALL a b = ((id a) = (id b))" |
  "SOURCEIDMatch SVTIG3 a b = True" |
  "SOURCEIDMatch SVTIG32 a b = True" |
  "SOURCEIDMatch SVTIG321 a b = True"
*)
 

(* A single interrupt remapping table entry, Section 9.10 *) 
record IRTE =
  svt :: SVT
  sq :: nat
  sid :: SOURCEID
  dst :: DESTID
  vec :: nat
  im :: bool (* 0 = normal delivery, 1 = posting *)
  avail :: nat
  dlm :: DLM
  tm :: bool 
  rh :: bool
  dm :: DM
  fpd :: bool
  p :: bool
  
  
definition IRTEWellFormed :: "IRTE \<Rightarrow> bool" where
  "IRTEWellFormed x \<longleftrightarrow> ENC (svt x) 3 \<and>
                        ENC (sq x) 5 \<and>
                        SOURCEIDWellFormed (sid x) \<and>
                        DESTIDWellFormed (dst x) \<and>
                        ENC (vec x) 8 \<and>
                        ENC (avail x) 4"


(* A single posted interrupt remapping table entry, Section 9.11 *) 
record IRTEPOSTED =
  pdaddr :: nat
  svt :: SVT
  sq :: nat
  sid :: SOURCEID
  vec :: nat
  urgent :: bool
  avail :: nat
  fpd :: bool
  p :: bool

definition IRTEPOSTEDWellFormed :: "IRTEPOSTED \<Rightarrow> bool" where
  "IRTEPOSTEDWellFormed x \<longleftrightarrow>
                    ENC (pdaddr x) 32 \<and>
                    ENC (sq x) 5 \<and>
                    SOURCEIDWellFormed (sid x) \<and>
                    ENC (vec x) 8 \<and>
                    ENC (avail x) 4"
                        
  

(* Input address in compatibility format, in format (5.1.2.1), fmt=0 *)
record ADDRINCOMPAT = 
  destination_mode :: nat
  redirection_hint :: bool
  destination_id :: nat


  

(* Input address format, in remappable format (5.1.2.2), fmt=1 *)
record ADDRIN = 
  handle :: nat
  shv :: bool

definition ADDRINWellFormed :: "ADDRIN \<Rightarrow> bool" where
  "ADDRINWellFormed x \<longleftrightarrow> (handle x) < 2^15"

(* Input data format *)
record DATAIN = 
  subhandle :: nat
 
definition DATAINWellFormed :: "DATAIN \<Rightarrow> bool" where 
  "DATAINWellFormed x \<longleftrightarrow>  (subhandle x) \<le> 2^15"


  

definition is_uint32 :: "nat \<Rightarrow> bool" where
  "is_uint32 n \<longleftrightarrow> n \<le> 0xffffffff \<and> n \<ge> 0"

(* is the SHV bit set (Position 3) *)
definition addr_shv_set :: "ADDR \<Rightarrow> bool" where
  "addr_shv_set addr = True"

(* This is the non configurable, table lookup function, See VT-D spec 5.1.3 *)
definition irte_map :: "ADDR \<Rightarrow> DATA \<Rightarrow> nat"
(*  where "irte_map addr dat \<Rightarrow> (if addr_shv_set addr then 0 else 1)" *)
  where "irte_map addr dat = 0"

definition iommu_mapvalid_indiv_dom_valid :: "IRQ set \<Rightarrow> bool"
  where "iommu_mapvalid_indiv_dom_valid xs  \<longleftrightarrow>  (\<forall>x \<in> xs. irq_is_memwrite x)"

definition iommu_mapvalid_pred :: "(IRQ \<Rightarrow> IRQ set) \<Rightarrow> bool"
  where "iommu_mapvalid_pred x = iommu_mapvalid_indiv_dom_valid (doms x)"    

definition iommu_mapvalid :: "(IRQ \<Rightarrow> IRQ set) set"
  where "iommu_mapvalid = {x. iommu_mapvalid_pred x}"

definition iommu :: CONTROLLER_CLASS
  where "iommu = \<lparr> in_port_num = 1, out_port_num =1, map_valid = iommu_mapvalid \<rparr>"

end