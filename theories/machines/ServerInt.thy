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
theory ServerInt
  imports "../model/Syntax"
begin
(*>*)

subsubsection {* Interrupts *}

(* Only encode the data word here, format is standard APIC ICR register format *)
definition "phi0_elapic_rcv0 = 0x29" (* Vec=0x29, Dest=0, Fixed destination mode *) 
definition "phi1_elapic_rcv0 = 0x29" (* Vec=0x29, Dest=0, Fixed destination mode *) 
definition "phi0_msi_write0 = 0x00000000FEE002B800000029"
definition "phi1_msi_write0 = 0x00000000FEE002B80000007D"

definition "x86_vec_domain = (32,255)"

text {* Host LAPIC 0 *}
definition "node_0_lapic0 = empty_spec \<lparr>
  acc_blocks := [x86_vec_domain],
  map_blocks := []
\<rparr>" 
  
text {* Host LAPIC 1 *}
definition "node_1_lapic1 = empty_spec \<lparr>
  acc_blocks := [x86_vec_domain],
  map_blocks := []
\<rparr>" 
  
text {* Core 0 to APICs *}   
definition "node_2_core0 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 3 251]
\<rparr>"
  
text {* Core 1 to APICs *}   
definition "node_3_core1 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 3 251]
\<rparr>"
  
text {* Timer0 to LAPIC0 *}   
definition "node_4_timer0 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 0 32]
\<rparr>"
  
text {* Timer1 to LAPIC1 *}   
definition "node_5_timer1 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 1 32]
\<rparr>"
  
text {* IOMMU to LAPICs. *}              
definition "node_6_iommu = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [
    one_map phi0_msi_write0 0 125,
    one_map phi1_msi_write0 0 126
]
\<rparr>"

text {* Phi0 LAPIC0 *}  
definition "node_7_phi0_lapic0 = empty_spec \<lparr>
  acc_blocks := [x86_vec_domain],
  map_blocks := []
\<rparr>" 

text {* Phi0 LAPIC1 *}  
definition "node_8_phi0_lapic1 = empty_spec \<lparr>
  acc_blocks := [x86_vec_domain],
  map_blocks := []
\<rparr>" 
  
text {* Phi0 Core 0 to APICs *}
definition "node_9_phi0_core0 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 8 251]
\<rparr>"
  
text {* Phi0 Core 1 to APICs *}
definition "node_10_phi0_core1 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 7 251]
\<rparr>"
  
text {* Phi0 Timer0 to Phi0 LAPIC0 *}   
definition "node_11_phi0_timer0 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 7 32]
\<rparr>"
  
text {* Phi0 Timer1 to Phi0 LAPIC1 *}   
definition "node_12_phi0_timer1 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 8 32]
\<rparr>"
  
text {* Phi0 IOAPIC0 -> LAPICs *}              
definition "node_13_phi0_ioapic = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 7 33]
\<rparr>" 
  
text {* Phi0 Thermal to IOAPIC *}              
definition "node_14_phi0_rtc = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 13 0]
\<rparr>" 
  
text {* Phi0 ELAPIC to LAPICs *}
definition "node_15_elapic = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map phi0_elapic_rcv0 7 0x29]
\<rparr>"
  
text {* Phi0 SBOX to IOMMU *}
definition "node_16_sbox = empty_spec \<lparr>
  acc_blocks := [],
 (* There should be a more expressive way of modeling the input *)
  map_blocks := [one_map 0 5 phi0_msi_write0]
\<rparr>"

text {* Phi1 LAPIC0 *}
definition "node_17_phi1_lapic0 = empty_spec \<lparr>
  acc_blocks := [x86_vec_domain],
  map_blocks := []
\<rparr>" 

text {* Phi1 LAPIC1 *}
definition "node_18_phi1_lapic1 = empty_spec \<lparr>
  acc_blocks := [x86_vec_domain],
  map_blocks := []
\<rparr>" 
  
text {* Phi1 Core 0 to APICs *}
definition "node_19_phi1_core0 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 18 251]
\<rparr>"
  
text {* Phi1 Core 1 to APICs *}
definition "node_20_phi1_core1 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 17 251]
\<rparr>"
  
text {* Phi1 Timer0 to Phi1 LAPIC0 *}
definition "node_21_phi1_timer0 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 17 32]
\<rparr>"
  
text {* Phi1 Timer1 to Phi1 LAPIC1 *}
definition "node_22_phi1_timer1 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 18 32]
\<rparr>"
  
text {* Phi1 IOAPIC0 to LAPICs *}              
definition "node_23_phi1_ioapic = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 17 33]
\<rparr>" 
  
text {* Phi1 Thermal to IOAPIC *}              
definition "node_24_phi1_rtc = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 23 0]
\<rparr>" 
  
text {* Phi1 ELAPIC to LAPICs *}              
definition "node_25_elapic = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map phi1_elapic_rcv0 17 0x29]
\<rparr>"
  
text {* Phi1 SBOX to IOMMU *}              
definition "node_26_sbox = empty_spec \<lparr>
  acc_blocks := [],
 (* There should be a more expressive way of modeling the input *)
  map_blocks := [one_map 0 5 phi1_msi_write0]
\<rparr>"
  
definition "sys = [
  (0,node_0_lapic0),
  (1,node_1_lapic1),
  (2,node_2_core0),
  (3,node_3_core1),
  (4,node_4_timer0),
  (5,node_5_timer1),
  (6,node_6_iommu),
  (7,node_7_phi0_lapic0),
  (8,node_8_phi0_lapic1),
  (9,node_9_phi0_core0),
  (10,node_10_phi0_core1),
  (11,node_11_phi0_timer0),
  (12,node_12_phi0_timer1),
  (13,node_13_phi0_ioapic),
  (14,node_14_phi0_rtc),
  (15,node_15_elapic),
  (16,node_16_sbox),
  (17,node_17_phi1_lapic0),
  (18,node_18_phi1_lapic1),
  (19,node_19_phi1_core0),
  (20,node_20_phi1_core1),
  (21,node_21_phi1_timer0),
  (22,node_22_phi1_timer1),
  (23,node_23_phi1_ioapic),
  (24,node_24_phi1_rtc),
  (25,node_25_elapic),
  (26,node_26_sbox)
]"

end