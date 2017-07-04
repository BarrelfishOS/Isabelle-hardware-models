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
theory DesktopInt
  imports "../model/Syntax"
begin
(*>*)

subsubsection {* Interrupts *}

text {* Convention: Interrupt issuing devices start at their 
        node with address 0. If it can trigger multiple interrupts,
        it issues contiguous addresses starting from zero.  *}  
  
text {* Convention: MSI uses memory 32bit memory writes. We encode such a memory write by
        concatenating the 64bit address with the 32bit data word. *} 

definition "gfx_msi_write = 0x00000000FEE002b800000029"
definition "nic_msi_write0 = 0x00000000FEE002b80000007D"
definition "nic_msi_write1 = 0x00000000FEE002b80000007E"
definition "nic_msi_write2 = 0x00000000FEE002b80000007F"
definition "nic_msi_write3 = 0x00000000FEE002b800000080"
definition "nic_msi_write4 = 0x00000000FEE002b800000081"
  
definition "x86_vec_domain = (32,255)"
  
text {* LAPIC 0 *}
definition "node_0_lapic_0 = empty_spec \<lparr>
  acc_blocks := [x86_vec_domain],
  map_blocks := []
\<rparr>" 
  
text {* LAPIC 1 *}
definition "node_1_lapic_1 = empty_spec \<lparr>
  acc_blocks := [x86_vec_domain],
  map_blocks := []
\<rparr>" 
  
text {* LAPIC 2 *}
definition "node_2_lapic_2 = empty_spec \<lparr>
  acc_blocks := [x86_vec_domain],
  map_blocks := []
\<rparr>"
 
text {* LAPIC 3 *}
definition "node_3_lapic_3 = empty_spec \<lparr>
  acc_blocks := [x86_vec_domain],
  map_blocks := []
\<rparr>" 
  
text {* IOAPIC 0 to LAPIC *}              
definition "node_4_ioapic = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 4 0 48, one_map 8 0 40]
\<rparr>" 
  
text {* LNKA to IOAPIC *}              
definition "node_5_lnka = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 4 4]
\<rparr>" 
  
text {* USB EHCI to LNKA *}              
definition "node_6_usb = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 5 0]
\<rparr>" 
  
text {* RTC to IOAPIC *}              
definition "node_7_rtc = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 4 8]
\<rparr>" 
  
text {* PCH to LAPICs. *}              
definition "node_8_pch = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [
    one_map nic_msi_write0 0 125, 
    one_map nic_msi_write1 0 126, 
    one_map nic_msi_write2 0 127, 
    one_map nic_msi_write3 0 128, 
    one_map nic_msi_write4 0 129, 
    one_map gfx_msi_write 0 41   
]
\<rparr>"
  
text {* NIC to PCH. Uses 5 interrupts. *}   
definition "node_9_nic = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [
    one_map 0 8 nic_msi_write0,
    one_map 1 8 nic_msi_write1,
    one_map 2 8 nic_msi_write2,
    one_map 3 8 nic_msi_write3,
    one_map 4 8 nic_msi_write4
]
\<rparr>"
  
text {* GFX to PCH. Uses 1 interrupt. *}   
definition "node_18_gfx = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [
    one_map 0 8 gfx_msi_write
]
\<rparr>"
  
text {* Timer0 to LAPIC0 *}   
definition "node_10_timer0 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 0 32]
\<rparr>"
  
text {* Timer1 to LAPIC1 *}   
definition "node_11_timer1 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 1 32]
\<rparr>"
  
text {* Timer2 to LAPIC2 *}   
definition "node_12_timer2 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 2 32]
\<rparr>"
  
text {* Timer3 to LAPIC3 *}   
definition "node_13_timer3 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 3 32]
\<rparr>"
  
text {* TODO:  needs the set destination to make sense. We use the TLB shootdown IPI
as example *}  
text {* Core 0 to Other APICs. *}   
definition "node_14_core0 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [
    one_map 0 3 251 (* [(1,251),(2,251),(3,251)] *)
    ] 
\<rparr>"
  
text {* Core 1 to Other APICs. *}   
definition "node_15_core1 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [
    one_map 0 3 251, (* [(0,251),(2,251),(3,251)] *)
    one_map 1 0 48
    ]
\<rparr>"
  
text {* Core 2 to Other APICs. *}   
definition "node_16_core2 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [
    one_map 0 3 251 (* [(0,251),(1,251),(3,251)] *)
    ]
\<rparr>"
  
text {* Core 3 to Other APICs. *}   
definition "node_17_core3 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [
    one_map 0 3 251 (* [(0,251),(1,251),(3,251)] *)
    ]
\<rparr>"

definition "sys = [
  (0,node_0_lapic_0),
  (1,node_1_lapic_1),
  (2,node_2_lapic_2),
  (3,node_3_lapic_3),
  (4,node_4_ioapic),
  (5,node_5_lnka),
  (6,node_6_usb),
  (7,node_7_rtc),
  (8,node_8_pch),
  (9,node_9_nic),
  (10,node_10_timer0),
  (11,node_11_timer1),
  (12,node_12_timer2),
  (13,node_13_timer3),
  (14,node_14_core0),
  (15,node_15_core1),
  (16,node_16_core2),
  (17,node_17_core3),
  (18,node_18_gfx)
]"

end