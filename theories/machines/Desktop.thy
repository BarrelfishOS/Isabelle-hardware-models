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
theory Desktop
  imports "../model/Syntax"
begin
(*>*)

subsubsection {* Address spaces *}

text {* The Interconnect *}              
definition "dram_sys0 = (0x0000000000100000, 0x00000000C00FFFFF)" 
definition "dram_sys1 = (0x0000000100000000, 0x000000083FFFFFFF)"
definition "pci_devs =  (0x00000000C0800000, 0x00000000C2FFFFFF)"
definition "node_0_interconnect = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [block_map dram_sys0 1 0x0, block_map dram_sys1 1 0xC0000000,
                 direct_map pci_devs 2]
\<rparr>" 
  
text {* The DRAM Controller: has 2 channels with 16G each. *}
definition "dram0 = (0x000000000, 0x3FFFFFFFF)"
definition "dram1 = (0x400000000, 0x7FFFFFFFF)"
definition "node_1_dram = empty_spec \<lparr>
  acc_blocks := [dram0, dram1],
  map_blocks := []
\<rparr>"

text {* The PCI Root Complex *}
definition "xhci  = (0xC1580000, 0xC158FFFF)"
definition "e1000 = (0xC1300000, 0xC13FFFFF)"
definition "ahci  = (0xC1520000, 0xC15207FF)"
definition "vga2  = (0xC1010000, 0xC1013FFF)"
definition "vga1  = (0xC2000000, 0xC2FFFFFF)"
  
definition "vga4  = (0xC1000000, 0xC100FFFF)"
definition "vga3  = (0xC0800000, 0xC0FFFFFF)"
  
definition "node_2_pci = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [direct_map dram_sys0 0, direct_map dram_sys1 0, 
                 direct_map xhci 3, direct_map e1000 4, 
                 direct_map ahci 5, direct_map vga1 6, 
                 direct_map vga2 6]
\<rparr>"

text {* XHCI USB Host Controller *} 
definition "node_3_xhci = empty_spec \<lparr>
  acc_blocks := [xhci],
  map_blocks := [direct_map dram_sys0 2, direct_map dram_sys1 2]
\<rparr>"
  
text {* PCI Network Card *} 
definition "node_4_e1000 = empty_spec \<lparr>
  acc_blocks := [e1000],
  map_blocks := [direct_map dram_sys0 2, direct_map dram_sys1 2]
\<rparr>"
  
text {* AHCI Disk Controller *} 
definition "node_5_ahci = empty_spec \<lparr>
  acc_blocks := [ahci],
  map_blocks := [direct_map dram_sys0 2, direct_map dram_sys1 2]
\<rparr>"
  
text {* Graphics Card *} 
definition "node_6_vga = empty_spec \<lparr>
  acc_blocks := [vga1, vga2],
  map_blocks := [direct_map dram_sys0 2, direct_map dram_sys1 2]
\<rparr>"


text {* CPU Cores*}
definition "lapic = (0xFEE00000, 0xFEE0FFFF)"
definition "cpu_phys = empty_spec \<lparr>
  acc_blocks := [lapic],
  overlay := Some 0
\<rparr>"
  
definition "cpu_virt0 = empty_spec \<lparr>
  acc_blocks := [],
  overlay := Some 7
\<rparr>"
definition "cpu_virt1 = empty_spec \<lparr>
  acc_blocks := [],
  overlay := Some 8
\<rparr>"
definition "cpu_virt2 = empty_spec \<lparr>
  acc_blocks := [],
  overlay := Some 9
\<rparr>"
definition "cpu_virt3 = empty_spec \<lparr>
  acc_blocks := [],
  overlay := Some 10
\<rparr>"
  
definition "sys = [(0, node_0_interconnect), 
                   (1, node_1_dram), 
                   (2, node_2_pci), 
                   (3, node_3_xhci), 
                   (4, node_4_e1000), 
                   (5,node_5_ahci), 
                   (6,node_6_vga), 
                   (7,cpu_phys), 
                   (8,cpu_phys),
                   (9,cpu_phys), 
                   (10,cpu_phys), 
                   (11,cpu_virt0), 
                   (12,cpu_virt1), 
                   (13,cpu_virt2),
                   (14,cpu_virt3) ]"
    
end