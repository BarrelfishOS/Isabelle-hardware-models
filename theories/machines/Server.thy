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
theory Server
  imports "../model/Syntax"
begin
(*>*)

subsubsection {* Address spaces *}

text {* DRAM *}
definition "dram_sys0 = (0x0000000000000000,0x000000000009BFFF)" 
definition "dram_sys1 = (0x0000000000100000,0x00000000BAD27FFF)"
definition "dram_sys2 = (0x00000000BAF90000,0x00000000BAFC4FFF)"
definition "dram_sys3 = (0x00000000BAFDA000,0x00000000BB3D3FFF)"
definition "dram_sys4 = (0x00000000BDFAC000,0x00000000BDFFFFFF)"
definition "dram_sys5 = (0x0000000100000000,0x000000203FFFFFFF)"
definition "dram_sys6 = (0x0000002040000000,0x000000403FFFFFFF)"

text {* PCI Express Ranges *}
definition "pci_lo_0 = (0xD0000000,0xD0EFFFFF)"
definition "pci_lo_1 = (0xEC000000,0xEC1FFFFF)" 
definition "pci_hi_0 = (0x0000380000000000,0x00003802009FFFFF)"
definition "pci_hi_1 = (0x0000380400000000,0x00003806007FFFFF)"

text {* The Node 0 Interconnect *}              
definition "node_0_interconnect = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [block_map dram_sys0 2 0x000000000, block_map dram_sys1 2 0x9C000,
                 block_map dram_sys2 2 0xBACC4000, block_map dram_sys3 2 0xBACF9000, 
                 block_map dram_sys4 2 0xBB0F3000, block_map dram_sys5 2 0xBB147000,
                 direct_map dram_sys6 1, direct_map pci_lo_0 4, 
                 direct_map pci_hi_0 4, direct_map pci_lo_1 1, 
                 direct_map pci_hi_1 1]
\<rparr>"

text {* The Node 1 Interconnect *}              
definition "node_1_interconnect = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [direct_map dram_sys0 0, direct_map dram_sys1 0,  
                 direct_map dram_sys2 0, direct_map dram_sys3 0, 
                 direct_map dram_sys4 0, direct_map dram_sys5 0, 
                 block_map dram_sys6 3 0x02000000000,  
                 direct_map pci_lo_0 0, direct_map pci_hi_0 0, 
                 direct_map pci_lo_1 5, direct_map pci_hi_1 5]
\<rparr>" 
  
text {* DRAM controller 0: 4 channels with 32G each. *}
definition "dram0_0 = (0x00000000000, 0x007FFFFFFFF)"
definition "dram0_1 = (0x00800000000, 0x00FFFFFFFFF)"
definition "dram0_2 = (0x01000000000, 0x017FFFFFFFF)"  
definition "dram0_3 = (0x01800000000, 0x01FFFFFFFFF)"
definition "node_2_dram = empty_spec \<lparr>
  acc_blocks := [dram0_0, dram0_1, dram0_2, dram0_3],
  map_blocks := []
\<rparr>"
  
text {* DRAM controller 1: 4 channels with 32G each *}
definition "dram1_0 = (0x02000000000, 0x027ffffffff)"
definition "dram1_1 = (0x02800000000, 0x02FFFFFFFFF)"
definition "dram1_2 = (0x03000000000, 0x037FFFFFFFF)"  
definition "dram1_3 = (0x03800000000, 0x03FFFFFFFFF)"
definition "node_3_dram = empty_spec \<lparr>
  acc_blocks := [dram1_0, dram1_1, dram1_2, dram1_3],
  map_blocks := []
\<rparr>"

text {* PCI Express Devices *}
definition "phi0_gddr = (0x380000000000, 0x3801FFFFFFFF)"
definition "phi0_mmio = (0xD0C00000, 0xd0C1FFFF)"
definition "phi1_gddr = (0x380400000000, 0x3805FFFFFFFF)"
definition "phi1_mmio = (0xDC200000, 0xEC21FFFF)"  
definition "dma0 = (0x3803FFF90000, 0x3803FFF23FFF)"
definition "dma1 = (0x3807FFF60000, 0x3807FFF03FFF)"
definition "ahci = (0xD0F00000, 0xD0F007FF)"
definition "ehci = (0xD0F10000, 0xD0F103FF)"
definition "ioapic0 = (0xD0F60000, 0xD0F60FFF)"
definition "ioapic1 = (0xEC300000, 0xEC300FFF)"
definition "e1000 = (0xD0960000, 0xD097FFFFF)"

text {* PCI Root Complex 0 *} 
definition "node_4_pci = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [direct_map dram_sys0 0, direct_map dram_sys1 0, 
                 direct_map dram_sys2 0, direct_map dram_sys3 0, 
                 direct_map dram_sys4 0, direct_map dram_sys5 0, 
                 direct_map dram_sys6 0, direct_map dma0 9, 
                 direct_map ahci 12, direct_map ehci 11, 
                 direct_map ioapic0 7, direct_map e1000 6,
                 block_map phi0_gddr 13 0x0, 
                 block_map phi0_mmio 13 0x08007D0000]
\<rparr>"
  
text {* PCI Root Complex 1 *}
definition "node_5_pci = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [direct_map dram_sys0 0, direct_map dram_sys1 0, 
                 direct_map dram_sys2 0, direct_map dram_sys3 0, 
                 direct_map dram_sys4 0, direct_map dram_sys5 0, 
                 direct_map dram_sys6 0, direct_map dma1 10,
                 direct_map ioapic1 8, direct_map dma1 10,
                 block_map phi1_gddr 13 0, 
                 block_map phi1_mmio 13 0x08007D0000]
\<rparr>"  

text {* e1000 Network Card *} 
definition "node_6_e1000 = empty_spec \<lparr>
  acc_blocks := [e1000],
  overlay := Some 4
\<rparr>"

text {* IO APICs *}
definition "node_7_ioapic = empty_spec \<lparr>
  acc_blocks := [ioapic0],
  overlay := Some 4
\<rparr>"

definition "node_8_ioapic = empty_spec \<lparr>
  acc_blocks := [ioapic1],
  overlay := Some 5
\<rparr>"

text {* DMA Engines *}
definition "node_9_dma = empty_spec \<lparr>
  acc_blocks := [dma0],
  overlay := Some 4
\<rparr>"

definition "node_10_dma = empty_spec \<lparr>
  acc_blocks := [dma1],
  overlay := Some 5
\<rparr>"
  
text {* USB Host Controller *} 
definition "node_11_ehci = empty_spec \<lparr>
  acc_blocks := [ehci],
  overlay := Some 4
\<rparr>"
  
text {* AHCI Disk controller *} 
definition "node_12_ahci = empty_spec \<lparr>
  acc_blocks := [ahci],
  overlay := Some 4
\<rparr>"

text {* Xeon Phi 0 *}

definition "phi_gddr = (0, 0x180000000)"
definition "phi_sbox = (0x08007D0000,0x8007E0000)"
definition "phi_sysmem = (0x8000000000, 0xFFFFFFFFFF)"
definition "phi_lut_e00 = (0x0000000000, 0x03FFFFFFFF)"  

definition "node_13_phi = empty_spec \<lparr>
  acc_blocks := [phi_gddr, phi_sbox],
  map_blocks := [block_map phi_sysmem 14 0x0]
\<rparr>"

definition "node_14_lut0 = empty_spec \<lparr>
  acc_blocks := [],
   map_blocks := [block_map phi_lut_e00 17 0x0]
\<rparr>"

text {* Xeon Phi 1 *}

definition "node_15_phi = empty_spec \<lparr>
  acc_blocks := [phi_gddr, phi_sbox],
  map_blocks := [block_map phi_sysmem 16 0x0]
\<rparr>"

definition "node_16_lut1 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [block_map phi_lut_e00 18 0x0]
\<rparr>"

text {* IO-MMU *}
definition "iommu_map = (0x0000000000, 0x03FFFFFFFF)"  

definition "node_17_iommu = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [direct_map iommu_map 4]
\<rparr>"

definition "node_18_iommu = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [direct_map iommu_map 5]
\<rparr>" 

text {* CPU Cores *}
definition "lapic = (0xFEE00000, 0xFEE0FFFF)"
definition "cpu_phys0 = empty_spec \<lparr>
  acc_blocks := [lapic],
  overlay := Some 0
\<rparr>"

definition "cpu_phys1 = empty_spec \<lparr>
  acc_blocks := [lapic],
  overlay := Some 1
\<rparr>"

definition "cpu_phi0 = empty_spec \<lparr>
  acc_blocks := [lapic],
  overlay := Some 13
\<rparr>"

definition "cpu_phi1 = empty_spec \<lparr>
  acc_blocks := [lapic],
  overlay := Some 15
\<rparr>"

definition "sys = [(0, node_0_interconnect), 
                   (1, node_1_interconnect), 
                   (2, node_2_dram), 
                   (3, node_3_dram), 
                   (4, node_4_pci), 
                   (5, node_5_pci), 
                   (6, node_6_e1000), 
                   (7, node_7_ioapic), 
                   (8, node_8_ioapic), 
                   (9, node_9_dma), 
                   (10, node_10_dma),
                   (11, node_11_ehci), 
                   (12, node_12_ahci), 
                   (13, node_13_phi),
                   (14, node_14_lut0), 
                   (15, node_15_phi), 
                   (16, node_16_lut1),
                   (17, node_17_iommu), 
                   (18, node_18_iommu)] @
                   repeat_node cpu_phys0 20 10 @
                   repeat_node cpu_phys1 30 10 @
                   repeat_node cpu_phi0 40 60 @
                   repeat_node cpu_phi1 100 60"
end