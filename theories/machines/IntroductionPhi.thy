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


theory IntroductionPhi
  imports "../model/Syntax"
begin

text {* mapped physical addresses of DRAM *}
definition "dram_sys0 =  blockn 0x0000000000000000 0x0000001fffffffff" 

text {* PCI Express Ranges *}
definition "pci_mmio = blockn 0xd000000000 0xd000efffff"
definition "pci_aperture = blockn 0x380000000000 0x3802009fffff"

text {* node 0: the node 0 interconnect *}              
definition "node_0_interconnect = empty_spec \<lparr>
  acc_blocks := [dram_sys0],
  map_blocks := [direct_map pci_mmio 1, direct_map pci_aperture 1]
\<rparr>"

text {* PCI Express devices *}

text {* node 1: the PCI root complex *} 
definition "node_1_pci = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [direct_map dram_sys0 0, block_map pci_mmio 2 0x08007d0000, block_map pci_aperture 2 0x0]
\<rparr>"
  
text {* node 2: Xeon Phi co-processor *}
definition "phi_gddr = blockn 0  0x180000000"
definition "phi_sbox = blockn 0x08007d0000 0x8007e0000"
definition "phi_sysmem = blockn 0x8000000000 0xffffffffff"
definition "node_2_phi = empty_spec \<lparr>
  acc_blocks := [phi_gddr,phi_sbox ],
  map_blocks := [block_map phi_sysmem 3 0x0]
\<rparr>"  

definition "node_3_lut = empty_spec \<lparr>
  acc_blocks := [],
  overlay := Some 1
\<rparr>" 

definition "sys = [(0, node_0_interconnect), (1, node_1_pci), (2, node_2_phi), 
                   (3, node_3_lut)]"

end