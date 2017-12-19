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
theory Cluster
  imports "../model/Syntax"
begin
(*>*)

subsubsection {* Model representation *}

definition "dram = blockn 0x0000000000000000 0x000000203FFFFFFF" 
definition "pci  = blockn 0x0000380000000000 0x00003802009FFFFF"

text {* The Interconnect: *}
  
definition "node_0_m0_interconnect = empty_spec \<lparr>
  acc_blocks := [dram],
  map_blocks := [direct_map pci 2]
\<rparr>"
  
definition "node_1_m1_interconnect = empty_spec \<lparr>
  acc_blocks := [dram],
  map_blocks := [direct_map pci 3]
\<rparr>"
  
text {* PCI Root Complexes: *}
  
definition "node_2_m0_pci = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [direct_map dram 0, direct_map pci 2]
\<rparr>"
  
definition "node_3_m1_pci = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [direct_map dram 1, direct_map pci 3]
\<rparr>"
  
text {* Infiniband Cards (RDMA): *}
  
definition "remote_ram = blockn 0x0000000000000000 0x0000000203FFFFFF"
definition "host_ram   = blockn 0x0000800000000000 0x0008000203FFFFFF"
definition "node_4_m1_cx3 = empty_spec \<lparr>
  acc_blocks := [pci],
  map_blocks := [block_map host_ram 6 0x0, block_map remote_ram 5 0x000800000000000]
\<rparr>"
definition "node_5_m1_cx3 = empty_spec \<lparr>
  acc_blocks := [pci],
  map_blocks := [block_map host_ram 7 0x0, block_map remote_ram 4 0x00080000000000]
\<rparr>"

text {* MMUs: *}
  
definition "node_6_m1_tab = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [],
  overlay := Some 8
\<rparr>"
definition "node_7_m1_tab = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [],
  overlay := Some 9
\<rparr>"
  
text {* IO-MMUs: *}
  
definition "node_8_m1_iommu = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [direct_map dram 2]
\<rparr>"
definition "node_9_m1_iommu = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [direct_map dram 3]
\<rparr>"

definition "sys = [(0, node_0_m0_interconnect), 
                   (1, node_1_m1_interconnect), 
                   (2, node_2_m0_pci), 
                   (3, node_3_m1_pci), 
                   (4, node_4_m1_cx3), 
                   (5, node_5_m1_cx3), 
                   (6, node_6_m1_tab), 
                   (7, node_7_m1_tab), 
                   (8, node_8_m1_iommu), 
                   (9, node_9_m1_iommu)]"

end