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
theory SCC
  imports "../model/Syntax"
begin
(*>*)

subsubsection {* Model representation *}
text_raw {* \label{isabelle:scc} *}

text {* Memory Controllers: 16GB each *} 
definition "dram = (0x000000000,0x3FFFFFFFF)" 
definition "node_mc = empty_spec \<lparr>
  acc_blocks := [dram],
  map_blocks := []
\<rparr>"

text {* Local Memory / Message Passing buffer of 16kB *}
definition "lmb = (0x000, 0xFFFF)"
definition "node_lmb = empty_spec \<lparr>
  acc_blocks := [lmb],
  map_blocks := []
\<rparr>"

text {* Local Configuration Registers *}
definition "conf = (0x000000, 0x7FFFFF)"
definition "node_conf = empty_spec \<lparr>
  acc_blocks := [conf],
  map_blocks := []
\<rparr>"

text {* 2D Mesh Network *}
definition "dram0 = (0x001800000000,0x001BFFFFFFFF)"
definition "dram1 = (0x00F000000000,0x0013FFFFFFFF)"
definition "dram2 = (0x041800000000,0x031BFFFFFFFF)"
definition "dram3 = (0x04F000000000,0x03F3FFFFFFFF)"

definition "conf_00 = (0x000800000000, 0x0008007FFFFF)"
definition "conf_01 = (0x002800000000, 0x0028007FFFFF)"
definition "mpb_00  = (0x000C00000000, 0x000c007FFFFF)"
definition "mbp_01  = (0x002C00000000, 0x002c007FFFFF)"  
definition "sif     = (0x00F400000000, 0x00F7FFFFFFFF)" 
definition "node_0_interconnect = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [block_map dram0 1 0x0, block_map dram1 2 0x0,
                 block_map dram2 2 0x0, block_map dram3 3 0x0,
                 block_map mpb_00 4 0x0, block_map mbp_01 5 0x0,
                 block_map conf_00 6 0x0, block_map conf_01 7 0x0,
                 block_map sif 44 0x0]
\<rparr>"
  
text {* Core 0.0 *}
definition "vram = (0x0000000, 0x0FFFFFF)"
definition "node_9_vas00 =  empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [block_map vram 10 0x0 ]
\<rparr>"
  
definition "cpu_phys =  empty_spec \<lparr>
  acc_blocks := [],
  overlay := Some 11
\<rparr>"

definition "lut00_cfg = (0x3000000, 0x3FFFFFF)"
definition "lut00_mpb = (0x1000000, 0x1FFFFFF)"
definition "node_11_lut00  =  empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [block_map lut00_cfg 5 0x0, block_map lut00_mpb 6 0x0],
  overlay := Some 0
\<rparr>"
  
text {* Core 1.0 *}
definition "node_12_vas01 =  empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [block_map vram 13 0x0 ]
\<rparr>"

definition "lut01_cfg = (0x3000000, 0x3FFFFFF)"
definition "lut01_mpb = (0x1000000, 0x1FFFFFF)"
definition "node_14_lut01  =  empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [block_map lut01_cfg 6 0x0, block_map lut01_mpb 7 0x0],
  overlay := Some 0
\<rparr>"
  
definition "sys = [(0, node_0_interconnect), 
                   (1,node_mc),  
                   (2,node_mc),  
                   (3,node_mc),  
                   (4,node_mc),
                   (5,node_lmb),  
                   (6,node_lmb),  
                   (7,node_conf),  
                   (8,node_conf), 
                   (9, node_9_vas00),
                   (10, cpu_phys),  
                   (11, node_11_lut00), 
                   (12, node_12_vas01), 
                   (13, cpu_phys), 
                   (14, node_14_lut01)
]"

end