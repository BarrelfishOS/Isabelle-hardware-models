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
theory OMAP44xx
  imports "../model/Syntax"
begin
(*>*)

subsubsection {* Address spaces *}

text {* RAM *}
definition "ram = (0x80000000, 0xBFFFFFFF)"
definition "node_1_ram = empty_spec \<lparr>
  acc_blocks := [ram],
  map_blocks := []
\<rparr>"

text {* General-Purpose Timer 5 *}
definition "gptimer5 = (0x0, 0x1000)"
definition "node_2_gptimer5 = empty_spec \<lparr>
  acc_blocks := [gptimer5],
  map_blocks := []
\<rparr>"

text {* The L3 Interconnect *}
definition "l3_boot = (0x00000000, 0x40000000)"
definition "l3_l4 = (0x49000000, 0x49FFFFFF)"
definition "l3_sdma = (0x4A056000, 0x4A056FFF)"
definition "l3_ram = (0x8000000, 0xBFFFFFFF)"

definition "node_3_l3_interconnect = empty_spec \<lparr>
  acc_blocks := [l3_boot],
  map_blocks := [direct_map l3_ram 1, direct_map l3_l4 2, direct_map l3_sdma 3 ]
\<rparr>"


text {* The L4 Interconnect *}
definition "l4_gptimer5_a9_module = (0x40138000, 0x40138FFF)"
definition "l4_gptimer5_a9_l4 = (0x40139000, 0x40139FFF)"
definition "l4_gptimer5_l3_module = (0x49038000, 0x49038FFF)"
definition "l4_gptimer5_l3_l4 = (0x49039000, 0x49039FFF)"

definition "l4_gptimer5_dsp_module = (0x01D38000, 0x01D38FFF)"
definition "l4_gptimer5_dsp_l4 = (0x01D39000, 0x01D39FFF)"

  
definition "l4_sdma_module = (0x4A056000, 0x4A056FFFF)"
definition "l4_sdma_l4 = (0x4A057000, 0x4A057FFF)"

definition "node_4_l4_interconnect = empty_spec \<lparr>
  acc_blocks := [l3_boot],
  map_blocks := []
\<rparr>"
  
 
text {* The DSP Subsystem *}  
definition "dspvirt_gptimer = (0x1000000, 0x10000FFF)"
definition "dspvirt_ram = (0x2000000, 0x5FFFFFF)"
definition "node_5_dspvirt = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [block_map dspvirt_gptimer 6 0x01D38000, 
                 block_map dspvirt_ram 6 0x8000000]
\<rparr>"

definition "dspphys_ram =  (0x80000000, 0xBFFFFFFF)"
definition "dspphys_gptimer5 = (0x01D38000, 0x01D38FFF)"
definition "node_6_dspphys = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [direct_map dspphys_ram 3, block_map dspphys_gptimer5 2 0]
\<rparr>"

text {* The SDMA Module *}
definition "sdma = (0x4A056000, 0x4A056FFF)"
definition "node_7_sdma = empty_spec \<lparr>
  acc_blocks := [sdma],
  map_blocks := [direct_map ram 1]
\<rparr>"

text {* The Cortex A9 MPU Subsystem *}
definition "a9_0_virt_ram =  (0x00000000, 0x3FFFFFFF)"
definition "a9_0_virt_gptimer_priv = (0x60000000, 0x60000FFF)"
definition "a9_0_virt_gptimer = (0x60001000, 0x60001FFF)"
definition "a9_0_virt_sdma = (0x60002000, 0x60002FFF)"

definition "node_8_a9virt_0 =  empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [block_map a9_0_virt_ram 9 0x8000000, 
                 block_map a9_0_virt_gptimer_priv 9 0x40138000, 
                 block_map a9_0_virt_gptimer 9 0x49038000, 
                 block_map a9_0_virt_sdma 9 0x4A056000]
\<rparr>"

definition "a9_0_phys_ram = (0x800000000, 0xBFFFFFFF)"
definition "a9_0_phys_gptimer_priv = (0x40138000, 0x40138FFF)"
definition "a9_0_phys_gptimer = (0x49038000, 0x49038FFF)"
definition "a9_0_phys_sdma = (0x4A056000, 0x4A056FFF)"
definition "node_9_a9phys_0 =  empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [direct_map a9_0_phys_ram 3, direct_map a9_0_phys_gptimer_priv 4,
                 direct_map a9_0_phys_gptimer 3, direct_map a9_0_phys_sdma 3]
\<rparr>"

definition "a9_1_virt_ram = (0x10000000, 0x4FFFFFFF)"
definition "a9_1_virt_gptimer_priv = (0x70000000, 0x70000FFF)"
definition "a9_1_virt_gptimer = (0x70001000, 0x70001FFF)"
definition "a9_1_virt_sdma = (0x70001000, 0x70001FFF)"
  
definition "node_10_a9virt_1 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [block_map a9_1_virt_ram 11 0x8000000, 
                 block_map a9_1_virt_gptimer_priv 11 0x40138000, 
                 block_map a9_1_virt_gptimer 11 0x49038000, 
                 block_map a9_1_virt_sdma 11 0x4A056000]
\<rparr>"

definition "a9_1_phys_ram = (0x800000000, 0xBFFFFFFF)"
definition "a9_1_phys_gptimer_priv =  (0x40138000, 0x40138FFF)"
definition "a9_1_phys_gptimer = (0x49038000, 0x49038FFF)"
definition "a9_1_phys_sdma = (0x4A056000, 0x4A056FFF)"
definition "node_11_a9phys_1 =  empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [direct_map a9_1_phys_ram 3, direct_map a9_1_phys_gptimer_priv 4,
                 direct_map a9_1_phys_gptimer 3, direct_map a9_1_phys_sdma 3]
\<rparr>"

text {* The Cortex M3 Subsystem *}
  
definition "m3_virt_ram_0  = (0x10000000, 0x4FFFFFF)"
definition "m3_virt_local_rom_0 = (0x50000000, 0x50003FFF)"
definition "m3_virt_local_ram_0 = (0x50020000, 0x5002FFFF)"
definition "node_12_m3_virt_0 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [block_map m3_virt_ram_0 13 0x00000000, 
                 block_map m3_virt_local_rom_0 13 0x55000000,
                 block_map  m3_virt_local_ram_0 13 0x55020000  ]
\<rparr>"  

definition "m3_local_ram = (0x55020000, 0x5502FFFF)"
definition "m3_local_rom = (0x55000000, 0x55003FFF)"
definition "m3_l3 = (0x00000000, 0x5FFFFFF)"
definition "node_13_m3_l2_mif = empty_spec \<lparr>
  acc_blocks := [m3_local_ram,m3_local_rom],
  map_blocks := [direct_map m3_l3 14]
\<rparr>"

definition "node_14_m3_phys = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [block_map m3_l3 3 0x8000000 ]
\<rparr>"

definition "sys = [(1,node_1_ram), 
                   (2, node_2_gptimer5), 
                   (3, node_3_l3_interconnect),
                   (4, node_4_l4_interconnect),
                   (5, node_5_dspvirt), 
                   (6, node_6_dspphys), 
                   (7, node_7_sdma), 
                   (8,node_8_a9virt_0), 
                   (9, node_9_a9phys_0), 
                   (10, node_10_a9virt_1), 
                   (11, node_11_a9phys_1), 
                   (12,node_12_m3_virt_0 ), 
                   (13,node_13_m3_l2_mif), 
                   (14, node_14_m3_phys)]"
end