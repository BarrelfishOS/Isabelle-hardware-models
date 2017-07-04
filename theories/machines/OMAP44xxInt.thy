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
theory OMAP44xxInt
  imports "../model/Syntax"
begin
(*>*)

subsubsection {* Interrupts *}

text {* Note: The DSP core is under NDA. The public datasheet only states 
which interrupts are delivered to the DSP, but not under which vector. Therefore,
the vector numbers have been assumed to be the same as the for the M3 subsystem *}

text {* Interrupt domains according to ARM GICv2 specification *}
definition "sgi_domain = (0,15)" (* Software generated interrupts *)
definition "ppi_domain = (16,31)" (* Private peripheral interrupts *)
definition "spi_domain = (32,1019)" (* Shared peripheral interrupts *)
definition "arm_vec_domain = (0,1020)" (* DSP/M3 input *)
  
text {* A9 Core 0. Can create SGI on A9 Core 1. *}
definition "node_0_a9_0 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 1 0] 
\<rparr>" 

text {* A9 Core 1. Can create SGI on A9 core 0. *}
definition "node_1_a9_1 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 0 0] 
\<rparr>" 
  
text {* 2: DSP. Cannot create interrupts. *}
definition "node_2_dsp = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := []
\<rparr>" 
  
text {* M3 Core 0. Cannot create interrupts. *}
definition "node_3_m3_0 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := []
\<rparr>" 

text {* M3 Core 1. Cannot create interrupts. *}
definition "node_4_m3_1 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := []
\<rparr>" 

text {* A9 CPU IF 0 *}
definition "node_5_if_a9_0 = empty_spec \<lparr>
  acc_blocks := [ppi_domain, sgi_domain, spi_domain],
  map_blocks := []
\<rparr>"
  
text {* A9 CPU IF 1 *}
definition "node_6_if_a9_1 = empty_spec \<lparr>
  acc_blocks := [ppi_domain, sgi_domain, spi_domain],
  map_blocks := []
\<rparr>"
  
text {* GIC Dist: The GIC can't change vector numbers, but destination for SPIs is configurable. *}
definition "node_7_gic = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [
  one_map 73 5 73,                (* GPTIMER5 41+32  to core 0 *) 
  one_map 131 5 131,              (* Audio 99+32 to core 0 *)
  one_map 132 5 132,              (* M3 MMU2 100+32 *)
  one_map 44 5 44,                (* SDMA interrupts: 12-15+32 to core 0 *)
  one_map 45 5 45,                (* ... to core 0 *)
  one_map 46 6 46,                (* ... to core 1 *)
  one_map 47 6 47                 (* ... to core 1 *)
]
\<rparr>"
  
text {* DSP INTC: Since the GIC accepts SDMA/interrupts, it must not be accepted here. In
 fact, we do not accept any interrupts, which corresponds to masking everything *}
definition "node_8_dsp_intc = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := []
\<rparr>"

text {* NVIC 0: Since the GIC accepts SDMA/ interrupts, it must not be accepted here. *}
definition "node_9_nvic_0 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [] 
\<rparr>"
  
text {* NVIC 1  *}
definition "node_10_nvic_1 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := []
\<rparr>"

text {*  A9 Core 0 Private Timer *}
definition "node_11_pt_0 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 5 29] 
\<rparr>"
  
text {* A9 Core 1 Private Timer. *}
definition "node_12_pt_1 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 6 29]  
\<rparr>"
  
text {* GPTIMER5: DSP is under NDA, vec 41 is guessed. *}
definition "node_13_gptimer5 = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 16 41] (* destination set of 3 is [(16,41), (8,41)] *)
\<rparr>"
  
text {* Audio *}
definition "node_14_audio = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 16 99] 
\<rparr>"
  
text {* SDMA: Generates four interrupts. *}
definition "node_15_sdma = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [
    one_map 0 16 12, (* destination set of 0 is [(16,12),(8,18),(9,18),(10,18)] *)
    one_map 1 16 13, (* destination set of 1 is [(16,13),(8,19),(9,19),(10,19)] *)
    one_map 2 16 14, (* destination set of 2 is [(16,14),(9,20),(10,20)] *)
    one_map 3 16 15  (* destination set of 3 is [(16,15),(9,21),(10,21)] *)
  ]  
\<rparr>"
  
text {* SPI: map from datasheet space into GIC space. Adds 32 to each vector number. *}
definition "node_16_spimap = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [
  block_map (0, 987) 7 32  (* GIC accepts at most 1019-32 interrupts *)
]
\<rparr>"

text {* GPTIMER5 *}
definition "node_17_m3mmu = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [one_map 0 16 100] 
\<rparr>"

definition "sys = [
  (0,node_0_a9_0),
  (1,node_1_a9_1),
  (2,node_2_dsp),
  (3,node_3_m3_0),
  (4,node_4_m3_1),
  (5,node_5_if_a9_0),
  (6,node_6_if_a9_1),
  (7,node_7_gic),
  (8,node_8_dsp_intc),
  (9,node_9_nvic_0),
  (10,node_10_nvic_1),
  (11,node_11_pt_0),
  (12,node_12_pt_1),
  (13,node_13_gptimer5),
  (14,node_14_audio),
  (15,node_15_sdma),
  (16,node_16_spimap),
  (17,node_17_m3mmu)
]"  

end
