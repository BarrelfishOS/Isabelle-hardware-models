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


theory IntroductionPC
  imports "../model/Syntax"
begin
                     
definition "loram = blockn 0x000001000 0x007fffffff"  (* 2G-4k *)
definition "lapic = blockn 0x0fee00000 0x00fee0ffff"  (* 64k *)
definition "mmio =  blockn 0x0fff00000 0x0fff00ffff" (* 64k *)
definition "hiram = blockn 0x100000000 0x027fffffff"  (* 6G *)
                       
text {* Node 0, the interconnect. *}
definition "interconnect = empty_spec \<lparr>
  acc_blocks := [loram, hiram],
  map_blocks := [direct_map mmio 1]
\<rparr>"

text {* Node 1, the NIC. *}
definition "nic = empty_spec \<lparr>
  acc_blocks := [mmio],
  overlay := Some 0
\<rparr>"
  
text {* Nodes 2 and 3, the CPUs. *}
definition "cpu = empty_spec \<lparr>
  acc_blocks := [lapic],
  overlay := Some 0
\<rparr>"

text {* Virtual Address Spaces *}

definition "vas_loram = blockn 0x000001000 0x07fffffff"
definition "vas_hiram = blockn 0x080000000 0x2ffffffff"
definition "vas_mmio =  blockn 0xfb00000000 0xfb0000ffff"
definition "vas_lapic = blockn 0x1b10000000 0x1b1000ffff"
  
definition "cpu0_virt = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [block_map vas_loram 0 0x000001000, 
                 block_map vas_hiram 0 0x100000000,
                 block_map vas_lapic 0 0x0fee00000,
                 block_map vas_mmio 0 0x0fff00000]
\<rparr>"
  
definition "cpu1_virt = empty_spec \<lparr>
  acc_blocks := [],
  map_blocks := [block_map vas_loram 0 0x000001000, 
                 block_map vas_lapic 0 0x0fee00000]
\<rparr>"
  
definition "sys = [(0, interconnect), (1, nic), (2, cpu), (3, cpu), 
                   (4, cpu0_virt), (5, cpu1_virt)]"

end