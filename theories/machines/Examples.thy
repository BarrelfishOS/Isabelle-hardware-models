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


theory Examples
  imports "../model/Syntax"
begin

definition "loram = blockn 0x000001000 0x01fffffff"
definition "lapic = blockn 0xb00000000 0x0b000ffff"
definition "mmio =  blockn 0xb00001000 0x0b0001fff"
definition "hiram = blockn 0x100000000 0x1ffffffff"

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
  
definition "sys = [(0, interconnect), (1, nic), (2, cpu), (3, cpu)]"
    
end