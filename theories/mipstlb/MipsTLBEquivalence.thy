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
theory MipsTLBEquivalence
  imports Main Set MipsTLB MipsTLBPageTable MipsTLBReplacementHandler MipsTLBLarge
begin
(*>*)
    
  
(* ========================================================================= *)  
section "Equivalence to Large TLB"
(* ========================================================================= *)  

text "Next we show that for all " 

    
  
lemma 
    assumes inrange: "vpn < MIPSPT_EntriesMax"
        and inrange2: "as < ASIDMax"
        and cap: "capacity (tlb mpt) > 0"
        and valid: "MipsTLBPT_valid mpt"
  shows "MipsTLBPT_translate mpt as vpn = 
         MIPSTLB_translate (MipsTLBLarge_create (pte mpt)) as vpn"
proof -
  from valid have ptvalid: "MIPSPT_valid (pte mpt)"
    by(simp add:MipsTLBPT_valid_def)
  
  from ptvalid inrange inrange2 have X0:
    " MIPSTLB_translate (MipsTLBLarge_create (pte mpt)) as vpn =  
     (if (v ((entry (pte mpt)) vpn as)) then {(pfn ((entry (pte mpt)) vpn as))} else {})"
    by(simp add:MipsTLBLarge_translate_is)
    
  from valid inrange inrange2 cap have X1:
    "MipsTLBPT_translate mpt as vpn =  (if (v ((entry (pte mpt)) vpn as)) then {(pfn ((entry  (pte mpt)) vpn as))} else {})"
    by(simp add:MipsTLBPT_translate_is)
  
  from X0 X1 show ?thesis by(auto)
qed
  
  
end  
