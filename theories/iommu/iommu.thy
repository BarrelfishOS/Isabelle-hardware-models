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

(* ######################################################################### *) 
chapter "The Intel VT-d Model (IOMMU)"
(* ######################################################################### *)


(*<*)
theory iommu
  imports Main Set "../model/Model" "../model/Syntax" Parity Nat 
          "HOL-Word.Word" "HOL-Word.WordBitwise"

begin
(*>*)  


(* ------------------------------------------------------------------------- *)
section "IO Addresses"
(* ------------------------------------------------------------------------- *)

text "There are two types of requests that can occur. 1) request w/o PASID and
      request with PASID"

record pciaddr = 
  bus :: "8 word"    (* 8 bits *)
  dev :: "5 word"    (* 5 bits *)
  fn  :: "3 word"    (* 3 bits *)



record ioaddr = 
  src :: pciaddr
  va  :: addr
  (* adding some things here
 Requests with address-space-identifier: These are memory requests with additional information
identifying the targeted process address space from endpoint devices supporting virtual memory
capabilities. Beyond attributes in normal requests, these requests specify the targeted process
address space identifier (PASID), and extended attributes such as Execute-Requested (ER) flag
(to indicate reads that are instruction fetches), and Privileged-mode-Requested (PR) flag (to
distinguish user versus supervisor access). For details, refer to the Process Address Space ID
(PASID) Capability in the PCI-Express specifications.
 *)

(* ------------------------------------------------------------------------- *)
section "Domain Assignment: The Root Table"
(* ------------------------------------------------------------------------- *)

text "Assignment of devices to domains. The root table is a 256 entry table
      of total 4kB residing in memory. There are two versions of the 
      root table and context entries: normal and extended."

(* ------------------------------------------------------------------------- *)
subsection "Context Entries and Root Table"
(* ------------------------------------------------------------------------- *)

record ContextEntry = 
  present :: bool
  addresswidth :: nat
  addresstype :: nat
  ptpointer :: nat
  domainid :: nat
  faultdisable :: bool

record RootTableEntry = 
  present :: bool  
  ctxtptr :: nat
  



(* ------------------------------------------------------------------------- *)
subsection "Extended Context Entries Root Table"
(* ------------------------------------------------------------------------- *)

record RootTableEntryExtended = 
  lowerpresent :: bool
  lowerctxtptr :: nat
  upperpresent :: bool
  upperctxtptr :: nat


(* ------------------------------------------------------------------------- *)
section "IOMMU"
(* ------------------------------------------------------------------------- *)

record iommu = 
  roottable :: nat

(*<*)
end
(*>*)  