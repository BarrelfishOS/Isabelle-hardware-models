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

datatype AGAW = AGAW39 | AGAW48 | AGAW57 | AGAW0

primrec addrbits :: "AGAW \<Rightarrow> nat" where
  "addrbits(AGAW39)  = 39"  | 
  "addrbits(AGAW48)  = 48"  |
  "addrbits(AGAW57)  = 57"  |
  "addrbits(AGAW0)   = 0"

(*

• 00b: Untranslated requests are translated using second-level
paging structures referenced through SLPTPTR field. Translated
requests and Translation Requests are blocked.
• 01b: Untranslated, Translated and Translation Requests are
supported. This encoding is treated as reserved by hardware
implementations not supporting Device-TLBs (DT=0 in Extended
Capability Register).
• 10b: Untranslated requests are processed as pass-through.
SLPTPTR field is ignored by hardware. Translated and Translation
Requests are blocked. This encoding is treated by hardware as
reserved for hardware implementations not supporting Pass
Through (PT=0 in Extended Capability Register).

 *)
datatype TTYPE = T_ONLY_TRANSLATE | T_ALLOW_ALL | T_ONLY_PASSTHROUGH

record ContextEntry = 
  present      :: bool
  faultdisable :: bool
  ttype        :: TTYPE
  slptptr      :: nat
  addrwidth    :: AGAW
  domid        :: nat



record RootTableEntry = 
  (* This field indicates whether the root-entry is present. *)
  present :: bool
 (* Pointer to Context-table for this bus. The Context-table is 
    4KB in size and size-aligned. *)
  ctp :: "nat \<Rightarrow> ContextEntry"
  
record RootTable = 
   entries :: "nat \<Rightarrow> RootTableEntry"


(* ------------------------------------------------------------------------- *)
subsection "Extended Context Entries Root Table"
(* ------------------------------------------------------------------------- *)

datatype PageAttribute = 
  PAT_UC | (* Uncacheable *)
  PAT_WC | (* Write_Combining *)
  PAT_WT | (* Write Through *)
  PAT_WP | (* Write Protected *)
  PAT_WB | (* Write Back *)
  PAT_UC2 (* Uncached *)

datatype EMT = 
  EMT_UC |
  EMT_WB 

datatype TTYPEE = TE_HOST_DTLB_DISABLE | 
                  TE_HOST_DTLB_ENABLE | 
                  TE_HOST_PASSTHROUGH |
                  TE_GUEST_DTLB_DISABLE |
                  TE_GUEST_DTLB_ENABLE 
                 

record ContextEntryExtended = 
  pasidstptr :: nat
  pasidptr :: nat
  pts :: nat 
  pat :: PageAttribute (* TODO: x8 *)
  slee :: bool
  ere :: bool
  eafe :: bool
  smep :: bool
  domid :: nat
  emte :: bool
  cd :: bool
  wpe :: bool
  nxe :: bool
  pge :: bool
  addwidth :: AGAW
  slptptr :: nat
  paside :: bool
  neste :: bool
  pre :: bool
  dinve :: bool
  emt :: EMT
  ttypee :: TTYPEE
  faultdisable :: bool
  present :: bool

definition NULL_ContexEntryExtended :: ContextEntryExtended
  where "NULL_ContexEntryExtended = \<lparr> 
    pasidstptr = 0,
    pasidptr = 0,
    pts  = 0,
    pat = PAT_UC, (* TODO: x8 *)
    slee = False,
    ere = False,
    eafe = False,
    smep = False,
    domid = 0,
    emte = False,
    cd = False,
    wpe = False,
    nxe = False,
    pge = False,
    addwidth = AGAW0,
    slptptr  = 0,
    paside = False,
    neste = False,
    pre = False,
    dinve = False,
    emt = EMT_UC,
    ttypee = TE_HOST_DTLB_DISABLE,
    faultdisable = False,
    present = False
\<rparr>"

record RootTableEntryExtended = 
  upresent :: bool
  uctp :: "nat \<Rightarrow> ContextEntryExtended"
  lpresent :: bool
  lctp :: "nat \<Rightarrow> ContextEntryExtended"

record RootTableExtended = 
  entries :: "nat \<Rightarrow> RootTableEntryExtended"

(* ------------------------------------------------------------------------- *)
subsection "Equivalence of Entries and their Extended Version"
(* ------------------------------------------------------------------------- *)

definition context_to_extended :: "ContextEntry \<Rightarrow> ContextEntryExtended "
  where "context_to_extended c = NULL_ContexEntryExtended"

definition convert_to_extended :: "RootTableEntry \<Rightarrow> RootTableEntryExtended"
  where "convert_to_extended = \<lparr> upresent = 0, uctp = 0, 
                                 lpresent = 0, lctp = 0  \<rparr>"



(* ------------------------------------------------------------------------- *)
section "IOMMU"
(* ------------------------------------------------------------------------- *)

record iommu = 
  roottable :: nat

(*<*)
end
(*>*)  