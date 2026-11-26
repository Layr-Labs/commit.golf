import CommitGolfCandidate.S4Compression
import CommitGolfCandidate.S4Dwords
import CommitGolfCandidate.S4Load
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
def rowStart (b : Bool) := if b then 2668 else 21
def ptrCode (reg : Reg) (p : Nat) := Instr.ADDI reg .x0 (BitVec.ofNat 12 p)
def fixedCopy (src dst n : Nat) := [ptrCode .x14 src,ptrCode .x15 dst]++checkedCopies n
def entryOps := [Sym.Calc.ld .x20 .x8 0]
def middleCopy := ptrCode .x14 512::doubleCopies .x9 .x14 96 32 8

private def sectionValid (b : Bool) (offset : Nat) (ops : List Instr) := listed .check (rowStart b+offset) ops
set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
private theorem checkPieces : ∀ b : Bool,
  sectionValid b 0 (entryOps.map Sym.Calc.instr) ∧ sectionValid b 1 (loadCode 416 24) ∧
  sectionValid b 51 (compressCode .x9 0 512 false) ∧ sectionValid b 54 middleCopy ∧
  sectionValid b 71 (compressCode .x0 512 352 false) ∧ sectionValid b 74 (compressCode .x9 160 384 false) ∧
  sectionValid b 77 [.ANDI .x6 .x20 1] ∧
  conditional .check (rowStart b+78) (rowStart b+80) .x6 .x0 true ∧
  directs .check (rowStart b+79) (rowStart b+109) ∧
  sectionValid b 80 (fixedCopy 352 512 8) ∧ sectionValid b 98 [ptrCode .x14 512,.SD .x14 .x0 64] ∧
  sectionValid b 100 (fixedCopy 416 584 3) ∧ directs .check (rowStart b+108) (rowStart b+137) ∧
  sectionValid b 109 (fixedCopy 416 512 3) ∧ sectionValid b 117 [ptrCode .x14 512,.SD .x14 .x0 24] ∧
  sectionValid b 119 (fixedCopy 352 544 8) ∧ sectionValid b 137 (compressCode .x0 512 256 false) := by decide

structure LeafSites (b : Bool) : Prop where
  idx : Matches .check (rowStart b) (entryOps.map Sym.Calc.instr)
  salt : Matches .check (rowStart b+1) (loadCode 416 24)
  first : Matches .check (rowStart b+51) (compressCode .x9 0 512 false)
  copyMid : Matches .check (rowStart b+54) middleCopy
  mid : Matches .check (rowStart b+71) (compressCode .x0 512 352 false)
  last : Matches .check (rowStart b+74) (compressCode .x9 160 384 false)
  parity : Matches .check (rowStart b+77) [.ANDI .x6 .x20 1]
  even : conditional .check (rowStart b+78) (rowStart b+80) .x6 .x0 true
  odd : directs .check (rowStart b+79) (rowStart b+109)
  evenAB : Matches .check (rowStart b+80) (fixedCopy 352 512 8)
  evenGap : Matches .check (rowStart b+98) [ptrCode .x14 512,.SD .x14 .x0 64]
  evenSalt : Matches .check (rowStart b+100) (fixedCopy 416 584 3)
  evenEnd : directs .check (rowStart b+108) (rowStart b+137)
  oddSalt : Matches .check (rowStart b+109) (fixedCopy 416 512 3)
  oddGap : Matches .check (rowStart b+117) [ptrCode .x14 512,.SD .x14 .x0 24]
  oddAB : Matches .check (rowStart b+119) (fixedCopy 352 544 8)
  final : Matches .check (rowStart b+137) (compressCode .x0 512 256 false)

theorem leafSites (b : Bool) : LeafSites b := by
  obtain ⟨i,s,a,b1,b2,c,p,e,o,ea,eg,es,skip,os,og,oa,f⟩:=checkPieces b
  exact ⟨matchesListed i,matchesListed s,matchesListed a,matchesListed b1,matchesListed b2,matchesListed c,
    matchesListed p,e,o,matchesListed ea,matchesListed eg,matchesListed es,skip,matchesListed os,matchesListed og,matchesListed oa,matchesListed f⟩
end CommitGolfCandidate.S4.Machine
