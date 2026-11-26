import CommitGolfCandidate.ReconstructedCheckLayout
import CommitGolfCandidate.ReconstructedWireBytes

namespace CommitGolfCandidate.Reconstruction.CheckRecordABI
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckLayout Binding
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxHeartbeats 1300000
abbrev W:=BitVec.ofNat 64

def position (input : CheckInput) (i : Fin input.positions.card) : {k // k∈input.positions} :=
  (input.positions.attach.sort (fun a b=>a.val≤b.val))[i.val]'(by have:=i.isLt;simpa)

def tableWord (j : Nat) : Word := W (∑ b ∈ Finset.range 8,
  ((Artifact.submission.image .check).data[8*j+b]?.getD 0).toNat * 2^(8*b))

/-- Caller data and immutable checker stack slots used across all records. -/
structure Persistent (s : MachineState) (input : CheckInput) : Prop where
  stream : StreamMemory s (Wire.unpackBytes input.proof)
  tables : CheckLayout.Tables s
  imageData : ∀ j<126,s.getMem (W (2097152+8*j))=tableWord j
  indices : ∀ i : Fin input.positions.card,s.getMem (wordAddress (CheckEntry.indexBase+i.val))=W (position input i).val.val
  values : ∀ i : Fin input.positions.card,∀ j : Fin 32,s.getMem (wordAddress (CheckEntry.valuesBase+32*i.val+j.val))=
    entryWords (input.values (position input i)) j
  commitment : ∀ j : Fin 4,s.getMem (W (4294971392+8*j.val))=input.commitment.extractLsb' (64*j.val) 64
  length : s.getMem (W (fp-2424))=W input.proof.length
  count : s.getMem (W (fp-2416))=W input.positions.card
  widths : s.getMem (W (fp-2408))=W 2097352
  valuesPtr : s.getMem (W (fp-2400))=wordAddress CheckEntry.valuesBase
  indexPtr : s.getMem (W (fp-2392))=wordAddress CheckEntry.indexBase
  marker : s.getMem (W (fp-2384))=3633
  returnPC : s.getMem (W (fp-8))=CommitBlocks.addr 20

structure Registers (s : MachineState) (ordinal cursor : Nat) : Prop where
  pc : s.pc=CommitBlocks.addr 122
  sp : s.getReg .x2=W CheckLayout.sp
  fp : s.getReg .x8=W CheckLayout.fp
  ordinal : s.getReg .x17=W ordinal
  cursor : s.getReg .x24=W cursor
  proof : s.getReg .x19=W proofBase
  beginCopy : s.getReg .x6=W (CheckLayout.fp-2328)
  endCopy : s.getReg .x7=W (CheckLayout.fp-2072)

structure Start (s : MachineState) (input : CheckInput) : Prop where
  kept : Persistent s input
  registers : Registers s 0 0
  flags : ∀ k<1024,s.getByte (W (4259840+k))=0

end CommitGolfCandidate.Reconstruction.CheckRecordABI
