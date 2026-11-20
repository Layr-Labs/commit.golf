import CommitGolf.Artifact
import CommitGolfCandidate.TwoPermutationManifest

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
attribute [local irreducible] ArtifactEncoding.decode

def image : Image := ⟨ArtifactEncoding.decode 32 Artifact.commitCode, ArtifactEncoding.decode 8 Artifact.commitData⟩
theorem exact_image : image = Artifact.submission.image .commit := rfl
def codeWord (index : Nat) : BitVec 32 :=
  if inside : index<233357 then Artifact.commitCode.get 32 ⟨index,inside⟩ else 0
def wordPC (index : Nat) : Word := BitVec.ofNat 64 (4096 + 4*index)

theorem fetch_decoded (state : MachineState) (index : Nat)
    (inCode : index < 233357) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (instruction : Instr)
    (decoded : Manifest.decodeBase (codeWord index)=some instruction) :
    fetch image state=some (.base instruction) := by
  have address : state.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have code : image.code=ArtifactEncoding.decode 32 Artifact.commitCode := by
    simp only [image]
  have length : index< image.code.length := by
    rw [code,ArtifactEncoding.length_decode]
    exact inCode
  have atIndex : image.code[index]?=some (Artifact.commitCode.get 32 ⟨index,inCode⟩) := by
    rw [List.getElem?_eq_getElem length,←List.getD_eq_getElem _ _ length,code,
      ArtifactEncoding.getD_decode _ _ _ inCode]
  rw [fetch,address,ite_eq_left (by omega),show (4096+4*index-4096)/4=index by omega,atIndex]
  have base : Manifest.decodeBase (Artifact.commitCode.get 32 ⟨index,inCode⟩)=some instruction := by
    simpa only [codeWord,dite_eq_left inCode] using decoded
  unfold Manifest.decodeBase at base
  cases result : decodeInstruction (Artifact.commitCode.get 32 ⟨index,inCode⟩) with
  | none => simp [result] at base
  | some ins => cases ins <;> simp_all



/-- Number of heads among the first n slots of a 4,096-leaf period. -/
def heads (n : Nat) := 373*(n/4096)+((n%4096+10)/11)
def rank (n : Nat) := (n%4096)%11
/-- The register cache represents loads charged earlier in this group. -/
def cacheCredit (n : Nat) : Nat :=
  if n%4096≥4092 ∨ rank n=0 then 0 else if rank n≤9 then 4 else 2

def bodyLen (n : Nat) : Nat :=
  if rank n=0 then (if n%4096=4092 then 11 else 15) else if rank n≤8 then 11 else 9

/-- Byte offset of leaf slot n inside the 32-byte binary leaf slots of one body. -/
def slotOff (n : Nat) := 32*n
/-- Number of heap-pointer rebases (4,096-byte windows, i.e. 128 leaves) before leaf slot n of a body. -/
def rb (n : Nat) := slotOff n/4096
/-- Leaf slot n is followed by a rebase of the centered heap pointer. -/
def rebase (n : Nat) : Prop := rb (n+1) ≠ rb n
instance (n : Nat) : Decidable (rebase n) := inferInstanceAs (Decidable (_ ≠ _))
def firstWord (n : Nat) := 21+11*n+cacheCredit n+rb n
def heapImm (n : Nat) := BitVec.ofNat 12 (2048+slotOff n-4096*rb n)
def sourceImm (n : Nat) := BitVec.ofNat 12 (3992-240*rank n)

/-- One leaf of the binary grouped body (P4): the head of a group (rank 0) stores the counter, queries the
permutation on counter‖key with the reply landing so that its last 16 bytes are the head's own salt slot, and
the next eight leaves copy their 16-byte slices relative to x12 and the last two from x14..x17 (prefetched). The centered heap pointer
x20 is rebased by the 4,096-byte stride x7 after every 128 leaves. -/
def packet (n : Nat) : List Instr :=
  [.ADDI .x12 .x10 (-32),.ECALL] ++
  (if rank n=0 then
    [.SD .x24 .x10 0,.ADDI .x12 .x10 (-120),.ADDI .x10 .x24 0,.ECALL] ++
    (if n%4096=4092 then [] else
       [.LD .x14 .x12 128,.LD .x15 .x12 136,.LD .x16 .x12 144,.LD .x17 .x12 152]) ++
     [.ADDI .x10 .x12 176,.SD .x10 .x10 0]
   else [.ADDI .x10 .x10 56,.SD .x10 .x10 0] ++
     (if rank n≤8 then [.LD .x31 .x12 (sourceImm n),.SD .x10 .x31 8,
                         .LD .x31 .x12 (sourceImm n+8),.SD .x10 .x31 16]
      else if rank n=9 then [.SD .x10 .x14 8,.SD .x10 .x15 16]
      else [.SD .x10 .x16 8,.SD .x10 .x17 16])) ++
  [.ADDI .x12 .x20 (heapImm n),.ECALL,.ADDI .x10 .x10 200] ++
  (if rebase n then [.ADD .x20 .x20 .x7] else [])

end TwoPermutationPrototype.Grouped
