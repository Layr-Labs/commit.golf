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



/-- Number of heads among the first n slots of a 64-leaf period. -/
def heads (n : Nat) := 6*(n/64)+((n%64+10)/11)
def rank (n : Nat) := (n%64)%11
def firstWord (n : Nat) := 21+11*n+heads n+n/128
def heapImm (n : Nat) := BitVec.ofNat 12 (2048+32*(n%128))
def sourceImm (n : Nat) := BitVec.ofNat 12 (16*(rank n-1))

/-- One leaf of the binary grouped body (P4): the head of a group (rank 0) stores the counter, queries the
permutation on counter‖key with the reply landing so that its last 16 bytes are the head's own salt slot, and
leaves the reply cursor in x22; the other leaves copy their 16-byte slice from x22. The centered heap pointer
x20 is rebased by the 4,096-byte stride x7 after every 128 leaves. -/
def packet (n : Nat) : List Instr :=
  [.ADDI .x12 .x10 (-32),.ECALL] ++
  (if rank n=0 then
    [.SD .x24 .x10 0,.ADDI .x12 .x10 (-120),.ADDI .x10 .x24 0,.ECALL,
     .ADDI .x22 .x12 0,.ADDI .x10 .x12 176,.SD .x10 .x10 0]
  else [.ADDI .x10 .x10 56,.SD .x10 .x10 0,.LD .x31 .x22 (sourceImm n),
    .SD .x10 .x31 8,.LD .x31 .x22 (sourceImm n+8),.SD .x10 .x31 16]) ++
  [.ADDI .x12 .x20 (heapImm n),.ECALL,.ADDI .x10 .x10 200] ++
  (if n%128=127 then [.ADD .x20 .x20 .x7] else [])

end TwoPermutationPrototype.Grouped
