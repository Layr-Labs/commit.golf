import CommitGolfCandidate.GroupedManifest
import CommitGolfCandidate.TwoPermutationManifest

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
attribute [local irreducible] ArtifactEncoding.decode

def image : Image := ⟨ArtifactEncoding.decode 32 GroupedArtifact.commitCode, ArtifactEncoding.decode 8 GroupedArtifact.commitData⟩
theorem exact_image : image = GroupedArtifact.submission.image .commit := rfl
def codeWord (index : Nat) : BitVec 32 :=
  if inside : index<201767 then GroupedArtifact.commitCode.get 32 ⟨index,inside⟩ else 0
def wordPC (index : Nat) : Word := BitVec.ofNat 64 (4096 + 4*index)

theorem fetch_decoded (state : MachineState) (index : Nat)
    (inCode : index < 201767) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (instruction : Instr)
    (decoded : Manifest.decodeBase (codeWord index)=some instruction) :
    fetch image state=some (.base instruction) := by
  have address : state.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have code : image.code=ArtifactEncoding.decode 32 GroupedArtifact.commitCode := by
    simp only [image]
  have length : index< image.code.length := by
    rw [code,ArtifactEncoding.length_decode]
    exact inCode
  have atIndex : image.code[index]?=some (GroupedArtifact.commitCode.get 32 ⟨index,inCode⟩) := by
    rw [List.getElem?_eq_getElem length,←List.getD_eq_getElem _ _ length,code,
      ArtifactEncoding.getD_decode _ _ _ inCode]
  rw [fetch,address,ite_eq_left (by omega),show (4096+4*index-4096)/4=index by omega,atIndex]
  have base : Manifest.decodeBase (GroupedArtifact.commitCode.get 32 ⟨index,inCode⟩)=some instruction := by
    simpa only [codeWord,dite_eq_left inCode] using decoded
  unfold Manifest.decodeBase at base
  cases result : decodeInstruction (GroupedArtifact.commitCode.get 32 ⟨index,inCode⟩) with
  | none => simp [result] at base
  | some ins => cases ins <;> simp_all



/-- Number of heads among the first n slots of a 64-leaf period. -/
def heads (n : Nat) := 187*(n/2048)+((n%2048+10)/11)
def rank (n : Nat) := (n%2048)%11
def pairPos (n : Nat) := (n%2048)%22
def pairHeads (n : Nat) := 94*(n/2048)+(n%2048+21)/22
def firstWord (n : Nat) := 21+11*n+pairHeads n+n/32
def heapImm (n : Nat) := BitVec.ofNat 12 (2048+512*((n/4)%8)+72+32*(n%4))
def sourceImm (n : Nat) := BitVec.ofNat 12 (2560+2816*((n%2048/11)%2)+16*(rank n-1))

def packet (n : Nat) : List Instr :=
  [.ADDI .x12 .x10 (-32),.ECALL] ++
  (if rank n=0 then
    [.SD .x24 .x10 0,.ADDI .x12 .x10 (-120),.ADDI .x10 .x24 0,.ECALL] ++ (if pairPos n=0 then [.ADDI .x7 .x12 1536] else []) ++
     [.ADDI .x10 .x12 176,.SD .x10 .x10 0]
  else [.ADDI .x10 .x10 56,.SD .x10 .x10 0,.LD .x31 .x7 (sourceImm n),
    .SD .x10 .x31 8,.LD .x31 .x7 (sourceImm n+8),.SD .x10 .x31 16]) ++
  [.ADDI .x12 .x20 (heapImm n),.ECALL,.ADDI .x10 .x10 200] ++
  (if n%32=31 then [.ADD .x20 .x20 .x23] else [])

end TwoPermutationPrototype.Grouped
