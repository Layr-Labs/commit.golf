import CommitGolf.Artifact
import CommitGolfCandidate.Stage3cDomains
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

set_option maxRecDepth 12000

def checkerWord (n : Fin 2147) := Artifact.checkCode.get 32 n

private theorem lookup {count : Nat} (a : ArtifactEncoding.Packed count) (n : Fin count) :
    (ArtifactEncoding.decode 32 a)[n.val]?=some (a.get 32 n) := by
  simp only [ArtifactEncoding.decode,List.getElem?_ofFn,dif_pos n.isLt]

theorem delivered (n : Fin 2147) :
    (Artifact.submission.image .check).code[n.val]?=some (checkerWord n) :=
  lookup Artifact.checkCode n

theorem firstTagSites :
    decodeInstruction (checkerWord 192)=some (.base (.ADDI .x6 .x0 1)) ∧
    decodeInstruction (checkerWord 193)=some (.base (.SLLI .x6 .x6 63)) ∧
    decodeInstruction (checkerWord 194)=some (.base (.SLLI .x7 .x29 8)) ∧
    decodeInstruction (checkerWord 195)=some (.base (.OR .x7 .x6 .x7)) ∧
    decodeInstruction (checkerWord 196)=some (.base (.SD .x10 .x7 64)) ∧
    decodeInstruction (checkerWord 198)=some (.base .ECALL) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem nextTagSites :
    decodeInstruction (checkerWord 201)=some (.base (.ADD .x12 .x7 .x6)) ∧
    decodeInstruction (checkerWord 202)=some (.base (.SD .x26 .x12 64)) ∧
    decodeInstruction (checkerWord 207)=some (.base .ECALL) := ⟨rfl,rfl,rfl⟩

/-- Store the all-zero word in the third 32-byte block, starting at byte 64. -/
def clearWord (i : Fin 4) : BitVec 32 :=
  BitVec.ofNat 32 (((64+8*i.val)/32)*2^25+25*2^15+3*2^12+((64+8*i.val)%32)*2^7+35)

theorem ordinary_gap_clear_sites : ∀ (d : Fin 24) (i : Fin 4),
    checkerWord ⟨1126+42*d.val+i.val,by have :=d.isLt;have :=i.isLt;omega⟩=clearWord i := by decide +kernel

theorem batch_gap_clear_sites : ∀ (d : Fin 15) (i : Fin 4),
    checkerWord ⟨246+35*d.val+i.val,by have :=d.isLt;have :=i.isLt;omega⟩=clearWord i := by decide +kernel

theorem pair_gap_clear_sites : ∀ i : Fin 4,
    checkerWord ⟨854+i.val,by have :=i.isLt;omega⟩=clearWord i := by decide +kernel

theorem clear_decodes (i : Fin 4) :
    decodeInstruction (clearWord i)=some (.base (.SD .x25 .x0 (BitVec.ofNat 12 (64+8*i.val)))) := by
  fin_cases i <;> rfl

def tagWord (h : Height) (j : Fin 16) : Word :=
  ((1 : Word) <<< 63 ||| (BitVec.ofNat 64 (h.val+1) <<< 8))+BitVec.ofNat 64 j.val

theorem tagFields : ∀ (h : Height) (j : Fin 16),
    (tagWord h j).toNat=2^63+256*(h.val+1)+j.val ∧ (tagWord h j).getLsbD 63=true := by
  decide +kernel

theorem tagMatchesFirst (h : Height) (tagged : h.val≠0) : (tagWord h 0).toNat=firstTag h := by
  exact ((tagFields h 0).1).trans (by simp [firstTag,tagged])
theorem tagMatchesNext (h : Height) (j : Fin 15) :
    (tagWord h ⟨j.val+1,by omega⟩).toNat=nextTag h j := by
  exact (tagFields h ⟨j.val+1,by omega⟩).1
end CommitGolfCandidate.Chained.BinaryMachine
