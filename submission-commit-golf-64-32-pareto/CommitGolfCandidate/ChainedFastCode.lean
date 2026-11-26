import CommitGolfCandidate.ChainedFastLayout
namespace CommitGolfCandidate.Chained.Native.Fast
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
def codeWord (i : Nat) : BitVec 32 := if h:i<233483 then Artifact.commitCode.get 32 ⟨i,h⟩ else 0
def baseOp (w : BitVec 32) : Option Instr := match decodeInstruction w with
  | some (.base op)=>some op | _=>none

def ArrayAt (base : Nat) (ops : List Instr) := ∀ i : Fin ops.length,
  baseOp (codeWord (base+i.val)) = some ops[i]
instance (b : Nat) (ops : List Instr) : Decidable (ArrayAt b ops) := by unfold ArrayAt;infer_instance

theorem fetchAt {base : Nat} {ops : List Instr} (table : ArrayAt base ops)
    (room : base+ops.length≤233483) (i : Fin ops.length) (s : MachineState) (here : s.pc=pc (base+i.val)) :
    fetch chainedCommitImage s=some (.base ops[i]) := by
  have inCode : base+i.val<233483 := by have:=i.isLt;omega
  have dec:=table i
  simp only [codeWord,inCode,dif_pos] at dec
  have n:s.pc.toNat=4096+4*(base+i.val) := by rw [here,pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have bound : base+i.val<chainedCommitImage.code.length := by rw [chained_commit_code,ArtifactEncoding.length_decode];exact inCode
  have entry:chainedCommitImage.code[base+i.val]?=some (Artifact.commitCode.get 32 ⟨base+i.val,inCode⟩) := by
    rw [List.getElem?_eq_getElem bound,←List.getD_eq_getElem _ _ bound,chained_commit_code,ArtifactEncoding.getD_decode _ _ _ inCode]
  rw [fetch,n,ite_eq_left (by omega),show (4096+4*(base+i.val)-4096)/4=base+i.val by omega,entry]
  cases val : decodeInstruction (Artifact.commitCode.get 32 ⟨base+i.val,inCode⟩) with
  | none => simp [baseOp,val] at dec
  | some op => cases op <;> simp_all [baseOp]

theorem init_code : ArrayAt 45688 setup := by decide +kernel
theorem headers : ∀ h : Low, ArrayAt (levelStart h) (header h) := by decide +kernel
theorem tails : ∀ h : Low, ArrayAt (tailStart h) (groupTail h) := by decide +kernel
theorem end_code : ArrayAt 51098 handoff := by decide +kernel

private theorem nodes0 : ∀ k : Lane, ArrayAt (nodeStart 0 k) (node 0 k) := by decide +kernel
private theorem nodes1 : ∀ k : Lane, ArrayAt (nodeStart 1 k) (node 1 k) := by decide +kernel
private theorem nodes2 : ∀ k : Lane, ArrayAt (nodeStart 2 k) (node 2 k) := by decide +kernel
private theorem nodes3 : ∀ k : Lane, ArrayAt (nodeStart 3 k) (node 3 k) := by decide +kernel
private theorem nodes4 : ∀ k : Lane, ArrayAt (nodeStart 4 k) (node 4 k) := by decide +kernel
private theorem nodes5 : ∀ k : Lane, ArrayAt (nodeStart 5 k) (node 5 k) := by decide +kernel
private theorem nodes6 : ∀ k : Lane, ArrayAt (nodeStart 6 k) (node 6 k) := by decide +kernel
private theorem nodes7 : ∀ k : Lane, ArrayAt (nodeStart 7 k) (node 7 k) := by decide +kernel
theorem nodes (h : Low) (k : Lane) : ArrayAt (nodeStart h k) (node h k) := by
  fin_cases h
  · exact nodes0 k
  · exact nodes1 k
  · exact nodes2 k
  · exact nodes3 k
  · exact nodes4 k
  · exact nodes5 k
  · exact nodes6 k
  · exact nodes7 k

end CommitGolfCandidate.Chained.Native.Fast
