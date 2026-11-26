import CommitGolfCandidate.TruncWireImage
import CommitGolfCandidate.LateArtifact
import CommitGolfCandidate.LateCalls
import CommitGolfCandidate.LateNormalEval

namespace CommitGolfCandidate.Late.Check3.Micro
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def image := Trunc.submission.image .check
def checkWord (n : Nat) : BitVec 32 := if h : n<433 then Artifact.checkCode.get 32 ⟨n,by omega⟩ else 0

private theorem packed_lookup {m : Nat} (a : ArtifactEncoding.Packed m) (j : Nat) (h : j<m) :
    (ArtifactEncoding.decode 32 a)[j]? = some (a.get 32 ⟨j,h⟩) := by
  simp only [ArtifactEncoding.decode,List.getElem?_ofFn,dif_pos h]

attribute [local irreducible] ArtifactEncoding.decode

theorem fetched (n : Nat) (hi : n<433) (op : Instr) (encoded : decodeInstruction (checkWord n)=some (.base op))
    (s : MachineState) (pc : s.pc=pcAt n) : fetch image s=some (.base op) := by
  have atWord : image.code[n]?=some (checkWord n) := by
    rw [checkWord,dif_pos hi]
    exact packed_lookup Artifact.checkCode n (by omega)
  simp only [fetch,pc,pcAt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 4096+4*n<2^64 by omega)]
  rw [if_pos (by constructor <;> omega)]
  simp only [Nat.add_sub_cancel_left,Nat.mul_div_cancel_left _ (by decide : 0<4),atWord,encoded]

/-- A deterministic fragment can be followed by any amount of remaining fuel. -/
def Runs (s t : MachineState) (steps cycles : Nat) : Prop := ∀ fuel,
  execute image (fuel+steps) s false = (do let r ← execute image fuel t false; pure (r.charge cycles 0))

theorem Runs.trans {s t u : MachineState} {a b c d : Nat} (left : Runs s t a c) (right : Runs t u b d) :
    Runs s u (a+b) (c+d) := by
  intro fuel
  rw [show fuel+(a+b)=fuel+b+a by omega,left,right]
  simp [bind_assoc,Execution.charge,Nat.add_assoc]

theorem Runs.refl (s : MachineState) : Runs s s 0 0 := by intro fuel; simp [Execution.charge]

theorem one (n : Nat) (hi : n<433) (op : Instr) (encoded : decodeInstruction (checkWord n)=some (.base op))
    (s t : MachineState) (pc : s.pc=pcAt n) (step : ordinaryStep s (.base op)=some t) :
    Runs s t 1 (instructionCycles (.base op)) :=
  fun f => execute_ordinary_step _ _ _ _ f _ (fetched _ hi _ encoded _ pc) step

end CommitGolfCandidate.Late.Check3.Micro
