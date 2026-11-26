import CommitGolfCandidate.LateArtifact
import CommitGolfCandidate.LateCalls

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def image := Late.submission.image .opening
def openWord (n : Nat) : BitVec 32 := if h : n<406 then Artifact.openingCode.get 32 ⟨n,h⟩ else 0

private theorem packed_lookup {m : Nat} (a : ArtifactEncoding.Packed m) (j : Nat) (h : j<m) :
    (ArtifactEncoding.decode 32 a)[j]? = some (a.get 32 ⟨j,h⟩) := by
  simp only [ArtifactEncoding.decode,List.getElem?_ofFn,dif_pos h]

attribute [local irreducible] ArtifactEncoding.decode

theorem fetched (n : Nat) (hi : n<406) (op : Instr) (encoded : decodeInstruction (openWord n)=some (.base op))
    (s : MachineState) (pc : s.pc=pcAt n) : fetch image s=some (.base op) := by
  have atWord : image.code[n]?=some (openWord n) := by
    rw [openWord,dif_pos hi]
    exact packed_lookup Artifact.openingCode n hi
  simp only [fetch,pc,pcAt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 4096+4*n<2^64 by omega)]
  rw [if_pos (by constructor <;> omega)]
  simp only [Nat.add_sub_cancel_left,Nat.mul_div_cancel_left _ (by decide : 0<4),atWord,encoded]

/-- A deterministic fragment can be followed by any amount of remaining fuel. -/
def Runs (s t : MachineState) (steps cycles : Nat) : Prop := ∀ fuel,
  execute image (fuel+steps) s true = (do let r ← execute image fuel t true; pure (r.charge cycles 0))

theorem Runs.trans {s t u : MachineState} {a b c d : Nat} (left : Runs s t a c) (right : Runs t u b d) :
    Runs s u (a+b) (c+d) := by
  intro fuel
  rw [show fuel+(a+b)=fuel+b+a by omega,left,right]
  simp [bind_assoc,Execution.charge,Nat.add_assoc]

theorem Runs.refl (s : MachineState) : Runs s s 0 0 := by intro fuel; simp [Execution.charge]

theorem one (n : Nat) (hi : n<406) (op : Instr) (encoded : decodeInstruction (openWord n)=some (.base op))
    (s t : MachineState) (pc : s.pc=pcAt n) (step : ordinaryStep s (.base op)=some t) :
    Runs s t 1 (instructionCycles (.base op)) :=
  fun f => execute_ordinary_step _ _ _ _ f _ (fetched _ hi _ encoded _ pc) step

def permitted : Instr → Bool
  | .ADDI .. | .SLLI .. | .SRLI .. | .ANDI .. | .XORI .. | .ADD .. | .LD .. | .SD .. => true
  | _ => false

private theorem regular (s : MachineState) (op : Instr) (p : permitted op) :
    (execInstrBr s op).pc=s.pc+4 ∧ instructionCycles (.base op)=1 ∧
    (memoryArgumentsValid s op → ordinaryStep s (.base op)=some (execInstrBr s op)) := by
  cases op <;> simp [permitted] at p
  all_goals exact ⟨rfl,rfl,fun ok => by simp only [ordinaryStep,ok,↓reduceIte]⟩

def before (ops : List Instr) (s : MachineState) (i : Nat) := (ops.take i).foldl execInstrBr s

theorem block (ops : List Instr) (n : Nat) (s : MachineState) (pc : s.pc=pcAt n)
    (enc : ∀ j : Fin ops.length, decodeInstruction (openWord (n+j.val))=some (.base ops[j.val]))
    (within : n+ops.length≤406) (valid : ∀ j : Fin ops.length, permitted ops[j.val])
    (safe : ∀ j : Fin ops.length, memoryArgumentsValid (before ops s j.val) ops[j.val]) :
    Runs s (ops.foldl execInstrBr s) ops.length ops.length := by
  intro fuel
  have next (i : Nat) (h : i<ops.length) :
      before ops s (i+1)=execInstrBr (before ops s i) ops[i] := by
    unfold before; rw [List.take_succ_eq_append_getElem h,List.foldl_append];rfl
  have pcs (i : Nat) (hi : i≤ops.length) : (before ops s i).pc=pcAt (n+i) := by
    induction i with
    | zero => simpa [before] using pc
    | succ i ih => rw [next _ (by omega),(regular _ _ (valid ⟨i,by omega⟩)).1,ih (by omega),
        show n+(i+1)=(n+i)+1 by omega,pc_succ]
  have run := execute_unit_steps image ops.length fuel (before ops s) true (by
    intro j hj
    have reg := regular (before ops s j) ops[j] (valid ⟨j,hj⟩)
    refine ⟨.base ops[j],fetched _ (by omega) _ (enc ⟨j,hj⟩) _ (pcs j (by omega)),?_,reg.2.1⟩
    rw [next j hj]; exact reg.2.2 (safe ⟨j,hj⟩))
  simpa only [before,List.take_zero,List.foldl_nil,List.take_length,Nat.add_comm ops.length fuel] using run

end CommitGolfCandidate.Late.Open
