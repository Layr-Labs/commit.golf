import CommitGolfCandidate.ReconstructedOpeningStraight
import CommitGolfCandidate.ReconstructedHonestScanPrefix

namespace CommitGolfCandidate.Reconstruction.CapPath
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestCuts
open HonestCapState (Path image)
open HonestCapStages (stops)
open CommitBlocks (addr)
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode Artifact.submission

abbrev Line := Nat × Instr

def listed : List Line → Prop
  | [] => True
  | (i,op)::rest => i<1660 ∧ OpeningStraight.actualAt i=some (.base op) ∧ op≠.ECALL ∧ listed rest

def final (s : MachineState) : List Line → MachineState
  | [] => s
  | (_,op)::rest => final (execInstrBr s op) rest

def follows (s : MachineState) : List Line → Nat → Prop
  | [],dst => s.pc=addr dst
  | (i,op)::rest,dst => s.pc=addr i ∧ follows (execInstrBr s op) rest dst

def clear : List Line → Prop
  | [] => True
  | (i,_)::rest => stops (addr i)=false ∧ clear rest

private theorem base_step (s t : MachineState) (op : Instr) (h : ordinaryStep s (.base op)=some t) :
    t=execInstrBr s op := by
  cases op <;> simp only [ordinaryStep,Option.ite_none_right_eq_some,Option.some.injEq] at h <;>
    first | exact h.2.symm | contradiction

private theorem first {s u : MachineState} {i : Nat} {op : Instr} {coins : Bool}
    (bounds : i<1660) (loaded : OpeningStraight.actualAt i=some (.base op)) (regular : op≠.ECALL)
    (pc : s.pc=addr i) (path : HonestCapState.Path coins s u) :
    (u=execInstrBr s op ∧ stops (execInstrBr s op).pc=true) ∨
      (HonestCapState.Path coins (execInstrBr s op) u ∧ stops (execInstrBr s op).pc=false) := by
  have outcome (r : Execution) (run : r∈support (execute image 1 s coins)) (continued : r.exit=.unfinished) :
      r.state=execInstrBr s op := by
    apply base_step
    exact HonestAbstract.continued_step _ s _ coins (OpeningStraight.fetched i _ bounds loaded s pc)
      (fun eq => regular (Instruction.base.inj eq)) r run continued
  cases path with
  | hit h ok atCut =>
    have same := outcome _ h ok
    exact Or.inl ⟨same,same ▸ atCut⟩
  | more h ok inside rest =>
    have same := outcome _ h ok
    exact Or.inr ⟨same ▸ rest,same ▸ inside⟩

theorem endpoint {s t : MachineState} {coins : Bool} {dst : Nat} {h : Line} {rest : List Line}
    (words : listed (h::rest)) (noCut : clear rest) (last : stops (addr dst)=true)
    (actual : follows s (h::rest) dst) (path : HonestCapState.Path coins s t) :
    t=final s (h::rest) := by
  induction rest generalizing s h with
  | nil =>
    rcases h with ⟨i,op⟩
    obtain ⟨pc,loc⟩ := actual
    rcases first words.1 words.2.1 words.2.2.1 pc path with hit|more
    · exact hit.1
    · have endPC : stops (execInstrBr s op).pc=true := loc ▸ last
      exact False.elim (by simpa using endPC.symm.trans more.2)
  | cons u us ih =>
    rcases h with ⟨i,op⟩
    rcases u with ⟨k,nextOp⟩
    rcases actual with ⟨pc,more⟩
    have safe : stops (execInstrBr s op).pc=false := more.1 ▸ noCut.1
    rcases first words.1 words.2.1 words.2.2.1 pc path with hit|step
    · exact False.elim (by simpa using safe.symm.trans hit.2)
    · exact ih words.2.2.2 noCut.2 more step.1

theorem final_append (s : MachineState) (a b : List Line) : final s (a++b)=final (final s a) b := by
  induction a generalizing s with
  | nil => rfl
  | cons h tail ih => exact ih _

end CommitGolfCandidate.Reconstruction.CapPath
