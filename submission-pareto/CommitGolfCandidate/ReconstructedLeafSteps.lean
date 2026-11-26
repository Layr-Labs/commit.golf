import CommitGolfCandidate.ReconstructedCommitExact
import CommitGolfCandidate.ReconstructedLeafCode

namespace CommitGolfCandidate.Reconstruction.LeafSteps
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitBlocks CommitSetup CommitExact TwoPermutationPrototype.RV64
open TwoPermutationPrototype (window)

inductive Step (o : Oracle) : Instr → MachineState → MachineState → Prop
  | ordinary (s t : MachineState) (op : Instr)
      (effect : ordinaryStep s (.base op) = some t) (pc : t.pc = s.pc+4) : Step o op s t
  | permute (s : MachineState) (src dst : Nat) (sourceRoom : src+25 ≤ 2^33) (outRoom : dst+25 ≤ 2^33)
      (source : s.getReg .x10 = wordAddress src) (out : s.getReg .x12 = wordAddress dst)
      (mode : s.getReg .x5 = 0) (len : s.getReg .x11 = 200) (kind : s.getReg .x13 = 1) :
      Step o .ECALL s
        (writeBits s (wordAddress dst) (o.permutation (packBuffer (window (memoryView s) src))))

theorem Step.advance {o : Oracle} {op : Instr} {s t : MachineState} (h : Step o op s t) :
    t.pc = s.pc+4 := by cases h with
  | ordinary _ _ _ _ pc => exact pc
  | permute => rfl

theorem Step.segment {o : Oracle} {op : Instr} {s t : MachineState} (h : Step o op s t)
    (f : fetch im s = some (.base op)) : Segment o im 1 s t := by cases h with
  | ordinary _ _ _ valid _ => exact plain _ _ _ _ _ f valid
  | permute _ _ _ room fits src dst mode len kind =>
    exact permutation _ _ _ _ _ room fits src dst mode len kind f

inductive Run (o : Oracle) : List Instr → MachineState → MachineState → Prop
  | nil (s : MachineState) : Run o [] s s
  | cons {op : Instr} {ops : List Instr} {s t u : MachineState}
      (first : Step o op s t) (rest : Run o ops t u) : Run o (op::ops) s u

theorem Run.one {o op s t} (h : Step o op s t) : Run o [op] s t := .cons h (.nil _)

theorem Run.append {o a b s t u} (l : Run o a s t) (r : Run o b t u) : Run o (a++b) s u := by
  induction l with
  | nil => exact r
  | cons first _ ih => exact .cons first (ih r)

theorem Run.segment {o ops s t} (trace : Run o ops s t) (i : Nat) (pc : s.pc = addr i)
    (ok : LeafCode.matchOps i ops = true) : Segment o im ops.length s t := by
  induction trace generalizing i with
  | nil => exact CommitExact.empty _ _ _
  | @cons op ops s t u step _ ih =>
    simp only [LeafCode.matchOps,Bool.and_eq_true] at ok
    have first := step.segment (LeafCode.fetch_word i op ok.1 s pc)
    have next := (step.advance.trans (congrArg (·+4) pc)).trans (addr_next i).symm
    simpa only [List.length_cons,Nat.add_comm 1] using CommitExact.compose first (ih (i+1) next ok.2)

theorem Run.next_pc {o ops s t} (trace : Run o ops s t) (i : Nat) (pc : s.pc = addr i) :
    t.pc = addr (i+ops.length) := by
  induction trace generalizing i with
  | nil => exact pc
  | @cons op ops s t u step _ ih =>
    have next := (step.advance.trans (congrArg (·+4) pc)).trans (addr_next i).symm
    simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (i+1) next

end CommitGolfCandidate.Reconstruction.LeafSteps
