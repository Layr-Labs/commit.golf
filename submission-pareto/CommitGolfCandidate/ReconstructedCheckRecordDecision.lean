import CommitGolfCandidate.ReconstructedCheckRecordEffect
import CommitGolfCandidate.ReconstructedCheckRecordGuard

namespace CommitGolfCandidate.Reconstruction.CheckRecordDecision
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecorded CheckLayout CheckRecordABI CheckRecordSlots
open TwoPermutationPrototype.RV64
set_option maxRecDepth 13500
set_option maxHeartbeats 1500000
abbrev W:=BitVec.ofNat 64

def Compatible (a : Slots) (k : Nat) (node : Binding.Digest) := a k=none ∨ a k=some node
deriving instance Decidable for Compatible

def checkKeep : List Reg := [.x2,.x8,.x5,.x6,.x7,.x10,.x11,.x12,.x13,.x14,.x15,.x19,.x23,.x24]

theorem decision (o : Oracle) (s : MachineState) (a : Slots) (k : Nat) (node : Binding.Digest) (small : k<1024)
    (state : Holds s a) (input : CheckPairPhysical.child s CheckPair.current node)
    (entry : s.pc=(if s.getByte (CheckRecordAccess.flag k)=0 then CommitBlocks.addr 109 else CommitBlocks.addr 398))
    (scaled : s.getReg .x23=W (32*k)) :
    ∃ t n,n≤11 ∧ Segment o n s t [] ∧ t.pc=(if Compatible a k node then CommitBlocks.addr 109 else CommitBlocks.addr 57) ∧
      (∀ r∈checkKeep,t.getReg r=s.getReg r) ∧ CheckRecordAccess.Mem s t := by
  cases logged : a k with
  | none=>
    have flag : s.getByte (CheckRecordAccess.flag k)=0:=by rw [state.flag k small,logged];rfl
    have yes : Compatible a k node:=Or.inl logged
    exact ⟨s,0,by decide,CheckRecorded.empty o s,by simpa only [ite_eq_left flag,ite_eq_left yes] using entry,fun _ _=>rfl,fun _ _=>rfl⟩
  | some old=>
    have flag : s.getByte (CheckRecordAccess.flag k)≠0:=by rw [state.flag k small,logged];change 1#8 ≠ 0#8;decide
    have compared:=CheckSlotCompare.positive o s k small (by simpa only [ite_eq_right flag] using entry) scaled
    obtain ⟨t,n,lim,run,pc,regs,mem⟩:=compared
    have iff : (∀ j : Fin 4,CheckSlotCompare.EqualAt s k j) ↔ Compatible a k node:=by
      rw [cellAgree s k node input old (state.words k small old logged)];simp [Compatible,logged]
    exact ⟨t,n,lim,run,by simpa only [iff] using pc,
      fun r hr=>regs r ((by decide : ∀ q : Reg,q∈checkKeep→CheckSlotWords.reserve q) r hr),mem⟩

structure Failure (s : MachineState) : Prop where
  pc : s.pc=CommitBlocks.addr 57
  status : s.getReg .x10=0xffffffffffffffff#64
  sp : s.getReg .x2=W CheckLayout.sp
  saved : s.getMem (W (CheckLayout.fp-8))=CommitBlocks.addr 20

structure Advance (s : MachineState) (input : CheckInput) (a : Slots) (i : Nat) : Prop where
  pc : s.pc=CommitBlocks.addr (if i=input.positions.card then 409 else 122)
  sp : s.getReg .x2=W CheckLayout.sp
  fp : s.getReg .x8=W CheckLayout.fp
  ordinal : s.getReg .x17=W i
  cursor : s.getReg .x24=W (CheckRecordSpec.cursor i)
  proof : s.getReg .x19=W proofBase
  beginCopy : s.getReg .x6=W (CheckLayout.fp-2328)
  endCopy : s.getReg .x7=W (CheckLayout.fp-2072)
  kept : Persistent s input
  slots : Holds s a
  count : s.getReg .x5=W input.positions.card

theorem registers {s : MachineState} {input : CheckInput} {a : Slots} {i : Nat} (h : Advance s input a i) (more : i < input.positions.card) :
    Registers s i (CheckRecordSpec.cursor i) :=
  ⟨by simpa only [ite_eq_right (Nat.ne_of_lt more)] using h.pc,h.sp,h.fp,h.ordinal,h.cursor,h.proof,h.beginCopy,h.endCopy⟩

end CommitGolfCandidate.Reconstruction.CheckRecordDecision
