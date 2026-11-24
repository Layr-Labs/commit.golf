import CommitGolfCandidate.ChainedTailParsePlan
import CommitGolfCandidate.ChainedByteWriteView

/-! Width-table and encoded-source preservation under inverse-row scratch stores. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option Elab.async false
attribute [local irreducible] tailParseStepState

def ParseWidthsAt (s : MachineState) (base : Word) (widths : List Nat) : Prop :=
  ∀ index, index<widths.length →
    s.getByte (base+BitVec.ofNat 64 (2*index+1))=BitVec.ofNat 8 (widths.getD index 0)

def ParseInputAt (s : MachineState) (base : Word) (input : Nat → List Bool) (count : Nat) : Prop :=
  ∀ index, index≤count → s.getByte (base+BitVec.ofNat 64 index)=tailBitsWord 8 (input index)

theorem parse_width_head (s : MachineState) (width : Nat) (widths : List Nat)
    (memory : ParseWidthsAt s (s.getReg .x21) (width::widths)) :
    s.getByte (s.getReg .x21+1)=BitVec.ofNat 8 width := by
  simpa using memory 0 (by simp)

theorem tail_parse_step_width_memory (s : MachineState) (width : Nat) (widths : List Nat)
    (memory : ParseWidthsAt s (s.getReg .x21) (width::widths))
    (fit : 2*(width::widths).length<2^64) :
    ParseWidthsAt (tailParseStepState s) ((tailParseStepState s).getReg .x21) widths := by
  intro index inside
  rw [tail_parse_step_source]
  have location : (s.getReg .x21+2)+BitVec.ofNat 64 (2*index+1)=
      s.getReg .x21+BitVec.ofNat 64 (2*(index+1)+1) := by
    change (s.getReg .x21+BitVec.ofNat 64 2)+BitVec.ofNat 64 (2*index+1)=_
    rw [byte_offset_add]
    rw [show 2+(2*index+1)=2*(index+1)+1 by omega]
  have different : (s.getReg .x21+2)+BitVec.ofNat 64 (2*index+1)≠s.getReg .x21 := by
    rw [location]
    intro same
    have impossible := byte_offset_inj (s.getReg .x21) (2*(index+1)+1) 0
      (by simp only [List.length_cons] at fit; omega) (by decide) (by simpa using same)
    omega
  rw [tail_parse_step_byte,ite_eq_right different,location]
  simpa only [List.getD_cons_succ] using memory (index+1) (by simpa using inside)

theorem tail_parse_step_input_memory (s : MachineState) (width : Nat) (widths : List Nat)
    (input : Nat → List Bool) (advance : Nat) (small : advance≤1)
    (pointer : (tailParseStepState s).getReg .x20=s.getReg .x20+BitVec.ofNat 64 advance)
    (memory : ParseInputAt s (s.getReg .x20) input (width::widths).length)
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) ((width::widths).map fun _ => [])) :
    ParseInputAt (tailParseStepState s) ((tailParseStepState s).getReg .x20)
      (fun i => input (advance+i)) widths.length := by
  intro index inside
  have location : (tailParseStepState s).getReg .x20+BitVec.ofNat 64 index=
      s.getReg .x20+BitVec.ofNat 64 (advance+index) := by
    rw [pointer,byte_offset_add]
  have different : (tailParseStepState s).getReg .x20+BitVec.ofNat 64 index≠s.getReg .x21 := by
    rw [location]
    have separation := apart 0 (by simp only [List.length_map,List.length_cons]; omega)
      (advance+index) (by simp only [List.length_map,List.length_cons]; omega)
    simpa using Ne.symm separation
  rw [tail_parse_step_byte,ite_eq_right different,location]
  exact memory (advance+index) (by simp only [List.length_cons]; omega)

end CommitGolfCandidate.Chained.Native
