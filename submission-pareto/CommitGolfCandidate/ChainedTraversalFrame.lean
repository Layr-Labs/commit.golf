import CommitGolfCandidate.ChainedRecordTailSetup

/-! Register frames and exact output cursors for complete native field/tail traversals. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem raw_fields_register (fields : List RawField) (s : MachineState) (reg : Reg)
    (a : reg≠.x5) (b : reg≠.x6) (c : reg≠.x7) (d : reg≠.x9) (e : reg≠.x10) (f : reg≠.x11) :
    (rawFieldsState fields s).getReg reg=s.getReg reg := by
  induction fields generalizing s with
  | nil => rw [raw_fields_zero]
  | cons field fields ih =>
    rw [raw_fields_cons,ih,RawField.state,preparedFieldState,field_build_frame _ _ reg a b c f,
      field_header_frame _ _ _ reg d e]

theorem tail_step_register (s : MachineState) (reg : Reg)
    (a : reg≠.x20) (b : reg≠.x21) (c : reg≠.x22) (d : reg≠.x23)
    (e : reg≠.x24) (f : reg≠.x25) (g : reg≠.x26) (h : reg≠.x28) :
    (tailStepState s).getReg reg=s.getReg reg := by
  rw [tail_step_emit_register s reg c,tail_emit_frame _ reg a d f h,tail_load_frame _ reg b e g]

theorem tail_fields_register (n : Nat) (s : MachineState) (reg : Reg)
    (a : reg≠.x20) (b : reg≠.x21) (c : reg≠.x22) (d : reg≠.x23)
    (e : reg≠.x24) (f : reg≠.x25) (g : reg≠.x26) (h : reg≠.x28) :
    (tailFieldsState n s).getReg reg=s.getReg reg := by
  induction n generalizing s with
  | zero => rw [tail_fields_state_zero]
  | succ n ih => rw [tail_fields_state_succ,ih,tail_step_register _ reg a b c d e f g h]

theorem tail_traverse_register (n : Nat) (s : MachineState) (reg : Reg)
    (a : reg≠.x20) (b : reg≠.x21) (c : reg≠.x22) (d : reg≠.x23)
    (e : reg≠.x24) (f : reg≠.x25) (g : reg≠.x26) (h : reg≠.x28) :
    (tailTraverseState n s).getReg reg=s.getReg reg := by
  rw [tailTraverseState,tail_finish_frame _ reg a,tail_fields_register _ _ reg a b c d e f g h,tail_entry_register]

theorem native_tail_cursor (rows : List (List Bool)) (front : List Bool) (s : MachineState)
    (buffer : TailBuffer s front) (small : ∀ row ∈ rows, row.length≤6)
    (memory : BytesAt s (s.getReg .x21) (descriptorBytes rows))
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) rows) :
    (tailFinishState (tailFieldsState rows.length s)).getReg .x20=
      s.getReg .x20+BitVec.ofNat 64 (packedBits (front++rows.flatten)).length := by
  obtain ⟨finalBuffer,_,finalPointer⟩ := native_tail_plan rows front s buffer small memory apart
  have length := congrArg List.length (tail_plan_packed rows front buffer.pending small)
  rw [List.length_append] at length
  rw [tail_finish_pointer,tail_empty_bits _ _ finalBuffer.count finalBuffer.pending,finalPointer]
  by_cases empty : (tailPlanCarry front rows).length=0
  · simp only [empty,decide_true,↓reduceIte,finishTailBytes,List.length_nil,Nat.add_zero] at length ⊢
    rw [length]
  · simp only [empty,decide_false,↓reduceIte,finishTailBytes,List.length_singleton] at length ⊢
    have location : (s.getReg .x20+BitVec.ofNat 64 (tailPlanBytes front rows).length)+1=
        s.getReg .x20+BitVec.ofNat 64 ((tailPlanBytes front rows).length+1) := by
      change (_+BitVec.ofNat 64 _)+BitVec.ofNat 64 1=_
      rw [byte_offset_add]
    rw [location,length]
    simp only [Bool.false_eq_true,↓reduceIte]

end CommitGolfCandidate.Chained.Native
