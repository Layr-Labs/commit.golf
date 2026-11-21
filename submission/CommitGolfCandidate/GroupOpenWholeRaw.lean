import CommitGolfCandidate.GroupOpenWholeCode

namespace TwoPermutationPrototype.GroupedOpening.Whole
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 PackedOpening
open Wide Shifted30 CapCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

private theorem pairPart (s : MachineState) (w n size : Nat) (src : Reg) (off p S T : Nat)
    (hw : size=2 ∨ size=4 ∨ size=8) (notTemp : src≠.x31)
    (code : Slice w (pairRows n size src p (off+p))) (bound : w+2*n≤6144)
    (pc : s.pc=pcAt w) (sr : s.getReg src=BitVec.ofNat 64 S)
    (dr : s.getReg .x21+BitVec.ofNat 64 off=BitVec.ofNat 64 T)
    (sa : (S+p)%size=0) (ta : (T+p)%size=0) (imm : off+p+size*n≤2048)
    (apart : S+p+size*n≤T) (room : T+p+size*n≤MEMORY_BYTES) :
    Done s (pairsRun size src p (off+p) 0 n s) (S+p) (T+p) (size*n) (2*n) (w+2*n) := by
  have dest : s.getReg .x21+BitVec.ofNat 64 (off+p)=BitVec.ofNat 64 (T+p) := by
    rw [BitVec.ofNat_add,←BitVec.add_assoc,dr,←BitVec.ofNat_add]
  have result := run_pairs size hw src notTemp w p (off+p) S (T+p) sa ta n 0 s
    (by simpa using pairsOfSlice code) (by simpa using bound) (by simpa [pcAt,AlignedFields.pcAt] using pc)
    sr dest (by simp;omega) (by simp;omega) (by simp;omega) (by simp;omega)
  obtain ⟨ran,next,regs,bytes,below⟩ := result
  exact ⟨ran,by simpa using next,regs,by simpa using bytes,below⟩

private theorem shiftPart (s : MachineState) (w : Nat) (src : Reg) (off p S T : Nat)
    (code : Slice w (Shifted32.chunkCode src off p)) (bound : w+6≤6144)
    (pc : s.pc=pcAt w) (sr : s.getReg src=BitVec.ofNat 64 S)
    (dr : s.getReg .x21+BitVec.ofNat 64 off=BitVec.ofNat 64 T)
    (sa : (S+p)%8=0) (ta : (T+p)%4=2) (imm : off+p+6<2048)
    (apart : S+p+8≤T) (room : T+p+8≤MEMORY_BYTES) :
    Done s (execCode s (Shifted32.chunkCode src off p)) (S+p) (T+p) 8 6 (w+6) := by
  have source : s.getReg src+BitVec.ofNat 64 p=BitVec.ofNat 64 (S+p) := by rw [sr,←BitVec.ofNat_add]
  have dest : s.getReg .x21+BitVec.ofNat 64 (off+p)=BitVec.ofNat 64 (T+p) := by
    rw [BitVec.ofNat_add,←BitVec.add_assoc,dr,←BitVec.ofNat_add]
  have mem := Shifted32.chunk_memory s src off _ _ _ source dest imm
  have ran := code_run (Shifted32.chunkCode src off p) w s bound (codeOfSlice code)
    (Shifted32.chunk_ready s _ _ _ _ _ source dest sa ta (by omega) room imm) pc
    (by intro i hi; simp only [Shifted32.chunkCode,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
    (by intro u i hi; simp only [Shifted32.chunkCode,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
  refine ⟨ran,?_,Shifted32.chunk_regs s _ _ _,
    copy_congr_mem mem (chunk_copy s _ _ false sa ta (by omega)
      (by unfold MEMORY_BYTES at room;omega) (by unfold MEMORY_BYTES at room;omega)),?_⟩
  · rw [Shifted32.chunk_pc,pc]; exact ofNat_step _ 6
  · intro q low; rw [getMem_congr mem]
    exact chunk_below s _ _ false q (by unfold MEMORY_BYTES at room;omega) low

theorem raw_run (q : Shape) (s : MachineState) (w : Nat) (src : Reg) (off S T : Nat)
    (code : RawCode q w src off) (bound : w+q.cycles≤6144) (pc : s.pc=pcAt w)
    (notTemp : src≠.x31) (sr : s.getReg src=BitVec.ofNat 64 S)
    (dr : s.getReg .x21+BitVec.ofNat 64 off=BitVec.ofNat 64 T)
    (sa : S%8=0) (ta : TargetAligned q T) (imm : off+32≤2048)
    (apart : S+q.size≤T) (room : T+q.size≤MEMORY_BYTES) :
    Done s (rawState q src off s) S T q.size q.cycles (w+q.cycles) := by
  cases q with
  | d16 =>
    change w+4≤6144 at bound
    change S+16≤T at apart
    change T+16≤MEMORY_BYTES at room
    change T%8=0 at ta
    have h0 := pairPart s (w+0) 2 8 src off 0 S T (by decide) notTemp code (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using acc0
  | w16 =>
    change w+8≤6144 at bound
    change S+16≤T at apart
    change T+16≤MEMORY_BYTES at room
    change T%8=4 at ta
    have h0 := pairPart s (w+0) 4 4 src off 0 S T (by decide) notTemp code (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using acc0
  | s16 =>
    change w+12≤6144 at bound
    change S+16≤T at apart
    change T+16≤MEMORY_BYTES at room
    change T%4=2 at ta
    obtain ⟨code0,code1⟩ := code
    have h0 := shiftPart s (w+0) src off 0 S T code0 (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    have h1 := shiftPart _ (w+6) src off 8 S T code1 (by omega) h0.pc
      ((acc0.regs _ notTemp).trans sr) (by rw [acc0.regs .x21 (by decide)];exact dr) (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc1 := append acc0 h1 (by omega) (by omega)
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using acc1
  | d28 =>
    change w+8≤6144 at bound
    change S+28≤T at apart
    change T+28≤MEMORY_BYTES at room
    change T%8=0 at ta
    obtain ⟨code0,code1⟩ := code
    have h0 := pairPart s (w+0) 3 8 src off 0 S T (by decide) notTemp code0 (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    have h1 := pairPart _ (w+6) 1 4 src off 24 S T (by decide) notTemp code1 (by omega) h0.pc
      ((acc0.regs _ notTemp).trans sr) (by rw [acc0.regs .x21 (by decide)];exact dr) (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc1 := append acc0 h1 (by omega) (by omega)
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using acc1
  | w28 =>
    change w+14≤6144 at bound
    change S+28≤T at apart
    change T+28≤MEMORY_BYTES at room
    change T%8=4 at ta
    have h0 := pairPart s (w+0) 7 4 src off 0 S T (by decide) notTemp code (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using acc0
  | s28 =>
    change w+22≤6144 at bound
    change S+28≤T at apart
    change T+28≤MEMORY_BYTES at room
    change T%4=2 at ta
    obtain ⟨code0,code1,code2,code3⟩ := code
    have h0 := shiftPart s (w+0) src off 0 S T code0 (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    have h1 := shiftPart _ (w+6) src off 8 S T code1 (by omega) h0.pc
      ((acc0.regs _ notTemp).trans sr) (by rw [acc0.regs .x21 (by decide)];exact dr) (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc1 := append acc0 h1 (by omega) (by omega)
    have h2 := shiftPart _ (w+12) src off 16 S T code2 (by omega) h1.pc
      ((acc1.regs _ notTemp).trans sr) (by rw [acc1.regs .x21 (by decide)];exact dr) (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc2 := append acc1 h2 (by omega) (by omega)
    have h3 := pairPart _ (w+18) 2 2 src off 24 S T (by decide) notTemp code3 (by omega) h2.pc
      ((acc2.regs _ notTemp).trans sr) (by rw [acc2.regs .x21 (by decide)];exact dr) (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc3 := append acc2 h3 (by omega) (by omega)
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using acc3
  | d30 =>
    change w+10≤6144 at bound
    change S+30≤T at apart
    change T+30≤MEMORY_BYTES at room
    change T%8=0 at ta
    obtain ⟨code0,code1,code2⟩ := code
    have h0 := pairPart s (w+0) 3 8 src off 0 S T (by decide) notTemp code0 (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    have h1 := pairPart _ (w+6) 1 4 src off 24 S T (by decide) notTemp code1 (by omega) h0.pc
      ((acc0.regs _ notTemp).trans sr) (by rw [acc0.regs .x21 (by decide)];exact dr) (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc1 := append acc0 h1 (by omega) (by omega)
    have h2 := pairPart _ (w+8) 1 2 src off 28 S T (by decide) notTemp code2 (by omega) h1.pc
      ((acc1.regs _ notTemp).trans sr) (by rw [acc1.regs .x21 (by decide)];exact dr) (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc2 := append acc1 h2 (by omega) (by omega)
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using acc2
  | w30 =>
    change w+16≤6144 at bound
    change S+30≤T at apart
    change T+30≤MEMORY_BYTES at room
    change T%8=4 at ta
    obtain ⟨code0,code1⟩ := code
    have h0 := pairPart s (w+0) 7 4 src off 0 S T (by decide) notTemp code0 (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    have h1 := pairPart _ (w+14) 1 2 src off 28 S T (by decide) notTemp code1 (by omega) h0.pc
      ((acc0.regs _ notTemp).trans sr) (by rw [acc0.regs .x21 (by decide)];exact dr) (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc1 := append acc0 h1 (by omega) (by omega)
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using acc1
  | s30 =>
    change w+22≤6144 at bound
    change S+30≤T at apart
    change T+30≤MEMORY_BYTES at room
    change T%4=2 at ta
    obtain ⟨ss,oo,rows⟩ := code
    subst src; subst off
    have h := copy30_done w s S T bound (fun j => codeOfSlice (rows j)) pc sr (by simpa using dr)
      sa ta apart (by omega) room
    exact ⟨h.run,h.pc,h.regs,h.bytes,h.below⟩
  | d32 =>
    change w+8≤6144 at bound
    change S+32≤T at apart
    change T+32≤MEMORY_BYTES at room
    change T%8=0 at ta
    have h0 := pairPart s (w+0) 4 8 src off 0 S T (by decide) notTemp code (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using acc0
  | w32 =>
    change w+16≤6144 at bound
    change S+32≤T at apart
    change T+32≤MEMORY_BYTES at room
    change T%8=4 at ta
    have h0 := pairPart s (w+0) 8 4 src off 0 S T (by decide) notTemp code (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using acc0
  | s32 =>
    change w+24≤6144 at bound
    change S+32≤T at apart
    change T+32≤MEMORY_BYTES at room
    change T%4=2 at ta
    obtain ⟨code0,code1,code2,code3⟩ := code
    have h0 := shiftPart s (w+0) src off 0 S T code0 (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    have h1 := shiftPart _ (w+6) src off 8 S T code1 (by omega) h0.pc
      ((acc0.regs _ notTemp).trans sr) (by rw [acc0.regs .x21 (by decide)];exact dr) (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc1 := append acc0 h1 (by omega) (by omega)
    have h2 := shiftPart _ (w+12) src off 16 S T code2 (by omega) h1.pc
      ((acc1.regs _ notTemp).trans sr) (by rw [acc1.regs .x21 (by decide)];exact dr) (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc2 := append acc1 h2 (by omega) (by omega)
    have h3 := shiftPart _ (w+18) src off 24 S T code3 (by omega) h2.pc
      ((acc2.regs _ notTemp).trans sr) (by rw [acc2.regs .x21 (by decide)];exact dr) (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc3 := append acc2 h3 (by omega) (by omega)
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using acc3


theorem field_copy (c : Fin 4) (f : Fin 18) (s : MachineState) (S T : Nat)
    (pc : s.pc=pcAt (rawStart c f)) (sr : s.getReg (source f)=BitVec.ofNat 64 S)
    (dr : s.getReg .x21+BitVec.ofNat 64 (offset f)=BitVec.ofNat 64 T)
    (sa : S%8=0) (r : T%8=destResidue c f)
    (apart : S+width f≤T) (room : T+width f≤MEMORY_BYTES) :
    Done s (rawState (shape c f) (source f) (offset f) s) S T (width f) (shape c f).cycles (rawStart c f+(shape c f).cycles) := by
  obtain ⟨bound,len,tmp,imm⟩ := placed c f
  rw [← len] at apart room ⊢
  exact raw_run _ s _ _ _ S T (raw_code c f) bound pc tmp sr dr sa (target_aligned c f T r) imm apart room

def copy (c f : Nat) (s : MachineState) := rawState (shape c f) (source f) (offset f) s

end TwoPermutationPrototype.GroupedOpening.Whole
