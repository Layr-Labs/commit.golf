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

private theorem six_memory (s : MachineState) (source : Reg) (store S T offset : Nat)
    (src : s.getReg source + BitVec.ofNat 64 offset = BitVec.ofNat 64 S)
    (dst : s.getReg .x21 + BitVec.ofNat 64 (store+offset) = BitVec.ofNat 64 T)
    (small : store+offset+6 < 2048) :
    (execCode s (sixRows source store offset)).mem = (chunkMemory s S T true).mem := by
  have addr (k : Nat) (h : k ≤ 6) :
      s.getReg .x21 + signExtend12 (BitVec.ofNat 12 (store+offset+k)) = BitVec.ofNat 64 (T+k) := by
    rw [sign12 _ (by omega), BitVec.ofNat_add, ← BitVec.add_assoc, dst, ← BitVec.ofNat_add]
  have sourceAddr : s.getReg source + signExtend12 (BitVec.ofNat 12 offset) = BitVec.ofNat 64 S := by
    rw [sign12 _ (by omega), src]
  have dst0 : s.getReg .x21 + signExtend12 (BitVec.ofNat 12 (store+offset)) = BitVec.ofNat 64 T := by
    simpa using addr 0 (by omega)
  simp only [execCode, sixRows, chunkMemory, ite_true,
    List.foldl_cons, List.foldl_nil, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0),
    MachineState.getReg_setReg_ne _ .x31 .x21 _ (by decide),
    reg_setHalfword, reg_setWord32, sourceAddr, dst0, addr 2 (by omega), addr 6 (by omega),
    show (16#6).toNat = 16 from rfl, show (32#6).toNat = 32 from rfl, shift_twice, mem_pc]
  simp only [MachineState.setHalfword, MachineState.setWord32, MachineState.setMem,
    MachineState.getMem, mem_pc, mem_reg]
  rfl

private theorem six_regs (s : MachineState) (source : Reg) (store offset : Nat) (r : Reg) (h : r ≠ .x31) :
    (execCode s (sixRows source store offset)).getReg r = s.getReg r := by
  simp [execCode, sixRows, execInstrBr,
    MachineState.getReg_setReg_ne _ .x31 r _ (Ne.symm h), reg_setHalfword, reg_setWord32]

private theorem six_pc (s : MachineState) (source : Reg) (store offset : Nat) :
    (execCode s (sixRows source store offset)).pc = s.pc+16 := by
  simp [execCode, sixRows, execInstrBr, MachineState.setPC, BitVec.add_assoc]

private theorem six_ready (s : MachineState) (source : Reg) (store S T offset : Nat)
    (src : s.getReg source + BitVec.ofNat 64 offset = BitVec.ofNat 64 S)
    (dst : s.getReg .x21 + BitVec.ofNat 64 (store+offset) = BitVec.ofNat 64 T)
    (sa : S % 8 = 0) (ta : T % 4 = 2) (sf : S+8 ≤ MEMORY_BYTES)
    (tf : T+6 ≤ MEMORY_BYTES) (small : store+offset+6 < 2048) : Ready s (sixRows source store offset) := by
  have addr (k : Nat) (h : k ≤ 6) :
      s.getReg .x21 + signExtend12 (BitVec.ofNat 12 (store+offset+k)) = BitVec.ofNat 64 (T+k) := by
    rw [sign12 _ (by omega), BitVec.ofNat_add, ← BitVec.add_assoc, dst, ← BitVec.ofNat_add]
  have dst0 : s.getReg .x21 + signExtend12 (BitVec.ofNat 12 (store+offset)) = BitVec.ofNat 64 T := by
    simpa using addr 0 (by omega)
  have sourceAddr : s.getReg source + signExtend12 (BitVec.ofNat 12 offset) = BitVec.ofNat 64 S := by
    rw [sign12 _ (by omega), src]
  have v0 := access_ok S 8 sa sf
  have v1 := access_ok T 2 (by omega) (by omega : T+2 ≤ MEMORY_BYTES)
  have v2 := access_ok (T+2) 4 (by omega) (by omega : T+2+4 ≤ MEMORY_BYTES)
  simp only [sixRows, Ready, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0),
    MachineState.getReg_setReg_ne _ .x31 .x21 _ (by decide), reg_setHalfword, reg_setWord32,
    sourceAddr, dst0, addr 2 (by omega), addr 6 (by omega), v0, v1, v2, and_self]

private theorem shortPart (s : MachineState) (w : Nat) (src : Reg) (off p S T : Nat)
    (code : Slice w (sixRows src off p)) (bound : w+4≤6144)
    (pc : s.pc=pcAt w) (sr : s.getReg src=BitVec.ofNat 64 S)
    (dr : s.getReg .x21+BitVec.ofNat 64 off=BitVec.ofNat 64 T)
    (sa : (S+p)%8=0) (ta : (T+p)%4=2) (imm : off+p+6<2048)
    (apart : S+p+8≤T+p) (room : T+p+6≤MEMORY_BYTES) :
    Done s (execCode s (sixRows src off p)) (S+p) (T+p) 6 4 (w+4) := by
  have source : s.getReg src+BitVec.ofNat 64 p=BitVec.ofNat 64 (S+p) := by rw [sr,←BitVec.ofNat_add]
  have dest : s.getReg .x21+BitVec.ofNat 64 (off+p)=BitVec.ofNat 64 (T+p) := by
    rw [BitVec.ofNat_add,←BitVec.add_assoc,dr,←BitVec.ofNat_add]
  have mem := six_memory s src off _ _ _ source dest imm
  have ran := code_run (sixRows src off p) w s bound (codeOfSlice code)
    (six_ready s _ _ _ _ _ source dest sa ta (by omega) room imm) pc
    (by intro i hi; simp only [sixRows,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl <;> rfl)
    (by intro u i hi; simp only [sixRows,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl <;> rfl)
  refine ⟨ran,?_,six_regs s _ _ _,
    copy_congr_mem mem (chunk_copy s _ _ true sa ta (by omega)
      (by unfold MEMORY_BYTES at room;omega) (by unfold MEMORY_BYTES at room;omega)),?_⟩
  · rw [six_pc,pc]; exact ofNat_step _ 4
  · intro q low; rw [getMem_congr mem]
    exact chunk_below s _ _ true q (by unfold MEMORY_BYTES at room;omega) low

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
    have h3 := shortPart _ (w+18) src off 24 S T code3 (by omega) h2.pc
      ((acc2.regs _ notTemp).trans sr) (by rw [acc2.regs .x21 (by decide)];exact dr) (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc3 := append acc2 h3 (by omega) (by omega)
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using acc3
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
