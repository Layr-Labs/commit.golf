import CommitGolfCandidate.GroupOpenWholeCode

namespace TwoPermutationPrototype.GroupedOpening.Whole
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 PackedOpening
open Wide Shifted30 CapCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

private theorem pairPart (s : MachineState) (w n size : Nat) (src : Reg) (off p S T : Nat)
    (hw : size=2 ∨ size=4 ∨ size=8) (notTemp : src≠.x31)
    (code : Slice w (pairRows n size src p (off+p))) (bound : w+2*n≤7872)
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

structure RawDone (s t : MachineState) (S T n cost word : Nat) : Prop where
  run : RunsOpeningBlock s t cost
  pc : t.pc=pcAt word
  regs : ∀ r, Carry.Free r → t.getReg r=s.getReg r
  bytes : ByteCopy s t S T n
  below : ∀ q : Word, q.toNat<T-T%8 → t.getMem q=s.getMem q

private theorem widen {s t S T n cost word} (done : Done s t S T n cost word) :
    RawDone s t S T n cost word :=
  ⟨done.run,done.pc,fun r free => done.regs r free.1,done.bytes,done.below⟩

private theorem carry_run (ops : List Carry.Op) (s : MachineState) (w : Nat) (src : Reg)
    (off S T n price : Nat) (cfg : Carry.Bounds s S T n src off)
    (code : Slice w (Carry.rows src off 0 ops)) (cycles : (Carry.rows src off 0 ops).length=price)
    (bound : w+price≤7872) (pc : s.pc=pcAt w)
    (valid : ∀ D v, Carry.Valid D (T%8) n 0 v ops) :
    RawDone s (execCode s (Carry.rows src off 0 ops)) S T n price (w+price) := by
  let v : Carry.Values := fun t => s.getReg t.reg
  have initial : Carry.Track s s S T 0 v := ⟨fun _=>rfl,fun _ _=>rfl,copy_zero s S T,fun _ _=>rfl⟩
  have ⟨ready,u,done,p⟩:=Carry.block cfg ops s 0 v initial (valid _ _)
  have simple:=Carry.rows_simple src off 0 ops
  refine ⟨?_,?_,done.fixed,done.copy,done.below⟩
  · rw [←cycles] at bound ⊢
    exact code_run _ w s bound (codeOfSlice code) ready pc (fun i h=>(simple i h).1)
      (fun m i h=>(simple i h).2 m)
  · rw [p,pc,cycles];exact ofNat_step _ _

theorem raw_run (q : Shape) (s : MachineState) (w : Nat) (src : Reg) (off S T : Nat)
    (code : RawCode q w src off) (bound : w+q.cycles≤7872) (pc : s.pc=pcAt w)
    (free : Carry.Free src) (sr : s.getReg src=BitVec.ofNat 64 S)
    (dr : s.getReg .x21+BitVec.ofNat 64 off=BitVec.ofNat 64 T)
    (sa : S%8=0) (ta : TargetAligned q T) (imm : off+32≤2048)
    (apart32 : S+32≤T) (room : T+q.size≤MEMORY_BYTES) :
    RawDone s (rawState q src off s) S T q.size q.cycles (w+q.cycles) := by
  have notTemp:=free.1
  have small : q.size≤32 := by cases q <;> decide
  have apart : S+q.size≤T := by omega
  cases q with
  | d16 =>
    change w+4≤7872 at bound
    change S+16≤T at apart
    change T+16≤MEMORY_BYTES at room
    change T%8=0 at ta
    have h0 := pairPart s (w+0) 2 8 src off 0 S T (by decide) notTemp code (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using (widen acc0)
  | w16 =>
    change w+8≤7872 at bound
    change S+16≤T at apart
    change T+16≤MEMORY_BYTES at room
    change T%8=4 at ta
    have h0 := pairPart s (w+0) 4 4 src off 0 S T (by decide) notTemp code (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using (widen acc0)
  | s16r2 =>
    exact carry_run Carry.s16r2 s w src off S T 16 11 ⟨sr,dr,free,sa,apart32,room,small,imm⟩
      code rfl bound pc (by change T%8=2 at ta; rw [ta];exact Carry.s16r2_valid)
  | s16r6 =>
    exact carry_run Carry.s16r6 s w src off S T 16 11 ⟨sr,dr,free,sa,apart32,room,small,imm⟩
      code rfl bound pc (by change T%8=6 at ta; rw [ta];exact Carry.s16r6_valid)
  | d28 =>
    change w+8≤7872 at bound
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
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using (widen acc1)
  | w28 =>
    change w+14≤7872 at bound
    change S+28≤T at apart
    change T+28≤MEMORY_BYTES at room
    change T%8=4 at ta
    have h0 := pairPart s (w+0) 7 4 src off 0 S T (by decide) notTemp code (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using (widen acc0)
  | s28r2 =>
    exact carry_run Carry.s28r2 s w src off S T 28 20 ⟨sr,dr,free,sa,apart32,room,small,imm⟩
      code rfl bound pc (by change T%8=2 at ta; rw [ta];exact Carry.s28r2_valid)
  | s28r6 =>
    exact carry_run Carry.s28r6 s w src off S T 28 19 ⟨sr,dr,free,sa,apart32,room,small,imm⟩
      code rfl bound pc (by change T%8=6 at ta; rw [ta];exact Carry.s28r6_valid)
  | d30 =>
    change w+10≤7872 at bound
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
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using (widen acc2)
  | w30 =>
    change w+16≤7872 at bound
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
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using (widen acc1)
  | s30r2 =>
    exact carry_run Carry.s30r2 s w src off S T 30 19 ⟨sr,dr,free,sa,apart32,room,small,imm⟩
      code rfl bound pc (by change T%8=2 at ta; rw [ta];exact Carry.s30r2_valid)
  | s30r6 =>
    exact carry_run Carry.s30r6 s w src off S T 30 19 ⟨sr,dr,free,sa,apart32,room,small,imm⟩
      code rfl bound pc (by change T%8=6 at ta; rw [ta];exact Carry.s30r6_valid)
  | d32 =>
    change w+8≤7872 at bound
    change S+32≤T at apart
    change T+32≤MEMORY_BYTES at room
    change T%8=0 at ta
    have h0 := pairPart s (w+0) 4 8 src off 0 S T (by decide) notTemp code (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using (widen acc0)
  | w32 =>
    change w+16≤7872 at bound
    change S+32≤T at apart
    change T+32≤MEMORY_BYTES at room
    change T%8=4 at ta
    have h0 := pairPart s (w+0) 8 4 src off 0 S T (by decide) notTemp code (by omega) pc
      sr dr (by omega) (by omega) (by omega) (by omega) (by omega)
    have acc0 := h0
    simpa only [rawState,Shape.size,Shape.cycles,Nat.add_zero,Nat.zero_add,Nat.add_assoc] using (widen acc0)
  | s32r2 =>
    exact carry_run Carry.s32r2 s w src off S T 32 21 ⟨sr,dr,free,sa,apart32,room,small,imm⟩
      code rfl bound pc (by change T%8=2 at ta; rw [ta];exact Carry.s32r2_valid)
  | s32r6 =>
    exact carry_run Carry.s32r6 s w src off S T 32 21 ⟨sr,dr,free,sa,apart32,room,small,imm⟩
      code rfl bound pc (by change T%8=6 at ta; rw [ta];exact Carry.s32r6_valid)

theorem field_copy (c : Fin 4) (f : Fin 18) (s : MachineState) (S T : Nat)
    (pc : s.pc=pcAt (rawStart c f)) (sr : s.getReg (source f)=BitVec.ofNat 64 S)
    (dr : s.getReg .x21+BitVec.ofNat 64 (offset f)=BitVec.ofNat 64 T)
    (sa : S%8=0) (r : T%8=destResidue c f)
    (apart : S+32≤T) (room : T+width f≤MEMORY_BYTES) :
    RawDone s (rawState (shape c f) (source f) (offset f) s) S T (width f) (shape c f).cycles (rawStart c f+(shape c f).cycles) := by
  obtain ⟨bound,len,tmp,imm⟩ := placed c f
  rw [← len] at room ⊢
  exact raw_run _ s _ _ _ S T (raw_code c f) bound pc tmp sr dr sa (target_aligned c f T r) imm apart room

def copy (c f : Nat) (s : MachineState) := rawState (shape c f) (source f) (offset f) s

end TwoPermutationPrototype.GroupedOpening.Whole
