import CommitGolfCandidate.GroupOpenShifted30

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open PackedOpening (ByteCopy)
open Wide Shifted30
set_option maxRecDepth 8192

namespace Shifted32

def chunkCode (source : Reg) (store offset : Nat) : List Instr :=
  [.LD .x31 source (BitVec.ofNat 12 offset), .SH .x21 .x31 (BitVec.ofNat 12 (store+offset)),
   .SRLI .x31 .x31 16, .SW .x21 .x31 (BitVec.ofNat 12 (store+offset+2)),
   .SRLI .x31 .x31 32, .SH .x21 .x31 (BitVec.ofNat 12 (store+offset+6))]

theorem chunk_memory (s : MachineState) (source : Reg) (store S T offset : Nat)
    (src : s.getReg source + BitVec.ofNat 64 offset = BitVec.ofNat 64 S)
    (dst : s.getReg .x21 + BitVec.ofNat 64 (store+offset) = BitVec.ofNat 64 T)
    (small : store+offset+6 < 2048) :
    (execCode s (chunkCode source store offset)).mem = (chunkMemory s S T false).mem := by
  have addr (k : Nat) (h : k ≤ 6) :
      s.getReg .x21 + signExtend12 (BitVec.ofNat 12 (store+offset+k)) = BitVec.ofNat 64 (T+k) := by
    rw [sign12 _ (by omega), BitVec.ofNat_add, ← BitVec.add_assoc, dst, ← BitVec.ofNat_add]
  have sourceAddr : s.getReg source + signExtend12 (BitVec.ofNat 12 offset) = BitVec.ofNat 64 S := by
    rw [sign12 _ (by omega), src]
  have dst0 : s.getReg .x21 + signExtend12 (BitVec.ofNat 12 (store+offset)) = BitVec.ofNat 64 T := by
    simpa using addr 0 (by omega)
  simp only [execCode, chunkCode, chunkMemory, Bool.false_eq_true, ite_false,
    List.foldl_cons, List.foldl_nil, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0),
    MachineState.getReg_setReg_ne _ .x31 .x21 _ (by decide),
    reg_setHalfword, reg_setWord32, sourceAddr, dst0, addr 2 (by omega), addr 6 (by omega),
    show (16#6).toNat = 16 from rfl, show (32#6).toNat = 32 from rfl, shift_twice, mem_pc]
  simp only [MachineState.setHalfword, MachineState.setWord32, MachineState.setMem,
    MachineState.getMem, mem_pc, mem_reg]
  rfl

theorem chunk_regs (s : MachineState) (source : Reg) (store offset : Nat) (r : Reg) (h : r ≠ .x31) :
    (execCode s (chunkCode source store offset)).getReg r = s.getReg r := by
  simp [execCode, chunkCode, execInstrBr,
    MachineState.getReg_setReg_ne _ .x31 r _ (Ne.symm h), reg_setHalfword, reg_setWord32]

theorem chunk_pc (s : MachineState) (source : Reg) (store offset : Nat) :
    (execCode s (chunkCode source store offset)).pc = s.pc+24 := by
  simp [execCode, chunkCode, execInstrBr, MachineState.setPC, BitVec.add_assoc]

theorem chunk_ready (s : MachineState) (source : Reg) (store S T offset : Nat)
    (src : s.getReg source + BitVec.ofNat 64 offset = BitVec.ofNat 64 S)
    (dst : s.getReg .x21 + BitVec.ofNat 64 (store+offset) = BitVec.ofNat 64 T)
    (sa : S % 8 = 0) (ta : T % 4 = 2) (sf : S+8 ≤ MEMORY_BYTES)
    (tf : T+8 ≤ MEMORY_BYTES) (small : store+offset+6 < 2048) : Ready s (chunkCode source store offset) := by
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
  have v3 := access_ok (T+6) 2 (by omega) (by omega : T+6+2 ≤ MEMORY_BYTES)
  simp only [chunkCode, Ready, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0),
    MachineState.getReg_setReg_ne _ .x31 .x21 _ (by decide), reg_setHalfword, reg_setWord32,
    sourceAddr, dst0, addr 2 (by omega), addr 6 (by omega), v0, v1, v2, v3, and_self]

theorem chunk_decoded (site : CopySite) (wide : site.wide = true) : ∀ k : Fin 4,
    CodeAt (site.start+2+6*k.val) (chunkCode site.source site.destOffset (8*k.val)) := by
  cases site with
  | quartet j => clear wide; revert j; unfold CodeAt; decide +kernel
  | firstSibling => unfold CodeAt; decide +kernel
  | _ => simp [CopySite.wide] at wide

structure ChunkDone (s t : MachineState) (S T word : Nat) : Prop where
  run : RunsOpeningBlock s t 6
  pc : t.pc = BitVec.ofNat 64 (4096+4*(word+6))
  regs : ∀ r, r ≠ .x31 → t.getReg r = s.getReg r
  bytes : ByteCopy s t S T 8
  below : ∀ q : Word, q.toNat < T-T%8 → t.getMem q = s.getMem q

theorem chunk_done (site : CopySite) (wide : site.wide = true) (k : Fin 4) (s : MachineState) (S T : Nat)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*(site.start+2+6*k.val)))
    (src : s.getReg site.source = BitVec.ofNat 64 S)
    (dst : s.getReg .x21 + BitVec.ofNat 64 site.destOffset = BitVec.ofNat 64 T)
    (sa : S % 8 = 0) (ta : T % 4 = 2) (apart : S+32 ≤ T)
    (sf : S+32 ≤ MEMORY_BYTES) (tf : T+32 ≤ MEMORY_BYTES) :
    ChunkDone s (execCode s (chunkCode site.source site.destOffset (8*k.val)))
      (S+8*k.val) (T+8*k.val) (site.start+2+6*k.val) := by
  have hk := k.isLt
  have bounds : site.start+32 ≤ 1062 ∧ site.destOffset+32 ≤ 2000 := by
    clear pc src dst
    cases site with
    | quartet j => clear wide; revert j; decide
    | firstSibling => decide
    | _ => simp [CopySite.wide] at wide
  have src' : s.getReg site.source + BitVec.ofNat 64 (8*k.val) = BitVec.ofNat 64 (S+8*k.val) := by
    rw [src, ← BitVec.ofNat_add]
  have dst' : s.getReg .x21 + BitVec.ofNat 64 (site.destOffset+8*k.val) = BitVec.ofNat 64 (T+8*k.val) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, dst, ← BitVec.ofNat_add]
  have memory := chunk_memory s site.source site.destOffset _ _ _ src' dst' (by omega)
  have run := code_run (chunkCode site.source site.destOffset (8*k.val)) _ s (by simp [chunkCode]; omega)
    (chunk_decoded site wide k) (chunk_ready s _ _ _ _ _ src' dst' (by omega) (by omega) (by omega) (by omega) (by omega)) pc
    (by intro i hi; simp only [chunkCode, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi; rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
    (by intro u i hi; simp only [chunkCode, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi; rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
  refine ⟨run, ?_, chunk_regs s _ _ _ , ?_, ?_⟩
  · rw [chunk_pc, pc, show (24 : Word) = BitVec.ofNat 64 (4*6) from rfl, ofNat_step]
  · exact copy_congr_mem memory (chunk_copy s _ _ false (by omega) (by omega) (by omega)
      (by unfold MEMORY_BYTES at sf; omega) (by unfold MEMORY_BYTES at tf; omega))
  · intro q below
    rw [getMem_congr memory]
    exact chunk_below s _ _ false q (by unfold MEMORY_BYTES at tf; omega) below

def copy32 (site : CopySite) (s : MachineState) : MachineState :=
  execCode (execCode (execCode (execCode s (chunkCode site.source site.destOffset 0))
    (chunkCode site.source site.destOffset 8)) (chunkCode site.source site.destOffset 16))
    (chunkCode site.source site.destOffset 24)

structure CopyDone (site : CopySite) (s t : MachineState) (S T : Nat) : Prop where
  run : RunsOpeningBlock s t 24
  pc : t.pc = BitVec.ofNat 64 (4096+4*(site.start+26))
  regs : ∀ r, r ≠ .x31 → t.getReg r = s.getReg r
  bytes : ByteCopy s t S T 32
  below : ∀ q : Word, q.toNat < T-T%8 → t.getMem q = s.getMem q

theorem copy32_done (site : CopySite) (wide : site.wide = true) (src31 : site.source ≠ .x31)
    (s : MachineState) (S T : Nat) (pc : s.pc = BitVec.ofNat 64 (4096+4*(site.start+2)))
    (src : s.getReg site.source = BitVec.ofNat 64 S)
    (dst : s.getReg .x21 + BitVec.ofNat 64 site.destOffset = BitVec.ofNat 64 T)
    (sa : S % 8 = 0) (ta : T % 4 = 2) (apart : S+32 ≤ T)
    (sf : S+32 ≤ MEMORY_BYTES) (tf : T+32 ≤ MEMORY_BYTES) :
    CopyDone site s (copy32 site s) S T := by
  let a := execCode s (chunkCode site.source site.destOffset 0)
  let b := execCode a (chunkCode site.source site.destOffset 8)
  let c := execCode b (chunkCode site.source site.destOffset 16)
  let d := execCode c (chunkCode site.source site.destOffset 24)
  have c0 : ChunkDone s a S T (site.start+2) := by
    simpa using chunk_done site wide (0 : Fin 4) s S T pc src dst sa ta apart sf tf
  have c1 : ChunkDone a b (S+8) (T+8) (site.start+8) := by
    simpa [Nat.add_assoc] using chunk_done site wide (1 : Fin 4) a S T c0.pc
      ((c0.regs _ src31).trans src) (by rw [c0.regs .x21 (by decide)]; exact dst) sa ta apart sf tf
  have c2 : ChunkDone b c (S+16) (T+16) (site.start+14) := by
    simpa [Nat.add_assoc] using chunk_done site wide (2 : Fin 4) b S T (by simpa [Nat.add_assoc] using c1.pc)
      ((c1.regs _ src31).trans ((c0.regs _ src31).trans src))
      (by rw [c1.regs .x21 (by decide), c0.regs .x21 (by decide)]; exact dst) sa ta apart sf tf
  have c3 : ChunkDone c d (S+24) (T+24) (site.start+20) := by
    simpa [Nat.add_assoc] using chunk_done site wide (3 : Fin 4) c S T (by simpa [Nat.add_assoc] using c2.pc)
      ((c2.regs _ src31).trans ((c1.regs _ src31).trans ((c0.regs _ src31).trans src)))
      (by rw [c2.regs .x21 (by decide), c1.regs .x21 (by decide), c0.regs .x21 (by decide)]; exact dst)
      sa ta apart sf tf
  have ram : MEMORY_BYTES < 2^64 := by decide
  have copy16 : ByteCopy s b S T 16 := copy_extend c0.bytes c1.bytes (by omega) (by omega)
  have copy24 : ByteCopy s c S T 24 := copy_extend copy16 c2.bytes (by omega) (by omega)
  refine ⟨((c0.run.next c1.run).next c2.run).next c3.run, ?_, ?_,
    copy_extend copy24 c3.bytes apart (by omega), ?_⟩
  · change d.pc = _
    simpa [Nat.add_assoc] using c3.pc
  · intro r h
    change d.getReg r = s.getReg r
    rw [c3.regs r h, c2.regs r h, c1.regs r h, c0.regs r h]
  · intro q below
    change d.getMem q = s.getMem q
    rw [c3.below q (by omega), c2.below q (by omega), c1.below q (by omega), c0.below q below]

end Shifted32
end TwoPermutationPrototype.GroupedOpening
