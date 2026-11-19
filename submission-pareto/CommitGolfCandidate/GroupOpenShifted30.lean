import CommitGolfCandidate.GroupOpenWideCopyCore

/-! Aligned loads with shifted halfword/word stores for the 2-mod-4 30-byte copy path.
The final load contributes only six bytes; its unused high bytes never enter the copy contract. -/

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open PackedOpening (ByteCopy)

namespace Shifted30

def chunkCode (offset : Nat) (last : Bool) : List Instr :=
  [.LD .x31 .x7 (BitVec.ofNat 12 offset), .SH .x21 .x31 (BitVec.ofNat 12 offset),
   .SRLI .x31 .x31 16, .SW .x21 .x31 (BitVec.ofNat 12 (offset+2))] ++
  if last then [] else [.SRLI .x31 .x31 32, .SH .x21 .x31 (BitVec.ofNat 12 (offset+6))]

def execCode (s : MachineState) (code : List Instr) : MachineState :=
  code.foldl execInstrBr s

theorem slice_byte (d : Word) (offset width i : Nat) (inside : i < width)
    (_fits : offset + width ≤ 8) :
    (((d >>> (8*offset)).truncate (8*width)) >>> (8*i)).truncate 8 =
      extractByte d (offset+i) := by
  unfold extractByte
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    show 8*i+j < 8*width by omega,
    show 8*offset+(8*i+j) = (offset+i)*8+j by omega]

theorem half_slice (s : MachineState) (S T offset : Nat)
    (sa : S % 8 = 0) (ta : T % 2 = 0) (part : offset+2 ≤ 8)
    (sf : S+8 ≤ 2^64) (tf : T+2 ≤ 2^64) :
    ByteCopy s (s.setHalfword (BitVec.ofNat 64 T)
      ((s.getMem (BitVec.ofNat 64 S) >>> (8*offset)).truncate 16)) (S+offset) T 2 := by
  have offT := Wide.offset_nat T (by omega)
  have alignT := Wide.align_eq T (by omega)
  constructor
  · intro i hi
    have alignTi : alignToDword (BitVec.ofNat 64 (T+i)) = alignToDword (BitVec.ofNat 64 T) := by
      rw [Wide.align_eq (T+i) (by omega), alignT]
      congr 1
      omega
    rw [ProjectedHalfword.store_byte, ite_eq_left ⟨alignTi, by rw [Wide.offset_nat (T+i) (by omega), offT]; omega⟩,
      Wide.offset_nat (T+i) (by omega), show (T+i)%8%2*8 = 8*i by omega]
    rw [slice_byte _ offset 2 i hi part]
    simpa only [Nat.add_assoc] using (Wide.byte_at s S (offset+i) sa (by omega) sf).symm
  · intro q outside
    rw [ProjectedHalfword.store_byte]
    by_cases hit : alignToDword q = alignToDword (BitVec.ofNat 64 T) ∧
        byteOffset q / 2 = byteOffset (BitVec.ofNat 64 T) / 2
    · exfalso
      rw [offT] at hit
      have back := Wide.of_align q (T-T%8) (by rw [hit.1, alignT])
      have ob := @byteOffset_lt_8 q
      apply outside (byteOffset q-T%8) (by omega)
      exact back.trans (congrArg (BitVec.ofNat 64) (by omega))
    · rw [ite_eq_right hit]

theorem word_slice (s : MachineState) (S T offset : Nat)
    (sa : S % 8 = 0) (ta : T % 4 = 0) (part : offset+4 ≤ 8)
    (sf : S+8 ≤ 2^64) (tf : T+4 ≤ 2^64) :
    ByteCopy s (s.setWord32 (BitVec.ofNat 64 T)
      ((s.getMem (BitVec.ofNat 64 S) >>> (8*offset)).truncate 32)) (S+offset) T 4 := by
  have offT := Wide.offset_nat T (by omega)
  have alignT := Wide.align_eq T (by omega)
  have pos : byteOffset (BitVec.ofNat 64 T) / 4 < 2 := by rw [offT]; omega
  constructor
  · intro i hi
    have alignTi : alignToDword (BitVec.ofNat 64 (T+i)) = alignToDword (BitVec.ofNat 64 T) := by
      rw [Wide.align_eq (T+i) (by omega), alignT]
      congr 1
      omega
    unfold MachineState.getByte MachineState.setWord32
    dsimp only
    rw [alignTi, MachineState.getMem_setMem_eq, Wide.offset_nat (T+i) (by omega),
      Wide.replace_word_byte _ _ _ _ pos (by omega), offT, ite_eq_left (by omega),
      show 8*((T+i)%8-4*(T%8/4)) = 8*i by omega]
    rw [slice_byte _ offset 4 i hi part]
    simpa only [MachineState.getByte, Nat.add_assoc] using (Wide.byte_at s S (offset+i) sa (by omega) sf).symm
  · intro q outside
    unfold MachineState.getByte MachineState.setWord32
    dsimp only
    by_cases same : alignToDword q = alignToDword (BitVec.ofNat 64 T)
    · rw [same, MachineState.getMem_setMem_eq, Wide.replace_word_byte _ _ _ _ pos byteOffset_lt_8]
      by_cases hit : 4*(byteOffset (BitVec.ofNat 64 T)/4) ≤ byteOffset q ∧
          byteOffset q < 4*(byteOffset (BitVec.ofNat 64 T)/4)+4
      · exfalso
        rw [offT] at hit
        have back := Wide.of_align q (T-T%8) (by rw [same, alignT])
        apply outside (byteOffset q-T%8) (by omega)
        exact back.trans (congrArg (BitVec.ofNat 64) (by omega))
      · rw [ite_eq_right hit]
    · rw [MachineState.getMem_setMem_ne same]

def chunkMemory (s : MachineState) (S T : Nat) (last : Bool) : MachineState :=
  let d := s.getMem (BitVec.ofNat 64 S)
  let a := s.setHalfword (BitVec.ofNat 64 T) (d.truncate 16)
  let b := a.setWord32 (BitVec.ofNat 64 (T+2)) ((d >>> 16).truncate 32)
  if last then b else b.setHalfword (BitVec.ofNat 64 (T+6)) ((d >>> 48).truncate 16)

theorem half_below (s : MachineState) (T : Nat) (v : BitVec 16) (q : Word)
    (fit : T < 2^64) (below : q.toNat < T-T%8) :
    (s.setHalfword (BitVec.ofNat 64 T) v).getMem q = s.getMem q := by
  unfold MachineState.setHalfword
  apply MachineState.getMem_setMem_ne
  intro same
  have h := congrArg BitVec.toNat same
  rw [Wide.align_nat T fit] at h
  omega

theorem word_below (s : MachineState) (T : Nat) (v : BitVec 32) (q : Word)
    (fit : T < 2^64) (below : q.toNat < T-T%8) :
    (s.setWord32 (BitVec.ofNat 64 T) v).getMem q = s.getMem q := by
  unfold MachineState.setWord32
  apply MachineState.getMem_setMem_ne
  intro same
  have h := congrArg BitVec.toNat same
  rw [Wide.align_nat T fit] at h
  omega

theorem chunk_copy (s : MachineState) (S T : Nat) (last : Bool)
    (sa : S % 8 = 0) (ta : T % 4 = 2) (apart : S+8 ≤ T)
    (sf : S+8 ≤ 2^64) (tf : T+8 ≤ 2^64) :
    ByteCopy s (chunkMemory s S T last) S T (if last then 6 else 8) := by
  let d := s.getMem (BitVec.ofNat 64 S)
  let a := s.setHalfword (BitVec.ofNat 64 T) (d.truncate 16)
  let b := a.setWord32 (BitVec.ofNat 64 (T+2)) ((d >>> 16).truncate 32)
  have small : (BitVec.ofNat 64 S).toNat = S := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have am : a.getMem (BitVec.ofNat 64 S) = d := half_below s T _ _ (by omega) (by rw [small]; omega)
  have bm : b.getMem (BitVec.ofNat 64 S) = d := by
    rw [show b = a.setWord32 (BitVec.ofNat 64 (T+2)) ((d >>> 16).truncate 32) from rfl,
      word_below a (T+2) _ _ (by omega) (by rw [small]; omega), am]
  have c1 : ByteCopy s a S T 2 := by
    simpa only [a, d, Nat.mul_zero, BitVec.ushiftRight_zero, Nat.add_zero] using
      half_slice s S T 0 sa (by omega) (by omega) sf (by omega)
  have c2 : ByteCopy a b (S+2) (T+2) 4 := by
    simpa only [b, am, show 8*2 = 16 from rfl] using
      word_slice a S (T+2) 2 sa (by omega) (by omega) sf (by omega)
  have c12 : ByteCopy s b S T 6 := copy_extend c1 c2 (by omega) (by omega)
  cases last
  · have c3 : ByteCopy b (b.setHalfword (BitVec.ofNat 64 (T+6)) ((d >>> 48).truncate 16)) (S+6) (T+6) 2 := by
      simpa only [bm, show 8*6 = 48 from rfl] using
        half_slice b S (T+6) 6 sa (by omega) (by omega) sf tf
    exact copy_extend c12 c3 apart tf
  · exact c12

theorem shift_twice (d : Word) : (d >>> 16) >>> 32 = d >>> 48 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight]

theorem mem_pc (s : MachineState) (v : Word) : (s.setPC v).mem = s.mem := rfl

theorem mem_reg (s : MachineState) (v : Word) : (s.setReg .x31 v).mem = s.mem := rfl

theorem chunk_memory (s : MachineState) (S T offset : Nat) (last : Bool)
    (src : s.getReg .x7 + BitVec.ofNat 64 offset = BitVec.ofNat 64 S)
    (dst : s.getReg .x21 + BitVec.ofNat 64 offset = BitVec.ofNat 64 T)
    (small : offset+6 < 2048) :
    (execCode s (chunkCode offset last)).mem = (chunkMemory s S T last).mem := by
  have addr (k : Nat) (h : k ≤ 6) :
      s.getReg .x21 + signExtend12 (BitVec.ofNat 12 (offset+k)) = BitVec.ofNat 64 (T+k) := by
    rw [sign12 _ (by omega), BitVec.ofNat_add, ← BitVec.add_assoc, dst, ← BitVec.ofNat_add]
  have source : s.getReg .x7 + signExtend12 (BitVec.ofNat 12 offset) = BitVec.ofNat 64 S := by
    rw [sign12 _ (by omega), src]
  have dst0 : s.getReg .x21 + signExtend12 (BitVec.ofNat 12 offset) = BitVec.ofNat 64 T := by
    simpa using addr 0 (by omega)
  cases last <;>
    simp only [execCode, chunkCode, chunkMemory, Bool.false_eq_true, ite_false, ite_true,
      List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0),
      MachineState.getReg_setReg_ne _ .x31 .x21 _ (by decide),
      MachineState.getReg_setReg_ne _ .x31 .x7 _ (by decide),
      reg_setHalfword, reg_setWord32, source, dst0, addr 2 (by omega), addr 6 (by omega),
      show (16#6).toNat = 16 from rfl, show (32#6).toNat = 32 from rfl, shift_twice, mem_pc] <;>
    simp only [MachineState.setHalfword, MachineState.setWord32, MachineState.setMem,
      MachineState.getMem, mem_pc, mem_reg] <;>
    rfl

def Ready : MachineState → List Instr → Prop
  | _, [] => True
  | s, i::is => memoryArgumentsValid s i = true ∧ Ready (execInstrBr s i) is

def CodeAt (word : Nat) (code : List Instr) : Prop :=
  ∀ j : Fin code.length, Decodes (word+j.val) code[j]

theorem code_run (code : List Instr) : ∀ (word : Nat) (s : MachineState),
    word+code.length ≤ 1890 → CodeAt word code → Ready s code →
    s.pc = BitVec.ofNat 64 (4096+4*word) →
    (∀ i ∈ code, stepKind i = true) →
    (∀ u i, i ∈ code → (execInstrBr u i).pc = u.pc+4) →
    RunsOpeningBlock s (execCode s code) code.length := by
  induction code with
  | nil => intro word s _ _ _ _ _ _; exact run_zero s
  | cons i is ih =>
    intro word s bound dec ready pc kind nextpc
    have first := run_step s word i (by simp only [List.length_cons] at bound; omega) pc
      (dec ⟨0, by simp⟩) (kind i (by simp)) ready.1
    have tail := ih (word+1) (execInstrBr s i) (by simp only [List.length_cons] at bound; omega)
      (fun j => by simpa [CodeAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dec ⟨j.val+1, by simpa using j.isLt⟩)
      ready.2 (by rw [nextpc s i (by simp), pc, ofNat_four])
      (fun a h => kind a (by simp [h])) (fun u a h => nextpc u a (by simp [h]))
    simpa [execCode, List.foldl, Nat.add_comm] using first.next tail

theorem chunk_regs (s : MachineState) (offset : Nat) (last : Bool) (r : Reg) (h : r ≠ .x31) :
    (execCode s (chunkCode offset last)).getReg r = s.getReg r := by
  cases last <;> simp [execCode, chunkCode, execInstrBr,
    MachineState.getReg_setReg_ne _ .x31 r _ (Ne.symm h), reg_setHalfword, reg_setWord32]

theorem chunk_pc (s : MachineState) (offset : Nat) (last : Bool) :
    (execCode s (chunkCode offset last)).pc = s.pc+BitVec.ofNat 64 (4*(chunkCode offset last).length) := by
  cases last <;> simp [execCode, chunkCode, execInstrBr, MachineState.setPC, BitVec.add_assoc]

theorem chunk_ready (s : MachineState) (S T offset : Nat) (last : Bool)
    (src : s.getReg .x7 + BitVec.ofNat 64 offset = BitVec.ofNat 64 S)
    (dst : s.getReg .x21 + BitVec.ofNat 64 offset = BitVec.ofNat 64 T)
    (sa : S % 8 = 0) (ta : T % 4 = 2) (sf : S+8 ≤ MEMORY_BYTES)
    (tf : T+(if last then 6 else 8) ≤ MEMORY_BYTES)
    (small : offset+6 < 2048) : Ready s (chunkCode offset last) := by
  have addr (k : Nat) (h : k ≤ 6) :
      s.getReg .x21 + signExtend12 (BitVec.ofNat 12 (offset+k)) = BitVec.ofNat 64 (T+k) := by
    rw [sign12 _ (by omega), BitVec.ofNat_add, ← BitVec.add_assoc, dst, ← BitVec.ofNat_add]
  have dst0 : s.getReg .x21 + signExtend12 (BitVec.ofNat 12 offset) = BitVec.ofNat 64 T := by simpa using addr 0 (by omega)
  have source : s.getReg .x7 + signExtend12 (BitVec.ofNat 12 offset) = BitVec.ofNat 64 S := by rw [sign12 _ (by omega), src]
  have v0 := access_ok S 8 sa sf
  have six : T+6 ≤ MEMORY_BYTES := by cases last <;> simp_all <;> omega
  have v1 := access_ok T 2 (by omega) (by omega : T+2 ≤ MEMORY_BYTES)
  have v2 := access_ok (T+2) 4 (by omega) (by omega : T+2+4 ≤ MEMORY_BYTES)
  have v3 : last=false → accessValid (BitVec.ofNat 64 (T+6)) 2 = true := by
    intro h; rw [h] at tf
    exact access_ok (T+6) 2 (by omega) (by simpa [Nat.add_assoc] using tf)
  cases last <;>
    simp only [chunkCode, Bool.false_eq_true, ite_false, ite_true, List.cons_append, List.nil_append,
      Ready, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0),
      MachineState.getReg_setReg_ne _ .x31 .x21 _ (by decide), reg_setHalfword, reg_setWord32,
      source, dst0, addr 2 (by omega), addr 6 (by omega), v0, v1, v2, v3, and_self]

theorem chunk_below (s : MachineState) (S T : Nat) (last : Bool) (q : Word)
    (fit : T+8 ≤ 2^64) (below : q.toNat < T-T%8) :
    (chunkMemory s S T last).getMem q = s.getMem q := by
  cases last <;>
    simp only [chunkMemory, Bool.false_eq_true, ite_false, ite_true] <;>
    repeat' first
      | rw [half_below _ _ _ q (by omega) (by omega)]
      | rw [word_below _ _ _ q (by omega) (by omega)]

theorem chunk_decoded : ∀ k : Fin 4,
    CodeAt (1867+6*k.val) (chunkCode (8*k.val) (decide (k.val=3))) := by
  unfold CodeAt
  decide +kernel

structure ChunkDone (s t : MachineState) (S T word size : Nat) : Prop where
  run : RunsOpeningBlock s t (if size=6 then 4 else 6)
  pc : t.pc = BitVec.ofNat 64 (4096+4*(word+(if size=6 then 4 else 6)))
  regs : ∀ r, r ≠ .x31 → t.getReg r = s.getReg r
  bytes : ByteCopy s t S T size
  below : ∀ q : Word, q.toNat < T-T%8 → t.getMem q = s.getMem q

theorem chunk_done (k : Fin 4) (s : MachineState) (S T : Nat)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*(1867+6*k.val)))
    (src : s.getReg .x7 = BitVec.ofNat 64 S) (dst : s.getReg .x21 = BitVec.ofNat 64 T)
    (sa : S % 8 = 0) (ta : T % 4 = 2) (apart : S+30 ≤ T)
    (sf : S+32 ≤ MEMORY_BYTES) (tf : T+30 ≤ MEMORY_BYTES) :
    ChunkDone s (execCode s (chunkCode (8*k.val) (decide (k.val=3))))
      (S+8*k.val) (T+8*k.val) (1867+6*k.val) (if k.val=3 then 6 else 8) := by
  have hk := k.isLt
  have ram : MEMORY_BYTES < 2^64 := by decide
  let last := decide (k.val=3)
  let code := chunkCode (8*k.val) last
  have len : code.length = if k.val=3 then 4 else 6 := by
    dsimp [code, last]; split <;> simp_all [chunkCode]
  have sr : s.getReg .x7 + BitVec.ofNat 64 (8*k.val) = BitVec.ofNat 64 (S+8*k.val) := by rw [src, ← BitVec.ofNat_add]
  have dr : s.getReg .x21 + BitVec.ofNat 64 (8*k.val) = BitVec.ofNat 64 (T+8*k.val) := by rw [dst, ← BitVec.ofNat_add]
  have ready := chunk_ready s (S+8*k.val) (T+8*k.val) (8*k.val) last sr dr
    (by omega) (by omega) (by omega) (by dsimp [last]; split <;> simp_all <;> omega) (by omega)
  have kind : ∀ i ∈ code, stepKind i = true := by
    intro i h; cases hlast : last <;> simp [code, hlast, chunkCode] at h <;>
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have nextpc : ∀ u i, i ∈ code → (execInstrBr u i).pc = u.pc+4 := by
    intro u i h; cases hlast : last <;> simp [code, hlast, chunkCode] at h <;>
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have run := code_run code (1867+6*k.val) s (by rw [len]; split <;> omega)
    (chunk_decoded k) ready pc kind nextpc
  rw [len] at run
  have mem := chunk_memory s (S+8*k.val) (T+8*k.val) (8*k.val) last sr dr (by omega)
  have copy := copy_congr_mem mem (chunk_copy s (S+8*k.val) (T+8*k.val) last
    (by omega) (by omega) (by omega) (by omega) (by omega))
  refine ⟨?_, ?_, chunk_regs s _ last, ?_, ?_⟩
  · by_cases h : k.val=3 <;> simpa [len, code, last, h] using run
  · rw [chunk_pc, pc, ← BitVec.ofNat_add, len]
    by_cases h : k.val=3 <;> simp [h]
    all_goals congr 1 <;> omega
  · simpa [last] using copy
  · intro q below
    have eqmem : (execCode s (chunkCode (8*k.val) last)).getMem q =
        (chunkMemory s (S+8*k.val) (T+8*k.val) last).getMem q := by unfold MachineState.getMem; rw [mem]
    rw [eqmem]
    exact chunk_below s _ _ last q (by omega) below

def copy30 (s : MachineState) : MachineState :=
  execCode (execCode (execCode (execCode s (chunkCode 0 false))
    (chunkCode 8 false)) (chunkCode 16 false)) (chunkCode 24 true)

structure CopyDone (s t : MachineState) (S T : Nat) : Prop where
  run : RunsOpeningBlock s t 22
  pc : t.pc = BitVec.ofNat 64 (4096+4*1889)
  regs : ∀ r, r ≠ .x31 → t.getReg r = s.getReg r
  bytes : ByteCopy s t S T 30
  below : ∀ q : Word, q.toNat < T-T%8 → t.getMem q = s.getMem q

theorem copy30_done (s : MachineState) (S T : Nat)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*1867))
    (src : s.getReg .x7 = BitVec.ofNat 64 S) (dst : s.getReg .x21 = BitVec.ofNat 64 T)
    (sa : S % 8 = 0) (ta : T % 4 = 2) (apart : S+30 ≤ T)
    (sf : S+32 ≤ MEMORY_BYTES) (tf : T+30 ≤ MEMORY_BYTES) :
    CopyDone s (copy30 s) S T := by
  let a := execCode s (chunkCode 0 false)
  let b := execCode a (chunkCode 8 false)
  let c := execCode b (chunkCode 16 false)
  let d := execCode c (chunkCode 24 true)
  have c0 : ChunkDone s a S T 1867 8 := by
    simpa using chunk_done (0 : Fin 4) s S T pc src dst sa ta apart sf tf
  have c1 : ChunkDone a b (S+8) (T+8) 1873 8 := by
    simpa using chunk_done (1 : Fin 4) a S T c0.pc
      ((c0.regs .x7 (by decide)).trans src) ((c0.regs .x21 (by decide)).trans dst) sa ta apart sf tf
  have c2 : ChunkDone b c (S+16) (T+16) 1879 8 := by
    simpa using chunk_done (2 : Fin 4) b S T c1.pc
      ((c1.regs .x7 (by decide)).trans ((c0.regs .x7 (by decide)).trans src))
      ((c1.regs .x21 (by decide)).trans ((c0.regs .x21 (by decide)).trans dst)) sa ta apart sf tf
  have c3 : ChunkDone c d (S+24) (T+24) 1885 6 := by
    simpa using chunk_done (3 : Fin 4) c S T c2.pc
      ((c2.regs .x7 (by decide)).trans ((c1.regs .x7 (by decide)).trans ((c0.regs .x7 (by decide)).trans src)))
      ((c2.regs .x21 (by decide)).trans ((c1.regs .x21 (by decide)).trans ((c0.regs .x21 (by decide)).trans dst)))
      sa ta apart sf tf
  have ram : MEMORY_BYTES < 2^64 := by decide
  have copy16 : ByteCopy s b S T 16 := copy_extend c0.bytes c1.bytes (by omega) (by omega)
  have copy24 : ByteCopy s c S T 24 := copy_extend copy16 c2.bytes (by omega) (by omega)
  refine ⟨((c0.run.next c1.run).next c2.run).next c3.run, c3.pc, ?_,
    copy_extend copy24 c3.bytes apart (by omega), ?_⟩
  · intro r h
    change d.getReg r = s.getReg r
    rw [c3.regs r h, c2.regs r h, c1.regs r h, c0.regs r h]
  · intro q below
    change d.getMem q = s.getMem q
    rw [c3.below q (by omega), c2.below q (by omega), c1.below q (by omega), c0.below q below]

theorem copy30_regs (s : MachineState) (r : Reg) (h : r ≠ .x31) :
    (copy30 s).getReg r = s.getReg r := by
  unfold copy30
  rw [chunk_regs _ _ _ r h, chunk_regs _ _ _ r h, chunk_regs _ _ _ r h, chunk_regs _ _ _ r h]

end Shifted30
end TwoPermutationPrototype.GroupedOpening
