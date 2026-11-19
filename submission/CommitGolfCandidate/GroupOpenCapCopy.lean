import CommitGolfCandidate.GroupOpenWideCopy

/-! Alignment-dispatched 28-byte cap copies, preserving every register except x31. -/

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open PackedOpening (ByteCopy)
open Wide Shifted30
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace CapCopy

def cycles (target : Nat) : Nat :=
  if target % 4 = 0 then (if target % 8 = 0 then 13 else 18) else 26

structure Done (s t : MachineState) (S T n cycles word : Nat) : Prop where
  run : RunsOpeningBlock s t cycles
  pc : t.pc = BitVec.ofNat 64 (4096+4*word)
  regs : ∀ r, r ≠ .x31 → t.getReg r = s.getReg r
  bytes : ByteCopy s t S T n
  below : ∀ q : Word, q.toNat < T-T%8 → t.getMem q = s.getMem q

theorem pairs (s : MachineState) (S T word load width n : Nat)
    (hw : width = 2 ∨ width = 4 ∨ width = 8)
    (code : PairsAt word n width .x7 load load) (bound : word+2*n ≤ 1939)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*word))
    (src : s.getReg .x7 = BitVec.ofNat 64 S) (dst : s.getReg .x21 = BitVec.ofNat 64 T)
    (sa : (S+load)%width=0) (ta : (T+load)%width=0)
    (imm : load+width*n ≤ 2048) (apart : S+load+width*n ≤ T)
    (room : T+load+width*n ≤ MEMORY_BYTES) :
    Done s (pairsRun width .x7 load load 0 n s) (S+load) (T+load) (width*n) (2*n) (word+2*n) := by
  have dr : s.getReg .x21+BitVec.ofNat 64 load = BitVec.ofNat 64 (T+load) := by
    rw [dst, ← BitVec.ofNat_add]
  obtain ⟨run, final, regs, bytes, below⟩ := run_pairs width hw .x7 (by decide)
    word load load S (T+load) sa ta n 0 s (by simpa using code) (by simpa using bound)
      (by simpa using pc) src dr (by simpa only [Nat.zero_add] using imm)
      (by simpa only [Nat.zero_add] using imm) (by simp only [Nat.zero_add]; omega)
      (by simp only [Nat.zero_add]; omega)
  exact ⟨run, by simpa using final, regs, by simpa using bytes, below⟩

private theorem chunks_code : ∀ k : Fin 3,
    CodeAt (1890+6*k.val) (Shifted32.chunkCode .x7 0 (8*k.val)) := by
  unfold CodeAt; decide +kernel

theorem chunk_at (word : Nat) (k : Fin 3) (s : MachineState) (S T : Nat)
    (code : CodeAt (word+6*k.val) (Shifted32.chunkCode .x7 0 (8*k.val)))
    (bound : word+18 ≤ 1939)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*(word+6*k.val)))
    (src : s.getReg .x7 = BitVec.ofNat 64 S) (dst : s.getReg .x21 = BitVec.ofNat 64 T)
    (sa : S%8=0) (ta : T%4=2) (apart : S+28 ≤ T) (room : T+28 ≤ MEMORY_BYTES) :
    Done s (execCode s (Shifted32.chunkCode .x7 0 (8*k.val)))
      (S+8*k.val) (T+8*k.val) 8 6 (word+6*k.val+6) := by
  have hk := k.isLt
  have src' : s.getReg .x7+BitVec.ofNat 64 (8*k.val)=BitVec.ofNat 64 (S+8*k.val) := by
    rw [src, ← BitVec.ofNat_add]
  have dst' : s.getReg .x21+BitVec.ofNat 64 (0+8*k.val)=BitVec.ofNat 64 (T+8*k.val) := by
    rw [dst]; simp only [Nat.zero_add, ← BitVec.ofNat_add]
  have mem := Shifted32.chunk_memory s .x7 0 _ _ _ src' dst' (by omega)
  have run := code_run (Shifted32.chunkCode .x7 0 (8*k.val)) _ s (by simp [Shifted32.chunkCode]; omega)
    code (Shifted32.chunk_ready s _ _ _ _ _ src' dst' (by omega) (by omega) (by omega) (by omega) (by omega)) pc
    (by intro i hi; simp only [Shifted32.chunkCode, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
    (by intro u i hi; simp only [Shifted32.chunkCode, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
  refine ⟨run, ?_, Shifted32.chunk_regs s _ _ _, ?_, ?_⟩
  · rw [Shifted32.chunk_pc, pc, show (24 : Word)=BitVec.ofNat 64 (4*6) from rfl, ofNat_step]
  · exact copy_congr_mem mem (chunk_copy s _ _ false (by omega) (by omega) (by omega)
      (by unfold MEMORY_BYTES at room; omega) (by unfold MEMORY_BYTES at room; omega))
  · intro q low
    rw [getMem_congr mem]
    exact chunk_below s _ _ false q (by unfold MEMORY_BYTES at room; omega) low

theorem chunk (k : Fin 3) (s : MachineState) (S T : Nat)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*(1890+6*k.val)))
    (src : s.getReg .x7 = BitVec.ofNat 64 S) (dst : s.getReg .x21 = BitVec.ofNat 64 T)
    (sa : S%8=0) (ta : T%4=2) (apart : S+28 ≤ T) (room : T+28 ≤ MEMORY_BYTES) :
    Done s (execCode s (Shifted32.chunkCode .x7 0 (8*k.val)))
      (S+8*k.val) (T+8*k.val) 8 6 (1890+6*k.val+6) :=
  chunk_at 1890 k s S T (chunks_code k) (by decide) pc src dst sa ta apart room

theorem append {s t u : MachineState} {S T n m c d word next : Nat}
    (first : Done s t S T n c word) (last : Done t u (S+n) (T+n) m d next)
    (apart : S+n+m ≤ T) (room : T+n+m ≤ MEMORY_BYTES) :
    Done s u S T (n+m) (c+d) next := by
  refine ⟨first.run.next last.run, last.pc, fun r h => (last.regs r h).trans (first.regs r h),
    copy_extend first.bytes last.bytes apart (by unfold MEMORY_BYTES at room; omega), ?_⟩
  intro q low
  rw [last.below q (by omega), first.below q low]

theorem jump {s t : MachineState} {S T n c word : Nat} (copy : Done s t S T n c word)
    (off : BitVec 21) (bound : word<1939) (code : Decodes word (.JAL .x0 off))
    (target : BitVec.ofNat 64 (4096+4*word)+signExtend21 off=BitVec.ofNat 64 (4096+4*698)) :
    Done s (execInstrBr t (.JAL .x0 off)) S T n (c+1) 698 := by
  have mem : (execInstrBr t (.JAL .x0 off)).mem=t.mem := rfl
  refine ⟨copy.run.next (run_step t word _ bound copy.pc code rfl rfl), ?_, ?_,
    copy_congr_mem mem copy.bytes, ?_⟩
  · change t.pc+signExtend21 off=_; rw [copy.pc, target]
  · intro r h
    have same : (execInstrBr t (.JAL .x0 off)).getReg r=t.getReg r := by cases r <;> rfl
    exact same.trans (copy.regs r h)
  · intro q low; exact (getMem_congr mem q).trans (copy.below q low)

theorem word_path (s : MachineState) (S T : Nat)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*684))
    (src : s.getReg .x7=BitVec.ofNat 64 S) (dst : s.getReg .x21=BitVec.ofNat 64 T)
    (sa : S%8=0) (ta : T%4=0) (apart : S+28 ≤ T) (room : T+28 ≤ MEMORY_BYTES) :
    ∃ t, Done s t S T 28 14 698 := by
  have h := pairs s S T 684 0 4 7 (by omega) (by decide +kernel) (by decide) pc src dst
    (by omega) (by omega) (by decide) apart (by omega)
  exact ⟨_, by simpa using h⟩

theorem dword_path (s : MachineState) (S T : Nat)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*674))
    (src : s.getReg .x7=BitVec.ofNat 64 S) (dst : s.getReg .x21=BitVec.ofNat 64 T)
    (sa : S%8=0) (ta : T%8=0) (apart : S+28 ≤ T) (room : T+28 ≤ MEMORY_BYTES) :
    ∃ t, Done s t S T 28 9 698 := by
  have a := pairs s S T 674 0 8 3 (by omega) (by decide +kernel) (by decide) pc src dst
    (by omega) (by omega) (by decide) (by omega) (by omega)
  have b := pairs _ S T 680 24 4 1 (by omega) (by decide +kernel) (by decide) a.pc
    ((a.regs _ (by decide)).trans src) ((a.regs _ (by decide)).trans dst)
    (by omega) (by omega) (by decide) apart (by omega)
  have both := append a b (by omega) (by omega)
  exact ⟨_, by simpa using jump both 64 (by decide) (by decide +kernel) (by decide)⟩

theorem shifted_path (s : MachineState) (S T : Nat)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*1890))
    (src : s.getReg .x7=BitVec.ofNat 64 S) (dst : s.getReg .x21=BitVec.ofNat 64 T)
    (sa : S%8=0) (ta : T%4=2) (apart : S+28 ≤ T) (room : T+28 ≤ MEMORY_BYTES) :
    ∃ t, Done s t S T 28 23 698 := by
  have a := chunk (0 : Fin 3) s S T pc src dst sa ta apart room
  have b := chunk (1 : Fin 3) _ S T a.pc
    ((a.regs _ (by decide)).trans src) ((a.regs _ (by decide)).trans dst) sa ta apart room
  have ab := append a b (by omega) (by omega)
  have c := chunk (2 : Fin 3) _ S T b.pc
    ((ab.regs _ (by decide)).trans src) ((ab.regs _ (by decide)).trans dst) sa ta apart room
  have abc := append ab c (by omega) (by omega)
  have d := pairs _ S T 1908 24 2 2 (by omega) (by decide +kernel) (by decide) c.pc
    ((abc.regs _ (by decide)).trans src) ((abc.regs _ (by decide)).trans dst)
    (by omega) (by omega) (by decide) apart (by omega)
  have both := append abc d (by omega) (by omega)
  exact ⟨_, by simpa using jump both 2092296 (by decide) (by decide +kernel) (by decide)⟩

theorem before {s e t : MachineState} {S T n c d word : Nat}
    (run : RunsOpeningBlock s e c) (regs : ∀ r, r ≠ .x31 → e.getReg r=s.getReg r)
    (mem : e.mem=s.mem) (copy : Done e t S T n d word) : Done s t S T n (c+d) word := by
  refine ⟨run.next copy.run, copy.pc, fun r h => (copy.regs r h).trans (regs r h),
    copy_congr_before mem.symm copy.bytes, ?_⟩
  intro q low; exact (copy.below q low).trans (getMem_congr mem q)

theorem test (s : MachineState) (T word modulus : Nat) (mask : BitVec 12) (off : BitVec 13)
    (bound : word+1<1939) (pc : s.pc=BitVec.ofNat 64 (4096+4*word))
    (code1 : Decodes word (.ANDI .x31 .x21 mask))
    (code2 : Decodes (word+1) (.BNE .x31 .x0 off))
    (small : 0<modulus ∧ modulus ≤ 8) (bits : s.getReg .x21 &&& signExtend12 mask=BitVec.ofNat 64 (T%modulus)) :
    ∃ e, RunsOpeningBlock s e 2 ∧
      e.pc=(if T%modulus=0 then BitVec.ofNat 64 (4096+4*(word+2))
        else BitVec.ofNat 64 (4096+4*(word+1))+signExtend13 off) ∧
      (∀ r, r ≠ .x31 → e.getReg r=s.getReg r) ∧ e.mem=s.mem := by
  let a := execInstrBr s (.ANDI .x31 .x21 mask)
  let b := execInstrBr a (.BNE .x31 .x0 off)
  obtain ⟨pa, va, ma⟩ := andi_facts s mask
  have pca : a.pc=BitVec.ofNat 64 (4096+4*(word+1)) := by rw [pa, pc, ofNat_four]
  have run1 := run_step s word _ (by omega) pc code1 rfl rfl
  have run2 := run_step a (word+1) _ bound pca code2 rfl rfl
  obtain ⟨pb, mb⟩ := bne_facts a off
  have regb (r : Reg) : b.getReg r=a.getReg r := by simp only [b, execInstrBr]; split <;> rfl
  refine ⟨b, run1.next run2, ?_, fun r h => (regb r).trans (ma.regs r h), mb.mem.trans ma.mem⟩
  rw [pb, va, bits, pca]
  by_cases zero : T%modulus=0
  · simp only [zero, ite_true]
    rw [ofNat_four]
  · have ne : BitVec.ofNat 64 (T%modulus) ≠ (0#64) := by
      intro eq
      have h := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat] at h
      have := Nat.mod_lt T small.1
      omega
    simp only [ne, if_false, zero]

theorem mask_bits (s : MachineState) (T mask : Nat) (hmask : mask=3 ∨ mask=7)
    (dst : s.getReg .x21=BitVec.ofNat 64 T) (fit : T<2^64) :
    s.getReg .x21 &&& signExtend12 (BitVec.ofNat 12 mask)=BitVec.ofNat 64 (T%(mask+1)) := by
  rcases hmask with rfl|rfl <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [dst, show signExtend12 (BitVec.ofNat 12 3)=(3#64 : Word) from rfl,
      show signExtend12 (BitVec.ofNat 12 7)=(7#64 : Word) from rfl,
      BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit,
      show 3%2^64=3 from rfl, show 7%2^64=7 from rfl] <;>
    first
    | rw [show (3:Nat)=2^2-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
    | rw [show (7:Nat)=2^3-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

/-- The three paths reach the unchanged final digest halfword with identical copied bytes. -/
theorem copy (s : MachineState) (S T : Nat) (pc : s.pc=BitVec.ofNat 64 (4096+4*670))
    (src : s.getReg .x7=BitVec.ofNat 64 S) (dst : s.getReg .x21=BitVec.ofNat 64 T)
    (sa : S%8=0) (ta : T%2=0) (apart : S+28 ≤ T) (room : T+28 ≤ MEMORY_BYTES) :
    ∃ t, Done s t S T 28 (cycles T) 698 := by
  have fit : T<2^64 := by unfold MEMORY_BYTES at room; omega
  obtain ⟨a, ra, pa, ga, ma⟩ := test s T 670 4 3 48 (by decide) pc (by decide +kernel)
    (by decide +kernel) (by decide) (mask_bits s T 3 (by simp) dst fit)
  by_cases four : T%4=0
  · have pca : a.pc=BitVec.ofNat 64 (4096+4*672) := by simpa [four] using pa
    obtain ⟨b, rb, pb, gb, mb⟩ := test a T 672 8 7 44 (by decide) pca (by decide +kernel)
      (by decide +kernel) (by decide) (mask_bits a T 7 (by simp) ((ga _ (by decide)).trans dst) fit)
    by_cases eight : T%8=0
    · obtain ⟨t, body⟩ := dword_path b S T (by simpa [eight] using pb)
        ((gb _ (by decide)).trans ((ga _ (by decide)).trans src))
        ((gb _ (by decide)).trans ((ga _ (by decide)).trans dst)) sa eight apart room
      exact ⟨t, by simpa [cycles, four, eight] using before ra ga ma (before rb gb mb body)⟩
    · obtain ⟨t, body⟩ := word_path b S T (by rw [if_neg eight] at pb; exact pb.trans (by decide))
        ((gb _ (by decide)).trans ((ga _ (by decide)).trans src))
        ((gb _ (by decide)).trans ((ga _ (by decide)).trans dst)) sa four apart room
      exact ⟨t, by simpa [cycles, four, eight] using before ra ga ma (before rb gb mb body)⟩
  · have pca : a.pc=BitVec.ofNat 64 (4096+4*683) := by rw [if_neg four] at pa; exact pa.trans (by decide)
    let b := execInstrBr a (.JAL .x0 4828)
    have rb := run_step a 683 (.JAL .x0 4828) (by decide) pca (by decide +kernel) rfl rfl
    have pcb : b.pc=BitVec.ofNat 64 (4096+4*1890) := by
      change a.pc+signExtend21 4828=_; rw [pca]; decide
    have gb (r : Reg) (_ : r ≠ .x31) : b.getReg r=a.getReg r := by cases r <;> rfl
    have mb : b.mem=a.mem := rfl
    obtain ⟨t, body⟩ := shifted_path b S T pcb
      ((gb _ (by decide)).trans ((ga _ (by decide)).trans src))
      ((gb _ (by decide)).trans ((ga _ (by decide)).trans dst)) sa (by omega) apart room
    exact ⟨t, by simpa [cycles, four] using before ra ga ma (before rb gb mb body)⟩

end CapCopy
end TwoPermutationPrototype.GroupedOpening
