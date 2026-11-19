import CommitGolfCandidate.K3C4CapMask
import CommitGolfCandidate.K3T238PackDecode
import CommitGolfCandidate.TwoPermutationPackedCopy
import CommitGolfCandidate.TwoPermutationPackedCapBytes

/-! # The last node of a packed cap frontier group (T238)

After the eighth-node guard (word 634, `x21` at the node's 28 bytes, `x7` at its heap slot): copy 28 bytes
(`lhu x31,2j(x21); sh x31,2j(x7)`, 634..661), gather the node's top 14 bits from bits 238..239 of the group's
seven 30-byte slots (662..687, base `x21`, scratch `x28`), `sw x31,28(x7)` (688), `addi x21,x21,28` (689),
`addi x30,x0,7` (690), `jal <330>` (691). The slot then holds `packedNodeAt` of the group's block, node 7. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Packed TwoPermutationPrototype.Sampling
open CommitGolfCandidate.ShortTree CommitGolfCandidate.ProjectedHalfword

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-- The 14 halfword copies at 634..661. -/
def eighthCode : CopyCode where
  image := packedImage
  start := 634
  count := 14
  source := .x21
  dest := .x7
  destOffset := 0
  sourceTemp := by decide
  destTemp := by decide
  offsetBound := by decide
  load := fun j hj s pc => cap_fetch s (634+2*j) _ (by omega) pc (by interval_cases j <;> rfl)
  store := fun j hj s pc => cap_fetch s (634+2*j+1) _ (by omega) pc (by interval_cases j <;> rfl)

/-- The gather at 662..687 (base `x21`, scratch `x28`). -/
def eighthGather (s : MachineState) : MachineState :=
  chunkAfter (chunkAfter (chunkAfter (chunkAfter (chunkAfter (chunkAfter (gatherStart s .x21)
    .x21 .x28 1) .x21 .x28 2) .x21 .x28 3) .x21 .x28 4) .x21 .x28 5) .x21 .x28 6

/-- `sw x31,28(x7); addi x21,x21,28; addi x30,x0,7; jal <330>` at 688..691. -/
def eighthTail (s : MachineState) : MachineState :=
  (execInstrBr (execInstrBr (execInstrBr s (.SW .x7 .x31 28)) (.ADDI .x21 .x21 28)) (.ADDI .x30 .x0 7)).setPC 0x1528

def eighthRead (s : MachineState) : MachineState := eighthTail (eighthGather (copyField eighthCode s))

/-! ### Registers and memory of the pieces -/

private theorem chunk_register (s : MachineState) (base tmp : Reg) (j : Nat) (q : Reg)
    (a : q ≠ .x31) (b : q ≠ tmp) : (chunkAfter s base tmp j).getReg q = s.getReg q := by
  simp only [chunkAfter, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b)]

private theorem start_register (s : MachineState) (base : Reg) (q : Reg) (a : q ≠ .x31) :
    (gatherStart s base).getReg q = s.getReg q := by
  simp only [gatherStart, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a)]

private theorem chunk_mem (s : MachineState) (base tmp : Reg) (j : Nat) (a : Word) :
    (chunkAfter s base tmp j).getMem a = s.getMem a := by
  simp only [chunkAfter, execInstrBr, arm_getMem_set_pc, arm_getMem_set_reg]

private theorem start_mem (s : MachineState) (base : Reg) (a : Word) : (gatherStart s base).getMem a = s.getMem a := by
  simp only [gatherStart, execInstrBr, arm_getMem_set_pc, arm_getMem_set_reg]

theorem eighth_gather_register (s : MachineState) (q : Reg) (a : q ≠ .x31) (b : q ≠ .x28) :
    (eighthGather s).getReg q = s.getReg q := by
  unfold eighthGather
  rw [chunk_register _ _ _ _ _ a b, chunk_register _ _ _ _ _ a b, chunk_register _ _ _ _ _ a b,
    chunk_register _ _ _ _ _ a b, chunk_register _ _ _ _ _ a b, chunk_register _ _ _ _ _ a b, start_register _ _ _ a]

theorem eighth_gather_mem (s : MachineState) (a : Word) : (eighthGather s).getMem a = s.getMem a := by
  unfold eighthGather
  rw [chunk_mem, chunk_mem, chunk_mem, chunk_mem, chunk_mem, chunk_mem, start_mem]

private theorem tail_register (s : MachineState) (q : Reg) (a : q ≠ .x21) (b : q ≠ .x30) :
    (eighthTail s).getReg q = s.getReg q := by
  simp only [eighthTail, execInstrBr, MachineState.setWord32, MachineState.getReg_setPC, arm_getReg_set_mem,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a), MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b)]

theorem eighth_read_register (s : MachineState) (r : Reg) (a : r ≠ .x21) (b : r ≠ .x28) (c : r ≠ .x30)
    (d : r ≠ .x31) : (eighthRead s).getReg r = s.getReg r := by
  unfold eighthRead
  rw [tail_register _ _ a c, eighth_gather_register _ _ d b, copy_field_register _ _ _ d]

/-! ### Bit-vector facts -/

private theorem replace_word_high (d : Word) (v : BitVec 32) : replaceWord32 d 1 v = v ++ d.extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp [replaceWord32]

private theorem split_dwords (x : BitVec 256) :
    ((x.extractLsb' 192 64 ++ x.extractLsb' 128 64) ++ x.extractLsb' 64 64) ++ x.extractLsb' 0 64 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases a : i < 64
  · simp [a]
  · by_cases b : i - 64 < 64
    · simp [a, b, show 64 + (i - 64) = i by omega]
    · by_cases c : i - 64 - 64 < 64
      · simp [a, b, c, show 128 + (i - 64 - 64) = i by omega]
      · simp [a, b, c, show 192 + (i - 64 - 64 - 64) = i by omega, show i - 64 - 64 - 64 < 64 by omega]

private theorem node_low (t : BitVec 14) (R : BitVec 224) (o : Nat) (fits : o+64 ≤ 224) :
    ((0 : BitVec 18) ++ (t ++ R)).extractLsb' o 64 = R.extractLsb' o 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show o+i < 238 by omega, show o+i < 224 by omega, ite_true]

private theorem node_high (t : BitVec 14) (R : BitVec 224) :
    ((0 : BitVec 18) ++ (t ++ R)).extractLsb' 192 64 = t.zeroExtend 32 ++ R.extractLsb' 192 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

private theorem truncate_widen (t : BitVec 14) : (t.zeroExtend 64).truncate 32 = t.zeroExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.getLsbD_setWidth]
  by_cases small : i < 14 <;> simp [small, hi, show i < 64 by omega]

/-- A doubleword whose first `m` bytes were copied from `src`. -/
private theorem dword_from_bytes (t s : MachineState) (dst src m : Nat) (aligned : dst % 8 = 0) (small : m ≤ 8)
    (bytes : ∀ i < m, t.getByte (BitVec.ofNat 64 (dst+i)) = s.getByte (BitVec.ofNat 64 (src+i))) :
    (t.getMem (BitVec.ofNat 64 dst)).extractLsb' 0 (8*m) = readBuffer s src m := by
  have w := TwoPermutationPrototype.Checker.read_word t (dst/8)
  have e : 8*(dst/8) = dst := by omega
  rw [e] at w
  have g : t.getMem (BitVec.ofNat 64 dst) = readBuffer t dst 8 := by
    rw [w]
    unfold memoryView wordAddress
    rw [e]
  have sl := read_buffer_slice t dst 8 0 m (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at sl
  rw [g, sl]
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [bytes i (Finset.mem_range.mp hi)]

private theorem spare_half_mem {s t : MachineState} (same : ∀ a, t.getMem a = s.getMem a) (P j : Nat) :
    spareHalf t P j = spareHalf s P j := by
  simp only [spareHalf, MachineState.getHalfword, same]

/-! ### The run -/

private theorem pc_step {s : MachineState} {w : Nat} (pc : s.pc = BitVec.ofNat 64 (4096+4*w)) (k : Nat) :
    s.pc + BitVec.ofNat 64 (4*k) = BitVec.ofNat 64 (4096+4*(w+k)) := by
  rw [pc, ← BitVec.ofNat_add]
  congr 1
  omega

attribute [local irreducible] copyField chunkAfter gatherStart

set_option maxHeartbeats 4000000 in
theorem eighth_read_facts (s : MachineState) (P slot : Nat) (pc : s.pc = 0x19e8)
    (src : s.getReg .x21 = BitVec.ofNat 64 P) (dst : s.getReg .x7 = BitVec.ofNat 64 slot)
    (slotAligned : slot % 8 = 0) (slotRoom : slot+32 ≤ 32768) (above : 32768+210 ≤ P) (even : P%2=0)
    (room : P+28 ≤ MEMORY_BYTES) :
    GroupHop s (eighthRead s) 58 ∧ (eighthRead s).pc = 0x1528 ∧
    (eighthRead s).getReg .x21 = BitVec.ofNat 64 (P+28) ∧ (eighthRead s).getReg .x30 = 7#64 ∧
    (∀ r, r ≠ .x21 → r ≠ .x28 → r ≠ .x30 → r ≠ .x31 → (eighthRead s).getReg r = s.getReg r) ∧
    readBuffer (eighthRead s) slot 32 = packedNodeAt s (P-210) 7 ∧
    (∀ word < 2^61, 8*word+8 ≤ slot ∨ slot+32 ≤ 8*word → memoryView (eighthRead s) word = memoryView s word) := by
  have lim : MEMORY_BYTES < 2^60 := by decide
  -- the copy
  have ready : CopyReady eighthCode s P slot 0 :=
    ⟨by rw [pc]; rfl, src, by change s.getReg .x7 + BitVec.ofNat 64 0 = _; rw [dst]; exact BitVec.add_zero _,
      by change P+2*14 ≤ MEMORY_BYTES; omega, by change slot+2*14 ≤ MEMORY_BYTES; omega,
      even, by omega⟩
  let s1 := copyField eighthCode s
  have hop1 : GroupHop s s1 28 := fun fuel => copy_field_execute eighthCode s P slot ready fuel false
  have p1 : s1.pc = BitVec.ofNat 64 (4096+4*662) := copy_field_pc eighthCode s P slot ready
  have r1 (q : Reg) (k : q ≠ .x31) : s1.getReg q = s.getReg q := copy_field_register _ _ _ k
  obtain ⟨copied, kept⟩ := forward_memory 14 s P slot (by omega) (by omega) (by omega) even (by omega)
  have mem1 : s1.mem = (copyLoopMemory false 14 s (BitVec.ofNat 64 P) (BitVec.ofNat 64 slot)).mem :=
    copy_field_memory eighthCode s P slot ready
  have byte1 (i : Nat) (inside : i < 28) :
      s1.getByte (BitVec.ofNat 64 (slot+i)) = s.getByte (BitVec.ofNat 64 (P+i)) := by
    have := copied i inside
    simpa only [MachineState.getByte, MachineState.getMem, mem1] using this
  have other1 (query : Word) (away : ∀ i < 28, query ≠ BitVec.ofNat 64 (slot+i)) :
      s1.getByte query = s.getByte query := by
    have := kept query away
    simpa only [MachineState.getByte, MachineState.getMem, mem1] using this
  -- the gather
  have base1 : s1.getReg .x21 = BitVec.ofNat 64 P := (r1 .x21 (by decide)).trans src
  obtain ⟨g0pc, mem0, g0regs, g0x31⟩ := gather_start_post s1 .x21 P base1 (by omega)
  let g0 := gatherStart s1 .x21
  have hop2 : GroupHop s1 g0 2 :=
    execute_gather_start s1 662 .x21 P (by decide) p1 rfl rfl base1 (by omega) even (by omega)
  have pg0 : g0.pc = BitVec.ofNat 64 (4096+4*664) := by
    rw [g0pc, BitVec.add_assoc]
    exact pc_step p1 2
  have chunk (t : MachineState) (w j : Nat) (small : 1 ≤ j ∧ j ≤ 6) (tpc : t.pc = BitVec.ofNat 64 (4096+4*w))
      (word : w = 664+4*(j-1)) (tb : t.getReg .x21 = BitVec.ofNat 64 P) :
      GroupHop t (chunkAfter t .x21 .x28 j) 4 ∧
        (chunkAfter t .x21 .x28 j).pc = BitVec.ofNat 64 (4096+4*(w+4)) ∧
        (chunkAfter t .x21 .x28 j).getReg .x21 = BitVec.ofNat 64 P := by
    obtain ⟨lo, hi⟩ := small
    obtain ⟨tpc', _, tregs, _⟩ := chunk_post t .x21 .x28 j P tb (by omega) (by omega) (by decide) (by decide)
    refine ⟨?_, ?_, (tregs .x21 (by decide) (by decide)).trans tb⟩
    · subst word
      apply execute_chunk t _ .x21 .x28 j P (by omega) tpc _ _ _ _ tb (by omega) (by omega) even (by omega)
      all_goals (interval_cases j <;> rfl)
    · rw [tpc', BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]
      exact pc_step tpc 4
  have base0 : g0.getReg .x21 = BitVec.ofNat 64 P := (g0regs .x21 (by decide)).trans base1
  obtain ⟨h3, pg1, b1⟩ := chunk g0 664 1 (by decide) pg0 rfl base0
  let g1 := chunkAfter g0 .x21 .x28 1
  obtain ⟨h4, pg2, b2⟩ := chunk g1 668 2 (by decide) pg1 rfl b1
  let g2 := chunkAfter g1 .x21 .x28 2
  obtain ⟨h5, pg3, b3⟩ := chunk g2 672 3 (by decide) pg2 rfl b2
  let g3 := chunkAfter g2 .x21 .x28 3
  obtain ⟨h6, pg4, b4⟩ := chunk g3 676 4 (by decide) pg3 rfl b3
  let g4 := chunkAfter g3 .x21 .x28 4
  obtain ⟨h7, pg5, b5⟩ := chunk g4 680 5 (by decide) pg4 rfl b4
  let g5 := chunkAfter g4 .x21 .x28 5
  obtain ⟨h8, pg6, b6⟩ := chunk g5 684 6 (by decide) pg5 rfl b5
  let g6 := chunkAfter g5 .x21 .x28 6
  have gathered : eighthGather s1 = g6 := rfl
  have g6mem (a : Word) : g6.getMem a = s1.getMem a := by
    rw [← gathered]
    exact eighth_gather_mem s1 a
  -- the tail
  have dst6 : g6.getReg .x7 = BitVec.ofNat 64 slot := by
    rw [← gathered, eighth_gather_register _ _ (by decide) (by decide), r1 .x7 (by decide), dst]
  have address : g6.getReg .x7 + signExtend12 28 = BitVec.ofNat 64 (slot+24+4) := by
    rw [dst6, show signExtend12 28 = BitVec.ofNat 64 28 from rfl, ← BitVec.ofNat_add]
  let t1 := execInstrBr g6 (.SW .x7 .x31 28)
  let t2 := execInstrBr t1 (.ADDI .x21 .x21 28)
  let t3 := execInstrBr t2 (.ADDI .x30 .x0 7)
  have h9 : GroupHop g6 t1 1 := arm_hop g6 688 _ (by decide) (by simpa using pg6) rfl
    (sw_step g6 .x7 .x31 28 (by rw [address]; exact access_ofNat _ 4 (by omega) (by omega))) rfl
  have pt1 : t1.pc = BitVec.ofNat 64 (4096+4*689) := pc_next (w := 688) (by simpa using pg6) rfl
  have h10 : GroupHop t1 t2 1 := arm_hop t1 689 _ (by decide) pt1 rfl rfl rfl
  have pt2 : t2.pc = BitVec.ofNat 64 (4096+4*690) := pc_next pt1 rfl
  have h11 : GroupHop t2 t3 1 := arm_hop t2 690 _ (by decide) pt2 rfl rfl rfl
  have pt3 : t3.pc = BitVec.ofNat 64 (4096+4*691) := pc_next pt2 rfl
  have h12 := cap_jal_hop t3 691 330 2095708 (by decide) pt3 rfl rfl
  have final : eighthRead s = t3.setPC (BitVec.ofNat 64 (4096+4*330)) := rfl
  -- memory of the final state
  have memFinal (a : Word) (away : a ≠ BitVec.ofNat 64 (slot+24)) : (eighthRead s).getMem a = s1.getMem a := by
    rw [final]
    simp only [t3, t2, t1, execInstrBr, MachineState.setWord32, arm_getMem_set_pc, arm_getMem_set_reg]
    rw [address, arm_align _ 4 (by omega) (by decide), MachineState.getMem_setMem_ne away, g6mem]
  have memTop : (eighthRead s).getMem (BitVec.ofNat 64 (slot+24)) =
      (g6.getReg .x31).truncate 32 ++ (s1.getMem (BitVec.ofNat 64 (slot+24))).extractLsb' 0 32 := by
    rw [final]
    simp only [t3, t2, t1, execInstrBr, MachineState.setWord32, arm_getMem_set_pc, arm_getMem_set_reg]
    rw [address, arm_align _ 4 (by omega) (by decide), arm_byte_offset _ 4 (by omega) (by decide),
      MachineState.getMem_setMem_eq, show (4:Nat)/4 = 1 from rfl, replace_word_high, g6mem]
  -- the gathered bits
  have memOf (t : MachineState) (j : Nat) (a : Word) : (chunkAfter t .x21 .x28 j).getMem a = t.getMem a :=
    chunk_mem t .x21 .x28 j a
  obtain ⟨-, -, -, c6⟩ := chunk_post g5 .x21 .x28 6 P b5 (by decide) (by omega) (by decide) (by decide)
  obtain ⟨-, -, -, c5⟩ := chunk_post g4 .x21 .x28 5 P b4 (by decide) (by omega) (by decide) (by decide)
  obtain ⟨-, -, -, c4⟩ := chunk_post g3 .x21 .x28 4 P b3 (by decide) (by omega) (by decide) (by decide)
  obtain ⟨-, -, -, c3⟩ := chunk_post g2 .x21 .x28 3 P b2 (by decide) (by omega) (by decide) (by decide)
  obtain ⟨-, -, -, c2⟩ := chunk_post g1 .x21 .x28 2 P b1 (by decide) (by omega) (by decide) (by decide)
  obtain ⟨-, -, -, c1⟩ := chunk_post g0 .x21 .x28 1 P base0 (by decide) (by omega) (by decide) (by decide)
  have e6 : g6.getReg .x31 = g5.getReg .x31 ||| (((spareHalf g5 P 6).zeroExtend 64 >>> 14) <<< (2*6)) := c6
  have e5 : g5.getReg .x31 = g4.getReg .x31 ||| (((spareHalf g4 P 5).zeroExtend 64 >>> 14) <<< (2*5)) := c5
  have e4 : g4.getReg .x31 = g3.getReg .x31 ||| (((spareHalf g3 P 4).zeroExtend 64 >>> 14) <<< (2*4)) := c4
  have e3 : g3.getReg .x31 = g2.getReg .x31 ||| (((spareHalf g2 P 3).zeroExtend 64 >>> 14) <<< (2*3)) := c3
  have e2 : g2.getReg .x31 = g1.getReg .x31 ||| (((spareHalf g1 P 2).zeroExtend 64 >>> 14) <<< (2*2)) := c2
  have e1 : g1.getReg .x31 = g0.getReg .x31 ||| (((spareHalf g0 P 1).zeroExtend 64 >>> 14) <<< (2*1)) := c1
  have e0 : g0.getReg .x31 = (spareHalf s1 P 0).zeroExtend 64 >>> 14 := g0x31
  have q1 : spareHalf g0 P 1 = spareHalf s1 P 1 := spare_half_mem mem0 P 1
  have q2 : spareHalf g1 P 2 = spareHalf s1 P 2 :=
    (spare_half_mem (memOf g0 1) P 2).trans (spare_half_mem mem0 P 2)
  have q3 : spareHalf g2 P 3 = spareHalf s1 P 3 :=
    ((spare_half_mem (memOf g1 2) P 3).trans (spare_half_mem (memOf g0 1) P 3)).trans (spare_half_mem mem0 P 3)
  have q4 : spareHalf g3 P 4 = spareHalf s1 P 4 :=
    (((spare_half_mem (memOf g2 3) P 4).trans (spare_half_mem (memOf g1 2) P 4)).trans
      (spare_half_mem (memOf g0 1) P 4)).trans (spare_half_mem mem0 P 4)
  have q5 : spareHalf g4 P 5 = spareHalf s1 P 5 :=
    ((((spare_half_mem (memOf g3 4) P 5).trans (spare_half_mem (memOf g2 3) P 5)).trans
      (spare_half_mem (memOf g1 2) P 5)).trans (spare_half_mem (memOf g0 1) P 5)).trans (spare_half_mem mem0 P 5)
  have q6 : spareHalf g5 P 6 = spareHalf s1 P 6 :=
    (((((spare_half_mem (memOf g4 5) P 6).trans (spare_half_mem (memOf g3 4) P 6)).trans
      (spare_half_mem (memOf g2 3) P 6)).trans (spare_half_mem (memOf g1 2) P 6)).trans
      (spare_half_mem (memOf g0 1) P 6)).trans (spare_half_mem mem0 P 6)
  have x31 : g6.getReg .x31 = ((spareHalf s1 P 6).extractLsb' 14 2 ++ (spareHalf s1 P 5).extractLsb' 14 2 ++
      (spareHalf s1 P 4).extractLsb' 14 2 ++ (spareHalf s1 P 3).extractLsb' 14 2 ++
      (spareHalf s1 P 2).extractLsb' 14 2 ++ (spareHalf s1 P 1).extractLsb' 14 2 ++
      (spareHalf s1 P 0).extractLsb' 14 2).zeroExtend 64 := by
    rw [e6, e5, e4, e3, e2, e1, e0, q1, q2, q3, q4, q5, q6]
    exact gather_bits _ _ _ _ _ _ _
  -- the spares are the block's bits 238..239, untouched by the copy
  have spare (j : Nat) (small : j ≤ 6) :
      (spareHalf s1 P j).extractLsb' 14 2 = packedSpareAt s (P-210+30*j) := by
    have q : P-182+30*j = (P-210+30*j)+28 := by omega
    have frameS : readBuffer s1 (P-210+30*j) 30 = readBuffer s (P-210+30*j) 30 := by
      apply buffer_byte_frame
      intro i inside
      apply word_eq_of_byte_frame
      intro b bb
      apply other1
      intro k kk same
      have eq := Opening.nat_address_injective (by omega) (by omega) same
      omega
    unfold spareHalf packedSpareAt
    rw [q, half_spare s1 (P-210+30*j) (by omega) (by omega), frameS]
  -- the slot
  have low (k : Nat) (small : k < 3) :
      (eighthRead s).getMem (BitVec.ofNat 64 (slot+8*k)) = readBuffer s (P+8*k) 8 := by
    rw [memFinal _ (cap_ofNat_ne (by omega) (by omega) (by omega))]
    have d := dword_from_bytes s1 s (slot+8*k) (P+8*k) 8 (by omega) (by decide)
      (fun i inside => by
        have := byte1 (8*k+i) (by omega)
        simpa only [Nat.add_assoc] using this)
    simpa only [Nat.reduceMul, BitVec.extractLsb'_eq_self] using d
  have top4 : (s1.getMem (BitVec.ofNat 64 (slot+24))).extractLsb' 0 32 = readBuffer s (P+24) 4 :=
    dword_from_bytes s1 s (slot+24) (P+24) 4 (by omega) (by decide)
      (fun i inside => by
        have := byte1 (24+i) (by omega)
        simpa only [Nat.add_assoc] using this)
  have hopAll : GroupHop s (t3.setPC (BitVec.ofNat 64 (4096+4*330))) 58 :=
    ((((((((((hop1.thenDo hop2).thenDo h3).thenDo h4).thenDo h5).thenDo h6).thenDo h7).thenDo h8).thenDo h9).thenDo
      h10).thenDo h11).thenDo h12
  refine ⟨final ▸ hopAll, rfl, ?_, ?_, fun r a b c d => eighth_read_register s r a b c d, ?_, ?_⟩
  · rw [final, MachineState.getReg_setPC]
    have e : t3.getReg .x21 = t1.getReg .x21 + signExtend12 28 := by
      simp only [t3, t2, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x30 ≠ Reg.x21 by decide),
        MachineState.getReg_setReg_eq (show Reg.x21 ≠ Reg.x0 by decide)]
    have f : t1.getReg .x21 = BitVec.ofNat 64 P := by
      simp only [t1, execInstrBr, MachineState.setWord32, MachineState.getReg_setPC, arm_getReg_set_mem]
      exact b6
    rw [e, f, show signExtend12 28 = BitVec.ofNat 64 28 from rfl, ← BitVec.ofNat_add]
  · rw [final, MachineState.getReg_setPC]
    have e : t3.getReg .x30 = t2.getReg .x0 + signExtend12 7 := by
      simp only [t3, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (show Reg.x30 ≠ Reg.x0 by decide)]
    rw [e]
    rfl
  · rw [read_digest_words _ _ slotAligned]
    have l0 := low 0 (by decide)
    have l1 := low 1 (by decide)
    have l2 := low 2 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at l0 l1 l2
    rw [l0, l1, l2, memTop, x31, truncate_widen, top4]
    unfold packedNodeAt
    rw [ite_eq_left rfl, show P-210+210 = P by omega, ← split_dwords ((0 : BitVec 18) ++ _), node_high,
      node_low _ _ 0 (by decide), node_low _ _ 64 (by decide), node_low _ _ 128 (by decide)]
    have r0 := read_buffer_slice s P 28 0 8 (by decide)
    have r1' := read_buffer_slice s P 28 8 8 (by decide)
    have r2 := read_buffer_slice s P 28 16 8 (by decide)
    have r3 := read_buffer_slice s P 28 24 4 (by decide)
    simp only [Nat.reduceMul, Nat.add_zero] at r0 r1' r2 r3
    rw [r0, r1', r2, r3, spare 0 (by decide), spare 1 (by decide), spare 2 (by decide), spare 3 (by decide),
      spare 4 (by decide), spare 5 (by decide), spare 6 (by decide)]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul]
  · intro word bounded outside
    have away : BitVec.ofNat 64 (8*word) ≠ BitVec.ofNat 64 (slot+24) := cap_ofNat_ne (by omega) (by omega) (by omega)
    change (eighthRead s).getMem (BitVec.ofNat 64 (8*word)) = s.getMem (BitVec.ofNat 64 (8*word))
    rw [memFinal _ away]
    have same := word_eq_of_byte_frame s s1 word (fun i inside => other1 _ (fun k kk eq => by
      have := Opening.nat_address_injective (by omega) (by omega) eq
      omega))
    exact same

end TwoPermutationPrototype.Packed.Checker
