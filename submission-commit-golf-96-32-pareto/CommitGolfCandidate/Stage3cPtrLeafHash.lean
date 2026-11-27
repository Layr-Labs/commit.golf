import CommitGolfCandidate.Stage3cPtrLeafSites
import CommitGolfCandidate.Stage3cPtrLeafCall
import CommitGolfCandidate.Stage3cLeafEntry

namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-- Registers that survive every leaf hash and every cursor update. -/
structure LeafRegs (s : MachineState) (k : Nat) : Prop where
  msg : s.getReg .x21 = BitVec.ofNat 64 (msgCursor k)
  row : s.getReg .x22 = BitVec.ofNat 64 (rowCursor k)
  node : s.getReg .x23 = BitVec.ofNat 64 (nodeCursor k)
  counter : s.getReg .x20 = BitVec.ofNat 64 (tileCounter k)
  mode : s.getReg .x5 = 0
  len : s.getReg .x11 = 96
  kind : s.getReg .x13 = 0
  baseMsg : s.getReg .x8 = 4096
  root : s.getReg .x9 = 4294971392
  td : s.getReg .x18 = 4294975488
  rows : s.getReg .x19 = rowBase
  scratch : s.getReg .x24 = 7516200960
  strideMsg : s.getReg .x25 = 4096
  strideRow : s.getReg .x26 = 2944
  spare : s.getReg .x27 = 0

structure AtLeaf (s : MachineState) (k : Nat) : Prop extends LeafRegs s k where
  pc : s.pc = pcAt (if k < LENGTH then leafPC k else 5678)

def srcImm (k c : Nat) : BitVec 12 := BitVec.ofNat 12 (immRaw (srcOff (k % 128) c))
def dstImm (k c : Nat) : BitVec 12 := BitVec.ofNat 12 (immRaw (dstOff (k % 128) c))

def leafReady (s : MachineState) (k c : Nat) :=
  prepareCall s (srcReg c) (dstReg c) (srcImm k c) (dstImm k c)

def leafReply (s : MachineState) (k c : Nat) (w : Digest) :=
  callState s (srcReg c) (dstReg c) (srcImm k c) (dstImm k c) w

private theorem base_dst (c : Fin 4) : Reg.x10 ≠ dstReg c.val := by
  fin_cases c <;> decide

private theorem cursor_split (n : Nat) (lo : 2048 ≤ n) (hi : n < 2 ^ 64) :
    BitVec.ofNat 64 n = BitVec.ofNat 64 (n - 2048) + BitVec.ofNat 64 2048 := by
  rw [← BitVec.ofNat_add]
  exact congrArg (BitVec.ofNat 64) (by omega)

private theorem add_src (base : Nat) (j : Fin 128) (c : Fin 4)
    (lo : 2048 ≤ base) (hi : base < 2 ^ 64) :
    BitVec.ofNat 64 base + signExtend12 (BitVec.ofNat 12 (immRaw (srcOff j.val c.val))) =
      BitVec.ofNat 64 (base - 2048 + srcOff j.val c.val) := by
  rw [cursor_split base lo hi, BitVec.add_assoc, (sext_offset j c).1, ← BitVec.ofNat_add]

private theorem add_dst (base : Nat) (j : Fin 128) (c : Fin 4)
    (lo : 2048 ≤ base) (hi : base < 2 ^ 64) :
    BitVec.ofNat 64 base + signExtend12 (BitVec.ofNat 12 (immRaw (dstOff j.val c.val))) =
      BitVec.ofNat 64 (base - 2048 + dstOff j.val c.val) := by
  rw [cursor_split base lo hi, BitVec.add_assoc, (sext_offset j c).2, ← BitVec.ofNat_add]

private theorem cursor_bounds (k : Nat) (hk : k < LENGTH) :
    2048 ≤ msgCursor k ∧ msgCursor k < 2 ^ 64 ∧
    2048 ≤ rowCursor k ∧ rowCursor k < 2 ^ 64 ∧
    2048 ≤ nodeCursor k ∧ nodeCursor k < 2 ^ 64 := by
  have hk' : k < 16777216 := by simpa [LENGTH, LOG_LENGTH] using hk
  have t : k / 128 ≤ 131071 := by omega
  have g16 : (k % 128) / 16 ≤ 7 := by omega
  have g32 : (k % 128) / 32 ≤ 3 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [msgCursor]; omega
  · have hle : msgCursor k ≤ 6144 + 131071 * 32768 + 7 * 4096 := by
      simp only [msgCursor]
      exact Nat.add_le_add
        (Nat.add_le_add_left (Nat.mul_le_mul_right 32768 t) 6144)
        (Nat.mul_le_mul_right 4096 g16)
    exact Nat.lt_of_le_of_lt hle (by decide)
  · simp only [rowCursor, rowBase]; omega
  · have hle : rowCursor k ≤ rowBase + 2048 + 131071 * 11776 + 3 * 2944 := by
      simp only [rowCursor]
      exact Nat.add_le_add
        (Nat.add_le_add_left (Nat.mul_le_mul_right 11776 t) (rowBase + 2048))
        (Nat.mul_le_mul_right 2944 g32)
    have hcap : rowBase + 2048 + 131071 * 11776 + 3 * 2944 < 2 ^ 64 := by
      unfold rowBase; decide
    exact Nat.lt_of_le_of_lt hle hcap
  · simp only [nodeCursor]; omega
  · have hle : nodeCursor k ≤ 4294975488 + 2048 + 131071 * 6144 + 3 * 1536 := by
      simp only [nodeCursor]
      exact Nat.add_le_add
        (Nat.add_le_add_left (Nat.mul_le_mul_right 6144 t) (4294975488 + 2048))
        (Nat.mul_le_mul_right 1536 g32)
    exact Nat.lt_of_le_of_lt hle (by decide)

theorem ready_addresses {s : MachineState} {k : Nat} (regs : LeafRegs s k)
    (c : Fin 4) (hk : k < LENGTH) :
    let r := leafReady s k c.val
    r.getReg .x10 = BitVec.ofNat 64 (absSrc k c.val) ∧
    r.getReg .x12 = BitVec.ofNat 64 (absDst k c.val) := by
  let j : Fin 128 := ⟨k % 128, Nat.mod_lt k (by decide)⟩
  obtain ⟨loM, hiM, loR, hiR, loN, hiN⟩ := cursor_bounds k hk
  obtain ⟨src, dst⟩ := call_addresses s (srcReg c.val) (dstReg c.val) (srcImm k c.val)
    (dstImm k c.val) (base_dst c)
  fin_cases c
  · simp only [leafReady, srcImm, dstImm, srcReg, dstReg, absSrc, absDst, regs.msg,
      show (0 = 3) = False by decide, ite_false, ite_true] at src dst ⊢
    rw [src, dst]
    exact ⟨add_src (msgCursor k) j ⟨0, by decide⟩ loM hiM,
      add_dst (msgCursor k) j ⟨0, by decide⟩ loM hiM⟩
  · simp only [leafReady, srcImm, dstImm, srcReg, dstReg, absSrc, absDst, regs.msg, regs.row,
      show (1 = 3) = False by decide, show (1 = 0) = False by decide, ite_false] at src dst ⊢
    rw [src, dst]
    exact ⟨add_src (msgCursor k) j ⟨1, by decide⟩ loM hiM,
      add_dst (rowCursor k) j ⟨1, by decide⟩ loR hiR⟩
  · simp only [leafReady, srcImm, dstImm, srcReg, dstReg, absSrc, absDst, regs.msg, regs.row,
      show (2 = 3) = False by decide, show (2 = 0) = False by decide, ite_false] at src dst ⊢
    rw [src, dst]
    exact ⟨add_src (msgCursor k) j ⟨2, by decide⟩ loM hiM,
      add_dst (rowCursor k) j ⟨2, by decide⟩ loR hiR⟩
  · simp only [leafReady, srcImm, dstImm, srcReg, dstReg, absSrc, absDst, regs.row, regs.node,
      show (3 = 0) = False by decide, ite_false, ite_true] at src dst ⊢
    rw [src, dst]
    exact ⟨add_src (rowCursor k) j ⟨3, by decide⟩ loR hiR,
      add_dst (nodeCursor k) j ⟨3, by decide⟩ loN hiN⟩

theorem reply_regs {s : MachineState} {k : Nat} (regs : LeafRegs s k) (c : Fin 4) (w : Digest) :
    LeafRegs (leafReply s k c.val w) k := by
  constructor <;>
    first
      | exact (call_register _ _ _ .x21 _ _ _ (by decide) (by decide)).trans regs.msg
      | exact (call_register _ _ _ .x22 _ _ _ (by decide) (by decide)).trans regs.row
      | exact (call_register _ _ _ .x23 _ _ _ (by decide) (by decide)).trans regs.node
      | exact (call_register _ _ _ .x20 _ _ _ (by decide) (by decide)).trans regs.counter
      | exact (call_register _ _ _ .x5 _ _ _ (by decide) (by decide)).trans regs.mode
      | exact (call_register _ _ _ .x11 _ _ _ (by decide) (by decide)).trans regs.len
      | exact (call_register _ _ _ .x13 _ _ _ (by decide) (by decide)).trans regs.kind
      | exact (call_register _ _ _ .x8 _ _ _ (by decide) (by decide)).trans regs.baseMsg
      | exact (call_register _ _ _ .x9 _ _ _ (by decide) (by decide)).trans regs.root
      | exact (call_register _ _ _ .x18 _ _ _ (by decide) (by decide)).trans regs.td
      | exact (call_register _ _ _ .x19 _ _ _ (by decide) (by decide)).trans regs.rows
      | exact (call_register _ _ _ .x24 _ _ _ (by decide) (by decide)).trans regs.scratch
      | exact (call_register _ _ _ .x25 _ _ _ (by decide) (by decide)).trans regs.strideMsg
      | exact (call_register _ _ _ .x26 _ _ _ (by decide) (by decide)).trans regs.strideRow
      | exact (call_register _ _ _ .x27 _ _ _ (by decide) (by decide)).trans regs.spare

theorem leafReplyPC (s : MachineState) (k c n : Nat) (w : Digest) (pc : s.pc = pcAt n) :
    (leafReply s k c w).pc = pcAt (n + 3) := by
  rw [show (leafReply s k c w).pc = s.pc + 12 from call_pc s _ _ _ _ w, pc]
  unfold pcAt
  change BitVec.ofNat 64 (4096 + 4 * n) + BitVec.ofNat 64 12 =
    BitVec.ofNat 64 (4096 + 4 * (n + 3))
  rw [← BitVec.ofNat_add]
  exact congrArg (BitVec.ofNat 64) (by omega)

private theorem execute_site {s : MachineState} {k : Nat} (regs : LeafRegs s k)
    (c : Fin 4) (pc : s.pc = pcAt (leafPC k + 3 * c.val)) (hk : k < LENGTH) (fuel : Nat) :
    execute commitImage (fuel + 3) s true =
      (do let w ← hash (readBuffer s (absSrc k c.val) 96)
          let r ← execute commitImage fuel (leafReply s k c.val w) true
          return r.charge 10 1) := by
  obtain ⟨op₁, op₂, op₃⟩ := call_sites k c
  obtain ⟨srcA, dstA⟩ := ready_addresses regs c hk
  obtain ⟨sa, sv, da, dv⟩ := leaf_range k hk c
  have sn : ((leafReady s k c.val).getReg .x10).toNat = absSrc k c.val := by
    rw [srcA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : absSrc k c.val < 2 ^ 64)]
  have dn : ((leafReady s k c.val).getReg .x12).toNat = absDst k c.val := by
    rw [dstA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : absDst k c.val < 2 ^ 64)]
  have valid : rangeValid ((leafReady s k c.val).getReg .x10) 96 = true ∧
      ((leafReady s k c.val).getReg .x10).toNat % 8 = 0 ∧
      rangeValid ((leafReady s k c.val).getReg .x12) 32 = true ∧
      ((leafReady s k c.val).getReg .x12).toNat % 8 = 0 := by
    simp only [rangeValid, sn, dn, MEMORY_BYTES]
    exact ⟨decide_eq_true sv, by simpa [sn] using sa, decide_eq_true dv, by simpa [dn] using da⟩
  have law := execute_compression s (leafPC k + 3 * c.val) fuel (srcReg c.val) (dstReg c.val)
    (srcImm k c.val) (dstImm k c.val) op₁ op₂ op₃ pc regs.mode regs.len regs.kind valid
  change _ = (do let w ← hash (readBuffer s ((leafReady s k c.val).getReg .x10).toNat 96)
                 let r ← execute commitImage fuel (leafReply s k c.val w) true
                 pure (r.charge 10 1)) at law
  rw [sn] at law
  exact law

def siteResult (h : Compression) (s : MachineState) (k : Nat) (c : Nat) :=
  leafReply s k c (h (readBuffer s (absSrc k c) 96))

theorem fixed_site (o : Oracle) {s : MachineState} {k : Nat} (regs : LeafRegs s k)
    (c : Fin 4) (pc : s.pc = pcAt (leafPC k + 3 * c.val)) (hk : k < LENGTH) (fuel : Nat) :
    o.run (execute commitImage (fuel + 3) s true) =
      (do let (out, n) ← o.run (execute commitImage fuel (siteResult o.compression s k c.val) true)
          return (out.charge 10 1, 1 + n)) := by
  rw [execute_site regs c pc hk]
  unfold Late.hash
  erw [oracle_run_public_bind o (.inl _)]
  simp only [oracle_run_bind, oracle_run_pure, pure_bind, bind_assoc, Nat.add_zero]
  rfl

def finalLeaf (h : Compression) (s : MachineState) (k : Nat) :=
  let u := siteResult h s k 0
  let a := siteResult h u k 1
  let b := siteResult h a k 2
  siteResult h b k 3

theorem fixed_leaf (o : Oracle) {s : MachineState} {k : Nat} (a : AtLeaf s k)
    (hk : k < LENGTH) (fuel : Nat) :
    o.run (execute commitImage (fuel + 12) s true) =
      (do let (out, n) ← o.run (execute commitImage fuel (finalLeaf o.compression s k) true)
          return (out.charge 40 4, 4 + n)) := by
  have pc0 : s.pc = pcAt (leafPC k) := by rw [a.pc, ite_eq_left hk]
  let c0 : Fin 4 := 0
  let c1 : Fin 4 := 1
  let c2 : Fin 4 := 2
  let c3 : Fin 4 := 3
  let u := siteResult o.compression s k c0.val
  let b := siteResult o.compression u k c1.val
  let c := siteResult o.compression b k c2.val
  have ru : LeafRegs u k := reply_regs a.toLeafRegs c0 _
  have rb : LeafRegs b k := reply_regs ru c1 _
  have rc : LeafRegs c k := reply_regs rb c2 _
  have pc1 : u.pc = pcAt (leafPC k + 3) := leafReplyPC s k c0.val (leafPC k) _ pc0
  have pc2 : b.pc = pcAt (leafPC k + 6) := leafReplyPC u k c1.val (leafPC k + 3) _ pc1
  have pc3 : c.pc = pcAt (leafPC k + 9) := leafReplyPC b k c2.val (leafPC k + 6) _ pc2
  rw [fixed_site o a.toLeafRegs c0 pc0 hk (fuel + 9),
      fixed_site o ru c1 pc1 hk (fuel + 6),
      fixed_site o rb c2 pc2 hk (fuel + 3),
      fixed_site o rc c3 pc3 hk fuel]
  simp only [bind_assoc, pure_bind, Execution.charge, ← Nat.add_assoc]
  rfl

theorem initial_leaf (s : MachineState) (a : AtLeaves s) : AtLeaf s 0 := by
  obtain ⟨msg0, row0, node0, ctr0⟩ := cursors_initial
  exact {
    toLeafRegs := {
      msg := a.curMsg.trans (congrArg (BitVec.ofNat 64) msg0.symm)
      row := a.curRow.trans (congrArg (BitVec.ofNat 64) row0.symm)
      node := a.curNode.trans (congrArg (BitVec.ofNat 64) node0.symm)
      counter := a.tiles.trans (congrArg (BitVec.ofNat 64) ctr0.symm)
      mode := a.mode
      len := a.len
      kind := a.kind
      baseMsg := a.msg
      root := a.root
      td := a.td
      rows := by simpa [rowBase] using a.rows
      scratch := a.scratch
      strideMsg := a.strideMsg
      strideRow := a.strideRow
      spare := a.spare }
    pc := by
      rw [a.pc, ite_eq_left (by decide : 0 < LENGTH)]
      unfold pcAt leafPC
      rfl }

end CommitGolfCandidate.Chained.BinaryMachine
