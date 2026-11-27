import CommitGolfCandidate.Stage3cTreeFrame
import CommitGolfCandidate.Stage3cPlainBlock
import CommitGolfCandidate.WriteMemory
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem read_join (s : MachineState) (a low high : Nat) :
    readBuffer s (a + low) high ++ readBuffer s a low =
      (readBuffer s a (low + high)).extractLsb' 0 (8 * high + 8 * low) := by
  have first := read_buffer_slice s a (low + high) 0 low (by omega)
  have second := read_buffer_slice s a (low + high) low high (by omega)
  simp only [Nat.add_zero, Nat.mul_zero] at first
  rw [← first, ← second]
  exact BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)

theorem read_parent_block (s : MachineState) (a : Nat) (l r : Output) (tag : Word)
    (left : readBuffer s a 32 = l) (right : readBuffer s (a + 32) 32 = r)
    (t : readBuffer s (a + 64) 8 = tag) (pad : readBuffer s (a + 72) 24 = 0) :
    readBuffer s a 96 = parentBlock l r tag := by
  have lo := read_join s a 32 32
  have high := read_join s (a + 64) 8 24
  have all := read_join s a 64 32
  rw [show a + 64 + 8 = a + 72 by omega, pad, t] at high
  rw [left, right] at lo
  change _ = (readBuffer s a 64).extractLsb' 0 512 at lo
  change _ = (readBuffer s (a + 64) 32).extractLsb' 0 256 at high
  change _ = (readBuffer s a 96).extractLsb' 0 768 at all
  simp only [BitVec.extractLsb'_eq_self] at lo high all
  rw [← lo, ← high] at all
  exact all.symm

theorem plain_node_digest (H : Compression) (h : Height) (l r : Output) (simple : ¬chained h) :
    parentDigest H h l r = storeReply h (H (parentBlock l r 0)) := by
  have size := (by decide +kernel : ∀ d : Height, ¬chained d → calls d = 1) h simple
  rw [parentDigest, queries, size, Nat.sub_self, parentBlock_plain h l r simple]
  rfl

theorem read_only_mem (s t : MachineState) (r n : Nat) (eq : s.mem = t.mem) :
    readBuffer s r n = readBuffer t r n := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem, eq]

theorem written (s : MachineState) (a : Nat) (v : Output) :
    readBuffer (writeBits s (BitVec.ofNat 64 a) v) a 32 = v := by
  simpa only [Nat.add_zero, Nat.mul_zero, BitVec.extractLsb'_eq_self] using
    write_bits_digest s a 0 v (by decide) (by decide)

theorem pointer_input {s : MachineState} {h : Height} {p : Nat}
    (pads : gaps s) (valid : p < count h) (plain : ¬chained h) :
    readBuffer s (nodeAddress h.val (2 * p)) 96 =
      parentBlock (readBuffer s (nodeAddress h.val (2 * p)) 32)
        (readBuffer s (nodeAddress h.val (2 * p + 1)) 32) 0 := by
  have gap := pads h p valid
  apply read_parent_block
  · rfl
  · rw [(children_contiguous h.val p).1]
  · exact gap.2 plain
  · exact gap.1

/-- A pointer store writes `parentDigest` at the parent slot and leaves every disjoint buffer alone.
The chained side condition is vacuous on an unchained level. -/
theorem pointer_effect (H : Compression) (h : Height) (p : Nat) (s t : MachineState)
    (plain : ¬chained h) (inside : p < count h) (pads : gaps s)
    (mem : t.mem = (writeBits s (BitVec.ofNat 64 (nodeAddress (h.val + 1) p))
      (storeReply h (H (readBuffer s (nodeAddress h.val (2 * p)) 96)))).mem) :
    NodeEffect H h p s t := by
  let dst := nodeAddress (h.val + 1) p
  let v := storeReply h (H (readBuffer s (nodeAddress h.val (2 * p)) 96))
  constructor
  · apply (read_only_mem _ _ dst 32 mem).trans
    apply (written s dst v).trans
    let left := readBuffer s (nodeAddress h.val (2 * p)) 32
    let right := readBuffer s (nodeAddress h.val (2 * p + 1)) 32
    have pack : (readBuffer s (nodeAddress h.val (2 * p)) 96 : BitVec COMPRESSION_INPUT_LENGTH) =
        (parentBlock left right 0 : BitVec COMPRESSION_INPUT_LENGTH) :=
      pointer_input pads inside plain
    have dig := plain_node_digest H h left right plain
    refine Eq.trans ?_ dig.symm
    simp only [v]
    exact congrArg (fun x => storeReply h (H x)) pack
  · intro a n fit sep _
    apply (read_only_mem _ _ a n mem).trans
    apply write_bits_read_outside
    · have room := parent_below_salts (h.val + 1) p inside
      unfold rowBase at room
      change dst + 32 ≤ 2 ^ 64
      simp only [dst]
      omega
    · change a + n ≤ 2 ^ 36 at fit
      omega
    · exact sep

end CommitGolfCandidate.Chained.BinaryMachine
