import CommitGolfCandidate.S5LeafMemory
import CommitGolfCandidate.S5Layout

namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def msgAddr (i : Nat) := 4096 + 256*i
def rowAddr (i : Nat) := rowBase + 96*i
def contentAddr (i : Nat) := rowAddr i + 32*(i%2)
def padAddr (i : Nat) := rowAddr i + (if i%2 = 0 then 64 else 24)

def store (s : MachineState) (a : Nat) (w : Digest) :=
  writeBits s (BitVec.ofNat 64 a) w

theorem store_read (s : MachineState) (a : Nat) (w : Digest) : readBuffer (store s a w) a 32 = w := by
  have slice := read_serialized_slice (store s a w) w a 0 32 (by
    intro j hj
    simpa only [store, Nat.zero_add, BitVec.ofNat_add] using
      write_bits_byte s (BitVec.ofNat 64 a) w j (by omega) (by decide))
  exact slice.trans BitVec.extractLsb'_eq_self

theorem store_away (s : MachineState) (a : Nat) (w : Digest) (r n : Nat)
    (ha : a+32 ≤ 2^64) (hr : r+n ≤ 2^64) (disjoint : r+n ≤ a ∨ a+32 ≤ r) :
    readBuffer (store s a w) r n = readBuffer s r n :=
  write_bits_read_outside s w a r n ha hr disjoint

def compressAt (h : Compression) (s : MachineState) (src dst : Nat) :=
  store s dst (h (readBuffer s src 96))

def writeLeaf (h : Compression) (s : MachineState) (i : Nat) :=
  let t := compressAt h s (msgAddr i) (msgAddr i+64)
  let a := compressAt h t (msgAddr i+64) (contentAddr i)
  let b := compressAt h a (msgAddr i+160) (contentAddr i+32)
  compressAt h b (rowAddr i) (nodeAddress 0 i)

private theorem filled_row (s : MachineState) (i : Index) (a b : Digest) (salt : Salt)
    (pad : readBuffer s (padAddr i) 8 = 0) (random : readBuffer s (saltAddress i) 24 = salt) :
    readBuffer (store (store s (contentAddr i) a) (contentAddr i+32) b) (rowAddr i) 96 =
      finalBlock (i.val.testBit 0) salt a b := by
  have bound : rowAddr i+96 ≤ 2^64 := by
    have h := i.isLt; change i.val < 16777216 at h; unfold rowAddr rowBase; omega
  have saltAddr : saltAddress i = rowAddr i + (if i.val%2 = 0 then 72 else 0) := rfl
  rw [saltAddr] at random
  unfold padAddr at pad
  unfold contentAddr
  by_cases even : i.val%2 = 0
  · have par : i.val.testBit 0 = false := by simp [Nat.testBit_eq_decide_div_mod_eq, even]
    simp only [even, if_true, Nat.mul_zero, Nat.add_zero, par] at pad random ⊢
    apply even_row
    · rw [store_away, store_read] <;> omega
    · exact store_read _ _ _
    · rw [store_away, store_away, pad] <;> omega
    · rw [store_away, store_away, random] <;> omega
  · have odd : i.val%2 = 1 := by omega
    have par : i.val.testBit 0 = true := by simp [Nat.testBit_eq_decide_div_mod_eq, odd]
    simp only [odd, Nat.one_ne_zero, if_false, Nat.mul_one, Nat.add_zero, par] at pad random ⊢
    rw [show rowAddr i+32+32 = rowAddr i+64 by omega]
    apply odd_row
    · rw [store_away, store_away, random] <;> omega
    · rw [store_away, store_away, pad] <;> omega
    · rw [store_away, store_read] <;> omega
    · exact store_read _ _ _

private structure Bounds (i : Nat) : Prop where
  message : msgAddr i + 256 ≤ 2^64
  content : contentAddr i + 32 ≤ 2^64
  pad : padAddr i + 8 ≤ 2^64
  salt : saltAddress i + 24 ≤ 2^64
  last : msgAddr i + 160 + 96 ≤ contentAddr i
  pad_after : msgAddr i + 64 + 32 ≤ padAddr i
  salt_after : msgAddr i + 64 + 32 ≤ saltAddress i

private theorem bounds (i : Index) : Bounds i := by
  have hi := i.isLt
  change i.val < 16777216 at hi
  constructor <;> simp only [msgAddr, contentAddr, padAddr, saltAddress, rowAddr, rowBase] <;>
    first | omega | split <;> omega

private theorem compress_eq (h : Compression) (s : MachineState) (src dst : Nat) (x : Block)
    (read : readBuffer s src 96 = x) :
    compressAt h s src dst = store s dst (h x) :=
  congrArg (fun q => store s dst (h q)) read

attribute [local irreducible] store readBuffer compressAt

/-- Execute the four writes at the semantic addresses of the leaf loop. -/
theorem write_leaf_digest (h : Compression) (s : MachineState) (i : Index) (v : Entry) (salt : Salt)
    (message : readBuffer s (msgAddr i) 256 = v)
    (pad : readBuffer s (padAddr i) 8 = 0) (random : readBuffer s (saltAddress i) 24 = salt) :
    readBuffer (writeLeaf h s i) (nodeAddress 0 i) 32 = leaf h (i.val.testBit 0) salt v := by
  let u : Digest := h (firstBlock v)
  let t := store s (msgAddr i+64) u
  let a : Digest := h (middleBlock v u)
  let b : Digest := h (lastBlock v)
  let l := store t (contentAddr i) a
  let r := store l (contentAddr i+32) b
  have bd := bounds i
  have mq := bd.message
  have small : msgAddr i+64+32 ≤ 2^64 := by omega
  have small' : msgAddr i+160+96 ≤ 2^64 := by omega
  obtain ⟨fst,mid,last⟩ := first_two_inputs s (msgAddr i) v message h mq
  have m' : readBuffer t (msgAddr i+64) 96 = middleBlock v u := by unfold t store; exact mid
  have l' : readBuffer t (msgAddr i+160) 96 = lastBlock v := by unfold t store; exact last
  have preserved := store_away t (contentAddr i) a (msgAddr i+160) 96 bd.content small' (Or.inl bd.last)
  have pd := (store_away s (msgAddr i+64) u (padAddr i) 8 small bd.pad (Or.inr bd.pad_after)).trans pad
  have sa := (store_away s (msgAddr i+64) u (saltAddress i) 24 small bd.salt (Or.inr bd.salt_after)).trans random
  have eq₁ : compressAt h s (msgAddr i) (msgAddr i+64) = t := compress_eq _ _ _ _ _ fst
  have eq₂ : compressAt h t (msgAddr i+64) (contentAddr i) = l := compress_eq _ _ _ _ _ m'
  have eq₃ : compressAt h l (msgAddr i+160) (contentAddr i+32) = r :=
    compress_eq _ _ _ _ _ (preserved.trans l')
  have row : readBuffer r (rowAddr i) 96 = finalBlock (i.val.testBit 0) salt a b :=
    filled_row t i a b salt pd sa
  have eq₄ := compress_eq h r (rowAddr i) (nodeAddress 0 i) _ row
  simp only [writeLeaf, eq₁, eq₂, eq₃, eq₄]
  exact store_read r (nodeAddress 0 i) (h (finalBlock (i.val.testBit 0) salt a b))

end CommitGolfCandidate.S5Machine
