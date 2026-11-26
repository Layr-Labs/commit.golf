import CommitGolfCandidate.LateLeafWrites

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

structure Separate (i addr len : Nat) : Prop where
  message : addr+len ≤ msgAddr i+64 ∨ msgAddr i+96 ≤ addr
  row : addr+len ≤ contentAddr i ∨ contentAddr i+64 ≤ addr
  node : addr+len ≤ nodeAddress 0 i ∨ nodeAddress 0 i+32 ≤ addr

private theorem writes_range (i : Index) :
    msgAddr i+96 ≤ 2^64 ∧ contentAddr i+64 ≤ 2^64 ∧ nodeAddress 0 i+32 ≤ 2^64 := by
  have h := i.isLt; change i.val < 16777216 at h
  have zero : levelOffset 0 = 0 := by decide
  simp only [msgAddr, rowAddr, contentAddr, rowBase, nodeAddress, zero, gapOffset]
  omega

attribute [local irreducible] store readBuffer

theorem write_leaf_frame (h : Compression) (s : MachineState) (i : Index) (addr len : Nat)
    (valid : addr+len ≤ 2^64) (sep : Separate i addr len) :
    readBuffer (writeLeaf h s i) addr len = readBuffer s addr len := by
  obtain ⟨m,c,n⟩ := writes_range i
  obtain ⟨dm,dc,dn⟩ := sep
  unfold writeLeaf compressAt
  dsimp only
  apply Eq.trans (store_away _ _ _ _ _ n valid dn)
  apply Eq.trans (store_away _ _ _ _ _ (by omega) valid (by omega))
  apply Eq.trans (store_away _ _ _ _ _ (by omega) valid (by omega))
  exact store_away _ _ _ _ _ (by omega) valid (by omega)

private theorem node_geometry (i : Nat) : nodeAddress 0 i = 4294971424+gapOffset i := by
  unfold nodeAddress; rw [show levelOffset 0 = 0 by decide, Nat.add_zero]

theorem future_entry (i j : Index) (lt : i.val < j.val) :
    Separate i (msgAddr j) 256 := by
  have hi := i.isLt; have hj := j.isLt
  change i.val < 16777216 at hi; change j.val < 16777216 at hj
  constructor <;> simp only [msgAddr, contentAddr, rowAddr, rowBase, node_geometry, gapOffset] <;> omega

theorem future_pad (i j : Index) (lt : i.val < j.val) : Separate i (padAddr j) 8 := by
  have hi := i.isLt; have hj := j.isLt
  change i.val < 16777216 at hi; change j.val < 16777216 at hj
  constructor <;> simp only [padAddr, contentAddr, rowAddr, rowBase, msgAddr, node_geometry, gapOffset] <;>
    split <;> omega

theorem salt_separate (i j : Index) : Separate i (saltAddress j) 24 := by
  have hi := i.isLt; have hj := j.isLt
  change i.val < 16777216 at hi; change j.val < 16777216 at hj
  constructor <;> simp only [saltAddress, contentAddr, rowAddr, rowBase, msgAddr, node_geometry, gapOffset] <;>
    split <;> omega

theorem previous_node (i j : Index) (lt : j.val < i.val) : Separate i (nodeAddress 0 j) 32 := by
  have hi := i.isLt; have hj := j.isLt
  change i.val < 16777216 at hi; change j.val < 16777216 at hj
  constructor <;> simp only [msgAddr, contentAddr, rowAddr, rowBase, node_geometry, gapOffset] <;> omega

end CommitGolfCandidate.Late
