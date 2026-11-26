import CommitGolfCandidate.LateLeafRun
import CommitGolfCandidate.LateLeafFrame

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

structure LeafContents (h : Compression) (m : Message) (salt : SaltTape) (k : Nat) (s : MachineState) : Prop where
  stored : ∀ j : Index, j.val < k →
    readBuffer s (nodeAddress 0 j) 32 = leaf h (j.val.testBit 0) (salt j) (m j)
  message : ∀ j : Index, k ≤ j.val → readBuffer s (msgAddr j) 256 = m j
  pad : ∀ j : Index, k ≤ j.val → readBuffer s (padAddr j) 8 = 0
  salts : ∀ j : Index, readBuffer s (saltAddress j) 24 = salt j

private theorem reads_valid (j : Index) : nodeAddress 0 j+32 ≤ 2^64 ∧ msgAddr j+256 ≤ 2^64 ∧
    padAddr j+8 ≤ 2^64 ∧ saltAddress j+24 ≤ 2^64 := by
  have hj := j.isLt; change j.val < 16777216 at hj
  have zero : levelOffset 0 = 0 := by decide
  simp only [nodeAddress, zero, msgAddr, padAddr, saltAddress, rowAddr, rowBase, gapOffset]
  split <;> omega

theorem leaf_contents_step (h : Compression) (m : Message) (salt : SaltTape) (i : Index)
    (s : MachineState) (old : LeafContents h m salt i s) :
    LeafContents h m salt (i.val+1) (writeLeaf h s i) := by
  constructor
  · intro j lt
    by_cases same : j = i
    · subst j
      exact write_leaf_digest h s i _ _ (old.message _ le_rfl) (old.pad _ le_rfl) (old.salts _)
    · have ne : j.val ≠ i.val := fun e => same (Fin.ext e)
      have prev : j.val < i.val := by omega
      exact (write_leaf_frame h s i _ 32 (reads_valid j).1 (previous_node i j prev)).trans (old.stored _ prev)
  · intro j next
    exact (write_leaf_frame h s i _ 256 (reads_valid j).2.1 (future_entry i j (by omega))).trans
      (old.message _ (by omega))
  · intro j next
    exact (write_leaf_frame h s i _ 8 (reads_valid j).2.2.1 (future_pad i j (by omega))).trans
      (old.pad _ (by omega))
  · intro j
    exact (write_leaf_frame h s i _ 24 (reads_valid j).2.2.2 (salt_separate i j)).trans (old.salts _)

theorem contents_congr {h : Compression} {m : Message} {salt : SaltTape} {k : Nat}
    {s t : MachineState} (same : s.mem = t.mem) (c : LeafContents h m salt k t) :
    LeafContents h m salt k s :=
  ⟨fun j hj => (read_congr_mem s t _ _ same).trans (c.stored j hj),
   fun j hj => (read_congr_mem s t _ _ same).trans (c.message j hj),
   fun j hj => (read_congr_mem s t _ _ same).trans (c.pad j hj),
   fun j => (read_congr_mem s t _ _ same).trans (c.salts j)⟩

theorem executed_leaf_contents (h : Compression) (m : Message) (salt : SaltTape) (s : MachineState)
    (tile : Nat) (i : Fin 32) (inside : 32*tile+i.val < LENGTH)
    (regs : LeafRegs s tile i) (old : LeafContents h m salt (32*tile+i.val) s) :
    LeafContents h m salt (32*tile+i.val+1) (finalLeafState h s tile i) :=
  contents_congr (leaf_state_memory h s tile i regs)
    (leaf_contents_step h m salt ⟨_,inside⟩ s old)

end CommitGolfCandidate.Late
