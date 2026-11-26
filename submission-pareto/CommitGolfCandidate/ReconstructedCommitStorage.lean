import CommitGolfCandidate.ReconstructedLeafTree

namespace CommitGolfCandidate.Reconstruction.CommitStorage
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
open Generator CommitWindows LeafContent LeafModel
attribute [local irreducible] readBuffer ArtifactEncoding.decode

abbrev Trapdoor := BitVec (8*Artifact.submission.sizes.trapdoor)
def load (t : Trapdoor) (address bytes : Nat) := t.extractLsb' (8*(address-4294971424)) (8*bytes)
def trap (s : MachineState) : Trapdoor := readBuffer s 4294971424 1610612736

structure Stored (o : Oracle) (k : Key) (msg : Message) (t : Trapdoor) : Prop where
  generator : ∀ w, generatorBase-16 ≤ w → w < generatorBase+25 → w ≠ generatorBase+1 →
    load t (8*w) 8 = generatorMemory 0 0 k w
  root : load t (CommitParents.addr 0 1) 32 = Binding.pack (LeafTree.tree o k msg 0 1)
  nodes : ∀ e j, CommitParents.Cell e j → 0<e →
    load t (CommitParents.addr e j) 32 = Binding.pack (CommitParents.consumed e j (LeafTree.tree o k msg e j))

theorem slice (s : MachineState) (a bytes : Nat) (lo : 4294971424≤a) (hi : a+bytes ≤ 5905584160) :
    load (trap s) a bytes = readBuffer s a bytes := by
  have h := read_buffer_slice s 4294971424 1610612736 (a-4294971424) bytes (by omega)
  rw [show 4294971424+(a-4294971424)=a by omega] at h
  exact h

private theorem mem_word (s : MachineState) (w : Nat) : readBuffer s (8*w) 8 = memoryView s w := by
  have slice := read_buffer_slice s (8*w) 32 0 8 (by decide)
  have one := read_digest_word s (8*w) 0 (by omega) (by decide)
  simp only [Nat.mul_zero,Nat.add_zero] at slice one
  exact slice.symm.trans one

theorem packed_cell (s : MachineState) (a : Nat) : readBuffer s a 32 = Binding.pack (CommitParents.cell s a) :=
  (Binding.pack_unpack _).symm

theorem matches_state (o : Oracle) (k : Key) (msg : Message) (s t : MachineState) (m : Model)
    (fits : Fits s m) (pre : Prefix o k msg LENGTH m.mem)
    (root : CommitParents.cell t (CommitParents.addr 0 1)=LeafTree.tree o k msg 0 1)
    (nodes : ∀ e j, CommitParents.Cell e j → 0<e →
      CommitParents.cell t (CommitParents.addr e j)=CommitParents.consumed e j (LeafTree.tree o k msg e j))
    (kept : ∀ a n, a+n≤2^64 → 5637148400≤a → readBuffer t a n = readBuffer s a n) :
    Stored o k msg (trap t) := by
  constructor
  · intro w low high notCounter
    have fit : w < 2^33 := by unfold generatorBase at high; omega
    rw [slice t _ _ (by unfold generatorBase at low;omega) (by unfold generatorBase at high;omega),
      kept _ _ (by omega) (by unfold generatorBase at low;omega),mem_word]
    exact (fits.memory w fit).trans (pre.header _ low high notCounter)
  · rw [slice t _ _ (by decide) (by decide),packed_cell,root]
  · intro e j cell nonzero
    have lim := Nat.pow_le_pow_right (n:=2) (by decide) (show e+1≤25 by have := cell.1;omega)
    have C := cell.2.2
    have d := cell.1
    rw [slice t _ _ (by unfold CommitParents.addr;omega) (by unfold CommitParents.addr;omega),packed_cell,nodes _ _ cell nonzero]

end CommitGolfCandidate.Reconstruction.CommitStorage
