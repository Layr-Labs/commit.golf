import CommitGolfCandidate.ReconstructedCommitStorage
import CommitGolfCandidate.ReconstructedHonestInputs

namespace CommitGolfCandidate.Reconstruction.OpeningTrap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype (window Words)
open CommitStorage CommitWindows Generator LeafContent

set_option maxRecDepth 8192
attribute [local irreducible] ArtifactEncoding.decode readBuffer

/-- Reloading the committed trapdoor through the official opening ABI reconstructs
the full little-endian buffer slice at every in-bounds byte interval. -/
theorem input_slice (t : CommitStorage.Trapdoor) (ps : Positions) (a n : Nat) (lo : 4294971424 ≤ a)
    (hi : a+n ≤ 5905584160) : readBuffer (HonestInputs.initial t ps) a n = load t a n := by
  apply read_serialized_slice
  intro j hj
  rw [show (HonestInputs.initial t ps).getByte (BitVec.ofNat 64 (a+j)) =
    inputByte Artifact.submission .opening (t,ps) (a+j) from initial_input_byte _ _ _ _ (by omega)]
  have base : Artifact.submission.layout.trapdoor=4294971424 := rfl
  have size : (8*Artifact.submission.sizes.trapdoor + 7)/8=1610612736 := rfl
  have inside : 4294971424≤a+j ∧ a+j<4294971424+1610612736 := by omega
  simp only [inputByte,Submission.inputBuffers,List.find?_cons,fixedBuffer,base,size,inside,decide_true,ite_true]
  exact congrArg (fun w => t.extractLsb' (8*w) 8) (show a+j-4294971424=a-4294971424+j by omega)

private theorem memory_word (s : MachineState) (w : Nat) : memoryView s w = readBuffer s (8*w) 8 := by
  have low := read_buffer_slice s (8*w) 32 0 8 (by decide)
  have phys := read_digest_word s (8*w) 0 (by omega) (by decide)
  simp only [Nat.mul_zero,Nat.add_zero] at low phys
  exact phys.symm.trans low

theorem first_word (t : CommitStorage.Trapdoor) (ps : Positions) (nonempty : 0<ps.card) (w : Nat)
    (lo : 4294971424≤8*w) (hi : 8*w+8≤5905584160) :
    memoryView (HonestInputs.first t ps) w = load t (8*w) 8 := by
  have frame := HonestInputs.first_frame t ps nonempty (8*w) (by omega) (by omega)
  change memoryView (HonestInputs.first t ps) w=memoryView (HonestInputs.initial t ps) w at frame
  exact frame.trans ((memory_word ..).trans (input_slice t ps _ _ lo hi))

theorem first_generator (o : Oracle) (k : Key) (msg : Message) (t : CommitStorage.Trapdoor)
    (stored : Stored o k msg t) (ps : Positions) (nonempty : 0<ps.card) :
    KeyRegion (memoryView (HonestInputs.first t ps)) k := by
  intro w lo hi except
  exact (first_word t ps nonempty w (by unfold generatorBase at lo;omega) (by unfold generatorBase at hi;omega)).trans
    (stored.generator _ lo hi except)

theorem first_cell (t : CommitStorage.Trapdoor) (ps : Positions) (nonempty : 0<ps.card) (d j : Nat)
    (bound : CommitParents.Cell d j) :
    readBuffer (HonestInputs.first t ps) (CommitParents.addr d j) 32 =
      load t (CommitParents.addr d j) 32 := by
  let a := CommitParents.addr d j
  have f := bound.2.2
  have depth := bound.1
  have limit := Nat.pow_le_pow_right (n:=2) (by decide) (show d+1≤25 by omega)
  have lo : 4294971424≤a := by dsimp [a,CommitParents.addr];omega
  have hi : a+32≤5905584160 := by dsimp [a,CommitParents.addr];omega
  have same (n : Nat) (h : n<4) : (HonestInputs.first t ps).getMem (BitVec.ofNat 64 (a+8*n)) =
      (HonestInputs.initial t ps).getMem (BitVec.ofNat 64 (a+8*n)) := HonestInputs.first_frame _ _ nonempty _ (by omega) (by omega)
  refine Eq.trans ?_ (input_slice t ps a 32 lo hi)
  change readBuffer _ a 32 = readBuffer _ a 32
  rw [read_digest_words _ _ (CommitParents.aligned d j),read_digest_words _ _ (CommitParents.aligned d j)]
  have h0 : (HonestInputs.first t ps).getMem (BitVec.ofNat 64 a) = _ := HonestInputs.first_frame _ _ nonempty _ (by omega) (by omega)
  rw [h0,same 1 (by decide),same 2 (by decide),same 3 (by decide)]

/-- The one counter write preceding a record's query makes the whole 25-word window
identical to the keyed commitment query, for every actual index. -/
theorem generate (m : TwoPermutationPrototype.Memory) (k : Key) (i : Index) (header : KeyRegion m k) :
    window (TwoPermutationPrototype.writeWord m (generatorBase+1) (BitVec.ofNat 64 (counter (tileOf i) (groupOf i))))
      (generatorBase-marker (groupOf i)) = (fun w : Fin 25 => inputWord (tileOf i) (groupOf i) k w.val) := by
  rw [←generator_window]
  funext v
  let w := generatorBase-marker (groupOf i)+v.val
  have mk : marker (groupOf i)≤16 := by unfold marker;omega
  have low : generatorBase-16≤w := by dsimp [w];omega
  have high : w<generatorBase+25 := by dsimp [w];have := v.isLt;omega
  change TwoPermutationPrototype.writeWord _ _ _ w=generatorMemory _ _ _ w
  by_cases h : w=generatorBase+1
  · rw [h]; simp [TwoPermutationPrototype.writeWord,generatorMemory]
  · simp only [TwoPermutationPrototype.writeWord,h,ite_false,header w low high h]
    simp only [generatorMemory,h,ite_false]

end CommitGolfCandidate.Reconstruction.OpeningTrap
