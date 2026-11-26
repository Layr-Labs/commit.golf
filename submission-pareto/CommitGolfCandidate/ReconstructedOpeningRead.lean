import CommitGolfCandidate.ReconstructedOpeningPut
import CommitGolfCandidate.ReconstructedOpeningTrap

namespace CommitGolfCandidate.Reconstruction.OpeningRead
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 OpeningPut Wire
set_option maxRecDepth 12000
attribute [local irreducible] ArtifactEncoding.decode execute

private theorem digit (s : Nat) (j : Nat) (b : Nat) (hb : b<8) :
    ((HonestStream.word s j) >>> (8*b)) % 256 = (s >>> (8*(8*j+b)))%256 := by
  have exp : 2^64 = 2^(8*b)*2^(64-8*b) := by rw [←pow_add];congr 1;omega
  have small : 8≤64-8*b := by omega
  have dv : 256 ∣ 2^(64-8*b) := Nat.pow_dvd_pow 2 small
  simp only [HonestStream.word,Nat.shiftRight_eq_div_pow]
  rw [exp,Nat.mod_mul_right_div_self,Nat.mod_mod_of_dvd _ dv,Nat.div_div_eq_div_mul,←pow_add]
  congr 3; omega

theorem byte (s : MachineState) (stream j : Nat) (valid : Serialized (memoryView s) stream)
    (inside : j<8*capacity) :
    s.getByte (BitVec.ofNat 64 (10334769248+j)) = BitVec.ofNat 8 (stream >>> (8*j)) := by
  let a := j/8
  let b := j%8
  have bounds : b<8 := by dsimp [b];omega
  have eq : 10334769248+j=8*(base+a)+b := by dsimp [a,b,base];omega
  rw [eq,aligned_byte s _ _ (by omega)]
  rw [Nat.div_eq_of_lt bounds,Nat.mul_zero,Nat.add_zero,Nat.mod_eq_of_lt bounds]
  apply BitVec.eq_of_toNat_eq
  simp only [extractByte,BitVec.truncate,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat]
  rw [Nat.mul_comm b 8]
  change ((memoryView s (base+a)).toNat >>> (8*b)) % 256 = _ 
  rw [valid a (by dsimp [a];omega),digit _ _ _ bounds,show 8*a+b=j by dsimp [a,b];omega]

/-- The proof bytes consumed by the official scheme are the packed fields, including
the final all-zero padding up to an eight-byte boundary. -/
theorem proof (r : Execution) (fs : List Field) (success : r.exit=.success)
    (length : (r.state.getReg .x11).toNat=alignedBytes (bits fs))
    (fits : alignedBytes (bits fs)≤8355061248) (memory : Serialized (memoryView r.state) (pack fs)) :
    Artifact.submission.readProof r=bytes fs := by
  have accepted : Artifact.submission.openingSucceeded r=true := by
    simp only [Submission.openingSucceeded,success,beq_self_eq_true,length]
    exact decide_eq_true (show alignedBytes (bits fs) ≤ Artifact.submission.sizes.proof from fits)
  simp only [Submission.readProof,accepted,ite_true,length,bytes]
  apply List.map_congr_left
  intro j hj
  have jb := List.mem_range.mp hj
  exact byte r.state (pack fs) j memory (by unfold capacity;omega)

/-- The honest opening loader starts with an all-zero proof arena, including all bytes
beyond a short batch. The loader table and stack are disjoint from this arena. -/
theorem initial (trap : CommitStorage.Trapdoor) (ps : Positions) (pos : 0<ps.card) :
    Serialized (memoryView (HonestInputs.first trap ps)) 0 := by
  intro j good
  have psBound : ps.card≤2^24 := by change ps.card≤LENGTH;simpa [Index] using Finset.card_le_univ ps
  change ((HonestInputs.first trap ps).getMem (BitVec.ofNat 64 (8*(base+j)))).toNat=_
  rw [HonestInputs.first_frame trap ps pos _ (by unfold base;omega) (by unfold base;unfold capacity at good;omega)]
  rw [HonestInputs.initial_zero trap ps _ (Or.inr (by unfold base;omega)) (by unfold base;unfold capacity at good;omega)]
  simp [HonestStream.word]

end CommitGolfCandidate.Reconstruction.OpeningRead
