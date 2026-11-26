import CommitGolfCandidate.ReconstructedOpeningTrap
import CommitGolfCandidate.ReconstructedRecordDigits

namespace CommitGolfCandidate.Reconstruction.OpeningNodes
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
open Encoding RecordDigits Binding
set_option maxRecDepth 12000
attribute [local irreducible] ArtifactEncoding.decode readBuffer

theorem sibling_cell (i : Index) (d : Fin 25) (pos : 0<d.val) : CommitParents.Cell d (sibling i d) := by
  let k := ((2^24+i.val) >>> (24-d.val))
  have n : i.val<2^24 := i.isLt
  have dd := d.isLt
  have mult : 2^d.val * 2^(24-d.val)=2^24 := by rw [←pow_add];congr 1;omega
  have upper : 2^(d.val+1) * 2^(24-d.val)=2^25 := by rw [←pow_add];congr 1;omega
  have lower : 2^d.val ≤ k := by
    dsimp [k];rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 (by rw [mult];omega)
  have high : k<2^(d.val+1) := by
    dsimp [k];rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by rw [upper];omega)
  have loEven : 2^d.val=2*2^(d.val-1) := by rw [←Nat.pow_succ'];congr 1;omega
  have hiEven : 2^(d.val+1)=2*2^d.val := Nat.pow_succ'
  change d.val≤24 ∧ 2^d.val≤ k ^^^ 1 ∧ k ^^^ 1 < 2^(d.val+1)
  by_cases e : k%2=0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr e)];omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))];omega

def raw (t : CommitStorage.Trapdoor) (d j : Nat) := Binding.unpack (CommitStorage.load t (CommitParents.addr d j) 32)

theorem from_abi (t : CommitStorage.Trapdoor) (ps : Positions) (h : 0<ps.card) (d j : Nat) (b : CommitParents.Cell d j) :
    Binding.unpack (readBuffer (HonestInputs.first t ps) (CommitParents.addr d j) 32) = raw t d j := by
  rw [OpeningTrap.first_cell t ps h d j b];rfl

theorem raw_of_stored (o : Oracle) (key : Generator.Key) (msg : Message) (t : CommitStorage.Trapdoor)
    (st : CommitStorage.Stored o key msg t) (d j : Nat) (bound : CommitParents.Cell d j) (positive : 0<d) :
    raw t d j=CommitParents.consumed d j (LeafTree.tree o key msg d j) := by
  rw [raw,st.nodes d j bound positive,Binding.unpack_pack]

private theorem top_mask (x : Binding.Digest) (d : Fin 25) (p : 0<d.val) (side : Bool) (can : Canonical d x) :
    (marked d side x).2.toNat%2^(width d-192)=x.2.toNat := by
  have lim := can.trans_le (ranges d d.isLt).1
  have cleared : ∀ i : Fin 25, 0 < i.val → ∀ s : Bool,
      (childMask i s).toNat%2^(width i-192)=0 := by decide
  simp only [marked,BitVec.toNat_or,Nat.or_mod_two_pow,cleared d p side,Nat.or_zero,Nat.mod_eq_of_lt lim]

theorem fields (o : Oracle) (key : Generator.Key) (msg : Message) (t : CommitStorage.Trapdoor)
    (st : CommitStorage.Stored o key msg t) (d : Fin 25) (j : Nat) (bound : CommitParents.Cell d j) (pos : 0<d.val) :
    let source := raw t d j
    let node := LeafTree.tree o key msg d j
    source.1=node.1 ∧ source.2.toNat%2^(lows d-192)=node.2.toNat%2^(lows d-192) ∧
      ((source.2.toNat%2^(width d-192)) >>> (lows d-192))=highDigit node (lows d) := by
  have good : Canonical d (LeafTree.tree o key msg d j) :=
    CommitParents.node_canonical _ _ _ _ bound.1 (LeafTree.canonical o key msg)
  have fit : lows d-192≤width d-192 := (by decide : ∀ b : Fin 25, lows b-192≤width b-192) d
  have clean := top_mask (LeafTree.tree o key msg d j) d pos (j%2=1) good
  rw [raw_of_stored o key msg t st d j bound pos]
  refine ⟨rfl,?_,congrArg (fun n : Nat => n >>> (lows d-192)) clean⟩
  exact (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 fit)).symm.trans (congrArg (· % 2^(lows d-192)) clean)

end CommitGolfCandidate.Reconstruction.OpeningNodes
