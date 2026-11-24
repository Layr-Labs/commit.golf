import CommitGolfCandidate.ChainedCachedField

/-! Delivered cached salts and parents satisfy the variable-width raw-field domains. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation.NonceChain
set_option maxRecDepth 8192

theorem final_value_width (h : Height) (value : Output) :
    (finalValue h value).toNat<2^(width h) := by
  have bits : value.toNat%2^(width h)<2^(width h) := Nat.mod_lt _ (by positivity)
  have upper : 2^(width h)≤2^256 := Nat.pow_le_pow_right (by decide) (by have := width_upper h; omega)
  simpa only [finalValue,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (bits.trans_le upper)] using bits

theorem parent_value_width (oracle : Oracle) (h : Height) (left right : BitVec 238) :
    (parentValue oracle h left right).toNat<2^(width h) := by
  simp only [parentValue,parentDigestTrace,check_evaluation_bind,check_evaluation_pure]
  exact final_value_width h _

theorem reference_heap_width (oracle : Oracle) (leaves : Nat → BitVec 238) (h : Height) (node : Nat)
    (lower : heightCount h≤node) (upper : node<2*heightCount h) :
    (referenceHeap oracle leaves node).toNat<2^(width h) := by
  have tree := reference_heap_tree oracle leaves h node lower upper
  have value := congrArg BitVec.toNat tree
  rw [BitVec.toNat_setWidth,Nat.mod_eq_of_lt ((referenceHeap oracle leaves node).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (by decide : 238≤256)))] at value
  rw [value]
  exact parent_value_width oracle h _ _

theorem delivered_salt_width (oracle : Oracle) (key : Key) (index : Index) :
    (deliveredSalts oracle key index).toNat<2^121 := by
  unfold deliveredSalts maskSalt saltMask
  rw [BitVec.toNat_and,BitVec.toNat_ofNat]
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

end CommitGolfCandidate.Chained.Native
