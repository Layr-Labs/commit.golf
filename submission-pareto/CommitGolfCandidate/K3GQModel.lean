import CommitGolfCandidate.TaggedPinnedModel
import CommitGolfCandidate.ProjectedCompression

/-!
# The quartet call with a parity-dependent node, and the width of each upper-tree node

Quartet group `g` (leaves `4g .. 4g+3`) hashes the record window `0^72 ‖ d0 d1 d2 d3`: the payload
(`d0` in its low bits) in bits `576..1600` and zeros in bits `0..576`. Its node is the call's reply
bytes `0..32` for even `g` and bytes `168..200` for odd `g` (the odd quartet's block sits 200 bytes below
the even one and both calls reuse their output pointer, so the two nodes abut as `node_odd ‖ node_even`).

Above the group nodes (heap nodes `2^22 + g`), the parent stored at heap node `n` keeps `nodeKeep n` of
its compression output: all 256 bits at level 21, the low 240 bits at levels 17..20, the low 238 bits
at the root and levels 1..16.
-/

namespace TwoPermutationPrototype.Sampling
open CommitGolf
open CommitGolfCandidate (low240)
open CommitGolfCandidate.ShortTree (padLow low240_padLow)
set_option maxRecDepth 8192
set_option exponentiation.threshold 2050

/-- The quartet window: zeros in bits `0..576`, the payload in bits `576..1600`. -/
def quartetEncode (payload : BitVec 1024) : Block := payload ++ (0 : BitVec 576)

theorem quartet_encode_injective : Function.Injective quartetEncode := by
  intro x y eq
  have slice := congrArg (fun input : BitVec 1600 => input.extractLsb' 576 1024) eq
  simpa only [quartetEncode, BitVec.extractLsb'_append_eq_left] using slice

/-- The node of quartet group `g`: reply bytes `0..32` for even `g`, bytes `168..200` for odd `g`. -/
def quartetNode (group : Nat) (reply : Block) : BitVec 256 :=
  if group % 2 = 0 then reply.extractLsb' 0 256 else reply.extractLsb' 1344 256

theorem quartet_node_parity (group : Nat) (reply : Block) :
    quartetNode (group % 2) reply = quartetNode group reply := by
  unfold quartetNode
  rw [Nat.mod_mod]

theorem quartet_node_even {group : Nat} (even : group % 2 = 0) (reply : Block) :
    quartetNode group reply = outputDigest reply := by
  unfold quartetNode
  rw [if_pos even]
  try rfl

theorem quartet_node_odd {group : Nat} (odd : group % 2 = 1) (reply : Block) :
    quartetNode group reply = reply.extractLsb' 1344 256 := by
  have notEven : ¬ group % 2 = 0 := by omega
  unfold quartetNode
  rw [if_neg notEven]

/-! ### Upper-tree node widths -/

/-- A digest cut to its low 238 bits (bits `238..256` zero). -/
def pad238 (x : BitVec 256) : BitVec 256 := (0 : BitVec 18) ++ x.extractLsb' 0 238

/-- What the parent stored at heap node `node` keeps of its compression output: level 21
(`[2^21, 2^22)`) all 256 bits, levels 17..20 (`[2^17, 2^21)`) the low 240 bits (`padLow`), the root
and levels 1..16 (`[1, 2^17)`) the low 238 bits. -/
def nodeKeep (node : Nat) (x : BitVec 256) : BitVec 256 :=
  if 2^21 ≤ node then x else if 2^17 ≤ node then padLow x else pad238 x

theorem node_keep_full {node : Nat} (level : 2^21 ≤ node) (x : BitVec 256) : nodeKeep node x = x := by
  unfold nodeKeep
  rw [if_pos level]

theorem node_keep_240 {node : Nat} (low : 2^17 ≤ node) (high : node < 2^21) (x : BitVec 256) :
    nodeKeep node x = padLow x := by
  have notFull : ¬ 2^21 ≤ node := by omega
  unfold nodeKeep
  rw [if_neg notFull, if_pos low]

theorem node_keep_238 {node : Nat} (level : node < 2^17) (x : BitVec 256) : nodeKeep node x = pad238 x := by
  have notFull : ¬ 2^21 ≤ node := by omega
  have notMid : ¬ 2^17 ≤ node := by omega
  unfold nodeKeep
  rw [if_neg notFull, if_neg notMid]

private theorem low238_of_low240_bits {x y : BitVec 256} (same : low240 x = low240 y) :
    x.extractLsb' 0 238 = y.extractLsb' 0 238 := by
  have raw := congrArg BitVec.toNat same
  simp only [low240, BitVec.extractLsb'_toNat, Nat.shiftRight_zero] at raw
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  have dvd : (2 : Nat)^238 ∣ 2^240 := Nat.pow_dvd_pow 2 (by norm_num)
  rw [← Nat.mod_mod_of_dvd x.toNat dvd, ← Nat.mod_mod_of_dvd y.toNat dvd, raw]

/-- Every node width keeps at least the low 238 bits: equal kept nodes agree there. -/
theorem node_keep_low238 (node : Nat) {x y : BitVec 256} (same : nodeKeep node x = nodeKeep node y) :
    x.extractLsb' 0 238 = y.extractLsb' 0 238 := by
  unfold nodeKeep at same
  split at same
  · exact congrArg (fun d : BitVec 256 => d.extractLsb' 0 238) same
  · split at same
    · exact low238_of_low240_bits ((low240_padLow x).symm.trans ((congrArg low240 same).trans (low240_padLow y)))
    · have low := congrArg (fun d : BitVec 256 => d.extractLsb' 0 238) same
      simpa only [pad238, BitVec.extractLsb'_append_eq_right] using low

end TwoPermutationPrototype.Sampling
