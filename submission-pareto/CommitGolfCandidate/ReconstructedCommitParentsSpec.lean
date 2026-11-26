import CommitGolfCandidate.ReconstructedBindingChains
import CommitGolfCandidate.ReconstructedHonestWords

namespace CommitGolfCandidate.Reconstruction.CommitParents
open Binding

/-- A node as stored immediately after it is built. Residue nodes receive
their right-child label later, immediately before their parent reads them. -/
def written (d : Nat) (x : Digest) : Digest := if d = 0 then x else marked d false x

/-- The committed trapdoor retains the final decorated words, including
the extra right-child label on residue levels. -/
def consumed (d k : Nat) (x : Digest) := marked d (k%2 = 1) x

theorem written_left (d k : Nat) (hd : 0 < d) (x : Digest) :
    consumed d (2*k) x = written d x := by simp [consumed,written,Nat.ne_of_gt hd]

theorem written_ordinary (d k : Nat) (hd : 0 < d) (hm : modulus d = 0) (x : Digest) :
    consumed d k x = written d x := by
  simp [consumed,written,Nat.ne_of_gt hd,marked,childMask,hm]

/-- The hash tree uses full 256-bit intermediate replies at paid levels.
Only the last reply gets reduced to the profile's effective radix. -/
def levels (C : Compress) (leaves : Nat → Digest) : Nat → Nat → Digest
  | 0,k => leaves k
  | h+1,k => parent C (23-h) (levels C leaves h (2*k)) (levels C leaves h (2*k+1))

def node (C : Compress) (leaves : Nat → Digest) (d k : Nat) := levels C leaves (24-d) k

theorem leaf_eq (C : Compress) (leaves : Nat → Digest) (k : Nat) :
    node C leaves 24 k = leaves k := rfl

theorem parent_eq (C : Compress) (leaves : Nat → Digest) (d k : Nat) (internal : d < 24) :
    node C leaves d k = parent C d (node C leaves (d+1) (2*k)) (node C leaves (d+1) (2*k+1)) := by
  unfold node
  have len : 24-d = (24-(d+1))+1 := by omega
  rw [len,levels,show 23-(24-(d+1))=d by omega]

theorem node_canonical (C : Compress) (leaves : Nat → Digest) (d k : Nat) (valid : d ≤ 24)
    (leaf_can : ∀ k, Canonical 24 (leaves k)) : Canonical d (node C leaves d k) := by
  by_cases h : d = 24
  · subst d; exact leaf_can k
  · rw [parent_eq _ _ _ _ (by omega)]
    exact canonical_project _ _

/-- In each unrolled group the i-th binary input is 64*i bytes after the
first. The stored parent is 32*i bytes after the first output. -/
def addr (d k : Nat) := 4294971424 + 32*(k+d)

theorem aligned (d k : Nat) : addr d k % 8 = 0 := by unfold addr;omega

theorem pair_contiguous (d k : Nat) :
    addr (d+1) (2*k+1) = addr (d+1) (2*k)+32 := by unfold addr;omega

theorem parent_memory_bounds (d k : Nat) (dep : d < 24) (lo : 2^d ≤ k) (hi : k < 2^(d+1)) :
    4294971424 ≤ addr d k ∧ addr d k+64 ≤ addr (d+1) (2*k) ∧
    addr (d+1) (2*k)+64 ≤ 5637148528-128 := by
  have bound := Nat.pow_le_pow_right (n := 2) (by decide) (show d+1 ≤ 24 by omega)
  unfold addr
  omega

/-- Labels assembled by the Python emitter for ordinary narrow words. -/
def narrowMarker (d : Nat) := (d <<< 16) + 65536 - 2^(width d-224)

theorem masks_exact :
    ∀ d : Fin 25, 0 < d.val → modulus d = 0 → width d < 240 →
      childMask d false = (BitVec.ofNat 64 (narrowMarker d) <<< 32) := by decide

end CommitGolfCandidate.Reconstruction.CommitParents
