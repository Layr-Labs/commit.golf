import CommitGolfCandidate.Stage3cPathAddress
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf
open CommitGolfCandidate.Chained.Binary (Field)

def levelBits : Nat→Nat | 0=>256 | d+1=>wireWidth (Binary.height d)
theorem node_width (H : Compression) (m : Message) (s : Late.SaltTape) (d j : Nat)
    (hd : d≤LOG_LENGTH) (hj : j<levelCount d) :
    (Late.node (Binary.treeM (M:=Id) H m s) d j).toNat < 2^levelBits d := by
  cases d with
  | zero=>exact BitVec.isLt _
  | succ d=>
    rw [fixed_tree_node _ _ _ _ _ hd hj]
    change (BitVec.ofNat 256 (_ % 2^wireWidth (Binary.height d))).toNat<_
    exact lt_of_le_of_lt (Nat.mod_le ..) (Nat.mod_lt _ (Nat.two_pow_pos _))

def FieldFits (f : Field) := f.value<2^f.bits

theorem record_fits (H : Compression) (m : Message) (s : Late.SaltTape) (i : Index) :
    ∀ f∈Binary.recordFields (Binary.treeM (M:=Id) H m s) s i,FieldFits f := by
  intro f mem
  rcases List.mem_cons.mp mem with rfl | mem
  · exact (s i).isLt
  · obtain ⟨d,range,rfl⟩:=List.mem_map.mp mem
    have dep:=List.mem_range.mp range
    have lt : d<LOG_LENGTH := by change d<24;omega
    have w (n : Nat) : (if n=0 then 256 else wireWidth (Binary.height (n-1)))=levelBits n := by
      cases n <;> simp [levelBits]
    change _<2^(if d=0 then _ else _)
    rw [w]
    exact node_width H m s d _ lt.le (Open.mate_bound i d lt)

theorem slot_fits (H : Compression) (m : Message) (s : Late.SaltTape) (xs : List Index) (p : Nat) (small : p<256) :
    FieldFits (Binary.slot (Binary.treeM (M:=Id) H m s) xs p) := by
  unfold FieldFits Binary.slot
  dsimp only
  split
  · split <;> apply lt_of_lt_of_eq (node_width H m s 15 _ (by decide) (by change _<512;omega)) <;> decide
  · exact node_width H m s 16 p (by decide) small
end CommitGolfCandidate.Chained.BinaryMachine
