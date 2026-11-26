import CommitGolfCandidate.S5Model
import CommitGolfCandidate.S5Padding
namespace CommitGolfCandidate.S5Machine
open CommitGolf Chained
open Late (Digest SaltTape)

def nodeHash (H : Compression) (d : Nat) (a b c : Digest) : Digest :=
  if d=0 then H (c++b++a) else parentDigest H (S5.height d) a b

theorem chain_eval (H : Compression) (h : Height) (a b : Digest) (n : Nat) :
    S5.chainM (M:=Id) H h (b++a) n=H ((parentQueries H h a b n).getLastD 0) := by
  induction n with
  | zero=>rfl
  | succ n ih=>change H (encodeNext _ _ (S5.chainM (M:=Id) H h (b++a) n))=_
               rw [ih,parentQueries,List.getLastD_concat]

theorem parent_eval (H : Compression) (d : Nat) (xs : List Digest) (j : Nat) :
    let i:=S4.radix d*j
    S5.parentM (M:=Id) H d xs j=nodeHash H d (xs[i]?.getD 0) (xs[i+1]?.getD 0) (xs[i+2]?.getD 0) := by
  by_cases bottom : d=0
  · subst d;rfl
  · simp only [S5.parentM,nodeHash,bottom,ite_false]
    change storeReply _ (S5.chainM (M:=Id) H _ (_++_) _)=_
    rw [chain_eval];rfl

def treeNode (H : Compression) (base : Nat→Digest) : Nat→Nat→Digest
  | 0,i=>if i<levelCount 0 then base i else 0
  | d+1,i=>if i<levelCount (d+1) then nodeHash H d (treeNode H base d (S4.radix d*i))
      (treeNode H base d (S4.radix d*i+1)) (treeNode H base d (S4.radix d*i+2)) else 0

theorem missing_node (H : Compression) (base : Nat→Digest) (d i : Nat) (hi : levelCount d ≤ i) :
    treeNode H base d i=0 := by cases d <;> exact if_neg (Nat.not_lt.mpr hi)
end CommitGolfCandidate.S5Machine
