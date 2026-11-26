import CommitGolfCandidate.LateTreeMemory
import CommitGolfCandidate.LateFixed

namespace CommitGolfCandidate.Late
open CommitGolf

def parents (h : Compression) (xs : List Digest) : List Digest := parentsM (M := Id) h xs

theorem parent_length (h : Compression) (xs : List Digest) : (parents h xs).length = xs.length/2 := by
  match xs with
  | [] => rfl
  | [_] => change 0 = 1/2; decide
  | l::r::tail =>
    change (parents h tail).length+1 = (tail.length+1+1)/2
    rw [parent_length h tail]; omega

theorem parent_index (h : Compression) (xs : List Digest) (j : Nat) (inside : 2*j+1 < xs.length) :
    (parents h xs)[j]?.getD 0 =
      h (parentBlock (xs[2*j]?.getD 0) (xs[2*j+1]?.getD 0)) := by
  match xs, j with
  | [], _ | [_], _ => simp only [List.length_nil,List.length_cons] at inside; omega
  | _::_::_, 0 => rfl
  | l::r::tail, j+1 =>
    simp only [List.length_cons] at inside
    change (parents h tail)[j]?.getD 0 = _
    rw [parent_index h tail j (by omega)]
    rw [show 2*(j+1)=2*j+1+1 by omega,
      show 2*j+1+1+1 = (2*j+1)+1+1 by omega]
    rfl

def initialList (h : Compression) (m : Message) (salt : SaltTape) :=
  (List.finRange LENGTH).map fun i => leaf h (i.val.testBit 0) (salt i) (m i)

def layerList (h : Compression) (xs : List Digest) : Nat → List Digest
  | 0 => xs
  | n+1 => parents h (layerList h xs n)

theorem shifted (h : Compression) (xs : List Digest) (n : Nat) :
    layerList h (parents h xs) n = layerList h xs (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (parents h) ih

def cached (h : Compression) (d : Nat) (xs : List Digest) : Levels := levelsM (M := Id) h d xs

theorem stored_layer (h : Compression) (xs : List Digest) (d n : Nat) (hi : n ≤ d) :
    ((cached h d xs)[n]?).getD [] = layerList h xs n := by
  induction d generalizing xs n with
  | zero =>
    have e : n=0 := by omega
    subst n
    rfl
  | succ d ih =>
    cases n with
    | zero => rfl
    | succ n => exact (ih (parents h xs) n (by omega)).trans (shifted h xs n)

theorem width (h : Compression) (xs : List Digest) (size : xs.length=LENGTH) (n : Nat) (hi : n≤LOG_LENGTH) :
    (layerList h xs n).length = levelCount n := by
  induction n with
  | zero => exact size
  | succ n ih =>
    change (parents h (layerList h xs n)).length = _
    rw [parent_length, ih (by omega), level_successor n (by omega)]
    omega

theorem layer_node (h : Compression) (xs : List Digest) (size : xs.length=LENGTH) (n j : Nat)
    (ht : n≤LOG_LENGTH) (inside : j<levelCount n) :
    (layerList h xs n)[j]?.getD 0 = treeNode h (fun k => xs[k]?.getD 0) n j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have e := level_successor n (by omega)
    have w := width h xs size n (by omega)
    change (parents h (layerList h xs n))[j]?.getD 0 = _
    rw [parent_index h _ j (by omega),ih (2*j) (by omega) (by omega), ih (2*j+1) (by omega) (by omega)]
    rfl

attribute [local irreducible] List.finRange

theorem fixed_tree_node (h : Compression) (m : Message) (salt : SaltTape) (n j : Nat)
    (ht : n≤LOG_LENGTH) (inside : j<levelCount n) :
    node (treeM (M := Id) h m salt) n j =
      treeNode h (fun k => (initialList h m salt)[k]?.getD 0) n j := by
  have mapId {α β : Type} (xs : List α) (f : α → β) : xs.mapM (m := Id) f = xs.map f := by
    induction xs with
    | nil => rfl
    | cons a l ih => simp [List.mapM_cons,ih]; rfl
  have ls : treeM (M := Id) h m salt = levelsM (M := Id) h LOG_LENGTH (initialList h m salt) := by
    unfold treeM initialList
    rw [mapId]; rfl
  rw [ls,node]
  change ((cached h LOG_LENGTH (initialList h m salt))[n]?.getD [])[j]?.getD 0 = _
  rw [stored_layer h _ LOG_LENGTH n ht]
  exact layer_node h _ (by simp [initialList]) n j ht inside

end CommitGolfCandidate.Late
