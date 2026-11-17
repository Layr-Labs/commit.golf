import CommitGolfCandidate.CapMultiproof

namespace CommitGolfCandidate
open CommitGolf

def capCut (compress : Compression) (lower : Nat) :
    (height : Nat) → Tree (lower + height) → Tree height
  | 0, tree => .leaf (tree.root compress)
  | height + 1, .node left right =>
      .node (capCut compress lower height left) (capCut compress lower height right)

def capLowerTree (lower : Nat) :
    (height : Nat) → Tree (lower + height) → Path height → Tree lower
  | 0, tree, .here => tree
  | height + 1, .node left _, .left path => capLowerTree lower height left path
  | height + 1, .node _ right, .right path => capLowerTree lower height right path

def capJoinPath {lower : Nat} (lowerPath : Path lower) :
    {height : Nat} → Path height → Path (lower + height)
  | 0, .here => lowerPath
  | _ + 1, .left path => .left (capJoinPath lowerPath path)
  | _ + 1, .right path => .right (capJoinPath lowerPath path)

theorem cap_cut_root (compress : Compression) (lower height : Nat)
    (tree : Tree (lower + height)) :
    (capCut compress lower height tree).root compress = tree.root compress := by
  induction height with
  | zero => rfl
  | succ height ih =>
      cases tree with
      | node left right => simp [capCut, Tree.root, ih]

theorem cap_cut_value (compress : Compression) (lower height : Nat)
    (tree : Tree (lower + height)) (path : Path height) :
    (capCut compress lower height tree).value path =
      (capLowerTree lower height tree path).root compress := by
  induction path with
  | here => rfl
  | left path ih =>
      cases tree with
      | node left right => simpa [capCut, Tree.value, capLowerTree] using ih left
  | right path ih =>
      cases tree with
      | node left right => simpa [capCut, Tree.value, capLowerTree] using ih right

theorem cap_join_value (lower height : Nat) (tree : Tree (lower + height))
    (lowerPath : Path lower) (upperPath : Path height) :
    tree.value (capJoinPath lowerPath upperPath) =
      (capLowerTree lower height tree upperPath).value lowerPath := by
  induction upperPath with
  | here => rfl
  | left path ih =>
      cases tree with
      | node left right => simpa [capJoinPath, Tree.value, capLowerTree] using ih left
  | right path ih =>
      cases tree with
      | node left right => simpa [capJoinPath, Tree.value, capLowerTree] using ih right

theorem cap_join_opening (compress : Compression) (lower height : Nat)
    (tree : Tree (lower + height)) (lowerPath : Path lower) (upperPath : Path height) :
    tree.opening compress (capJoinPath lowerPath upperPath) =
      (capLowerTree lower height tree upperPath).opening compress lowerPath ++
        (capCut compress lower height tree).opening compress upperPath := by
  induction upperPath with
  | here => simp [capJoinPath, capLowerTree, capCut, Tree.opening]
  | left path ih =>
      cases tree with
      | node left right =>
          simp only [capJoinPath, Tree.opening, capLowerTree, capCut, ih left, cap_cut_root,
            List.append_assoc]
  | right path ih =>
      cases tree with
      | node left right =>
          simp only [capJoinPath, Tree.opening, capLowerTree, capCut, ih right, cap_cut_root,
            List.append_assoc]
end CommitGolfCandidate
