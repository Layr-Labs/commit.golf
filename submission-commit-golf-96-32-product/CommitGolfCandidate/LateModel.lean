import CommitGolf.Statements
import CommitGolfCandidate.Cut

/-! One-pass honest view for the paired, late-salt binary commitment.
Bit-vector concatenation puts its right operand at the lower memory address. -/
namespace CommitGolfCandidate.Late
open CommitGolf OracleComp

abbrev Digest := BitVec 256
abbrev Salt := BitVec 192
abbrev PairCoins := BitVec 384
abbrev SaltTape := Index → Salt
abbrev Block := BitVec COMPRESSION_INPUT_LENGTH

def firstBlock (v : Entry) : Block := v.extractLsb' 0 768
def middleBlock (v : Entry) (u : Digest) : Block := v.extractLsb' 768 512 ++ u
def lastBlock (v : Entry) : Block := v.extractLsb' 1280 768

def finalBlock (odd : Bool) (s : Salt) (a b : Digest) : Block :=
  if odd then b ++ a ++ (0 : BitVec 64) ++ s
  else s ++ (0 : BitVec 64) ++ b ++ a

def leafM {M : Type → Type} [Monad M] (h : Block → M Digest)
    (odd : Bool) (s : Salt) (v : Entry) : M Digest := do
  let u ← h (firstBlock v)
  let a ← h (middleBlock v u)
  let b ← h (lastBlock v)
  h (finalBlock odd s a b)

def leaf (h : Compression) := leafM (M := Id) h

def parentBlock (l r : Digest) : Block := (0 : Digest) ++ r ++ l

/-- Byte offset within each level. Every pair occupies a 96-byte input row. -/
def gapOffset (i : Nat) := 96*(i/2) + 32*(i%2)

def pairSalts (w : PairCoins) (odd : Bool) : Salt :=
  w.extractLsb' (if odd then 192 else 0) 192

def drawPair : OracleComp World PairCoins :=
  liftM ($ᵗ PairCoins : ProbComp PairCoins)

/-- Machine order: finish the independent 48-byte draws before hashing. -/
def sampleSalts : OracleComp World SaltTape := do
  let words ← (List.range (LENGTH/2)).mapM (fun _ => drawPair)
  return fun i => pairSalts (words[i.val/2]?.getD 0) (i.val.testBit 0)

def hash (x : Block) : OracleComp World Digest :=
  liftM (World.query (.inr (.inl x)))

/-- The parents at `height` (stored in `cut` form: heights 3..17 keep their low 240 bits). -/
def parentsM {M : Type → Type} [Monad M] (h : Block → M Digest) (height : Nat) :
    List Digest → M (List Digest)
  | l :: r :: xs => do
    let p ← h (parentBlock l r)
    return cut height p :: (← parentsM h height xs)
  | _ => pure []

abbrev Levels := List (List Digest)

/-- Each internal digest is computed once and retained for later openings. -/
def levelsM {M : Type → Type} [Monad M] (h : Block → M Digest) :
    Nat → List Digest → M Levels
  | 0, layer => pure [layer]
  | d+1, layer => do
    let parents ← parentsM h (LOG_LENGTH - d) layer
    return layer :: (← levelsM h d parents)

def treeM {M : Type → Type} [Monad M] (h : Block → M Digest)
    (m : Message) (s : SaltTape) : M Levels := do
  let leaves ← (List.finRange LENGTH).mapM fun i => leafM h (i.val.testBit 0) (s i) (m i)
  levelsM h LOG_LENGTH leaves

def node (tree : Levels) (level index : Nat) : Digest :=
  ((tree[level]?).getD [])[index]?.getD 0

def bytes {n : Nat} (w : BitVec (8*n)) : List Byte :=
  List.ofFn fun i : Fin n => w.extractLsb' (8*i.val) 8

def record (tree : Levels) (s : SaltTape) (depth : Nat) (i : Index) : Proof :=
  bytes (n := 24) (s i) ++ (List.range depth).flatMap fun level =>
    bytes (n := 32) (node tree level ((i.val / 2^level) ^^^ 1))

/-- With both children present, sorted order selects the right sibling. -/
def capSlot (tree : Levels) (indices : List Index) (pair : Nat) : Digest :=
  match indices.find? (fun i => i.val / 2^17 == pair) with
  | none => node tree 17 pair
  | some i => node tree 16 ((i.val / 2^16) ^^^ 1)

/-- The sibling bytes of a batch record: levels 0..2 (heights 0..2) are full digests; levels 3..15
are the low 30 bytes of their (cut) node. -/
def batchSibling (tree : Levels) (level index : Nat) : Proof :=
  if level < 3 then bytes (n := 32) (node tree level index)
  else bytes (n := 30) (low240 (node tree level index))

/-- A batch record: 24-byte salt, 3 x 32 + 13 x 30 sibling bytes (510 bytes). -/
def batchRecord (tree : Levels) (s : SaltTape) (i : Index) : Proof :=
  bytes (n := 24) (s i) ++ (List.range 16).flatMap fun level =>
    batchSibling tree level ((i.val / 2^level) ^^^ 1)

def opening (tree : Levels) (s : SaltTape) (positions : Positions) : Proof :=
  let indices := positions.sort (· ≤ ·)
  if positions.card = BATCH then
    indices.flatMap (batchRecord tree s) ++
      (List.range 128).flatMap fun p => bytes (n := 30) (low240 (capSlot tree indices p))
  else indices.flatMap (record tree s LOG_LENGTH)

/-- The hiding experiment does not invoke its checker. The machine supplies it. -/
abbrev Checker := Commitment → (p : Positions) → Values p → Proof → OracleComp PublicSpec Bool

def scheme (check : Checker) : Scheme where
  Trapdoor := Levels × SaltTape
  commit m := do
    let s ← sampleSalts
    let tree ← treeM hash m s
    return (node tree LOG_LENGTH 0, tree, s)
  opening td p := pure (opening td.1 td.2 p)
  check := check

/-- The single abstract obligation supplied by the hiding proof. -/
def HidingGoal : Prop := ∀ check : Checker, (scheme check).Hiding HIDING_ERROR

end CommitGolfCandidate.Late
