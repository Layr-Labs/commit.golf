import CommitGolfCandidate.R4Tree
import CommitGolfCandidate.LateTrapdoor
import CommitGolfCandidate.Probability
import CommitGolfCandidate.S4HidingTree

/-! Contract between the unchained fused commit and the 70,080-byte R4b-format opener.
The image arguments keep the specification independent of the generated artifact in
either prover's checkout. The two measured deliverables both instantiate .twentyFour. -/
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

inductive Group where
  | twelve | twentyFour
  deriving DecidableEq

def depth : Group → Nat | .twelve => 3 | .twentyFour => 4
def leaves : Group → Nat | .twelve => 12 | .twentyFour => 24

/-- Real or padded slots at height h in one full fused group, for h < depth g. -/
def slots (g : Group) (h : Nat) := if h=0 then leaves g else 2^(depth g-h)

abbrev Tape := Fin (LENGTH/2) → R4.PairRand
abbrev rootAddress : Nat := 4294971392
abbrev tdAddress : Nat := 4294971424
def tree (o : Oracle) (m : Message) (r : Tape) := S4Hiding.tree o.compression m (R4.pairSalts r)

def finalRowAddress (i : Nat) := Late.rowBase + 184*(i/2) + 88*(i%2)

def finalRow (o : Oracle) (m : Message) (r : Tape) (i : Index) : Late.Block :=
  let ab := LateHiding.prehash o.compression (m i)
  Late.finalBlock (i.val.testBit 0) (R4.pairSalts r i) ab.1 ab.2

/-- The serialized trapdoor at commit exit, before rebuilding any low node. -/
structure FusedTrapdoor (g : Group) (o : Oracle) (m : Message) (r : Tape)
    (td : Late.Trapdoor) : Prop where
  rows : ∀ i : Index, Late.slice td (finalRowAddress i.val) 96 = finalRow o m r i
  salts : ∀ i : Index, Late.slice td (Late.sharedSaltAddr i.val) 24 = R4.pairSalts r i
  stored : ∀ h, depth g ≤ h → h ≤ LOG_LENGTH → ∀ j, j < Late.levelCount h →
    Late.slice td (Late.nodeAddress h j) 32 = Late.node (tree o m r) h j
  omitted : ∀ h, h < depth g → ∀ j, j < Late.levelCount h →
    Late.slice td (Late.nodeAddress h j) 32 = 0
  gaps : ∀ h p k, Late.Padding h p k → Late.slice td (Late.unusedSlotAddr h p k) 32 = 0
  unused : ∀ a, Late.nodeAddress LOG_LENGTH 0 + 32 ≤ a → a < tdAddress+3355443200 →
    (a < Late.rowBase ∨ Late.rowBase + 184*(LENGTH/2) ≤ a) → Late.slice td a 1 = 0

/-- Same ABI and checker; commit and opening are independent image parameters. -/
def program (commit opening : Image) : Submission :=
  { Late.submission with image := fun
      | .commit => commit
      | .opening => opening
      | .check => Late.submission.image .check }

def commitCalls : Nat := 78293686
def commitExec (price : Nat) (s : MachineState) : Execution := ⟨.success,s,price,commitCalls⟩

def Final (g : Group) (o : Oracle) (m : Message) (r : Tape) (s : MachineState) : Prop :=
  readBuffer s rootAddress 32 = Late.node (tree o m r) LOG_LENGTH 0 ∧
  FusedTrapdoor g o m r (readBuffer s tdAddress 3355443200)

/-- R4a's phase-0 register and memory contract, expressed without importing its
proof of the old downstream commit loop. One 40-byte draw is identified per pair. -/
structure AfterDraw (m : Message) (r : Tape) (s : MachineState) : Prop where
  pc : s.pc = BitVec.ofNat 64 (4096+4*32797)
  db : s.getReg .x2 = BitVec.ofNat 64 (2^36)
  mode : s.getReg .x5 = 0
  msg : s.getReg .x8 = 4096
  td : s.getReg .x9 = BitVec.ofNat 64 tdAddress
  cursor : s.getReg .x10 = 3840
  width : s.getReg .x11 = 96
  kind : s.getReg .x13 = 0
  row : s.getReg .x18 = BitVec.ofNat 64 Late.rowBase
  stop : s.getReg .x19 = BitVec.ofNat 64 (4096+2^32-256)
  root : s.getReg .x26 = BitVec.ofNat 64 rootAddress
  even : ∀ j : Fin (LENGTH/2),
    readBuffer s (Late.rowBase+184*j.val+72) 24 = R4.pairSaltEven (r j)
  odd : ∀ j : Fin (LENGTH/2),
    readBuffer s (Late.rowBase+184*j.val+88) 24 = R4.pairSaltOdd (r j)
  frame : ∀ q, q < 2^64 →
    (∀ j < LENGTH/2, q < Late.rowBase+184*j+72 ∨ Late.rowBase+184*j+112 ≤ q) →
    s.getByte (BitVec.ofNat 64 q) = (Late.submission.initialState .commit m).getByte (BitVec.ofNat 64 q)

/-- Commit prover's deterministic obligation at R4a's post-random boundary, PC word 32797.
The prefix used 16,778,266 steps, 58,721,306 cycles, and zero public queries. -/
def FixedTapeCommit (g : Group) (commit : Image) (price : Nat) : Prop :=
  ∀ o m r s, AfterDraw m r s → ∃ t, Final g o m r t ∧
    o.run (execute commit (2^40-16778266) s true) =
      pure (commitExec (price-58721306) t, commitCalls)

/-- Public commit-side result after assembling the unchanged uniform tape draw. -/
def CommitLaw (g : Group) (commit opening : Image) (price : Nat) : Prop :=
  ∀ (o : Oracle) (m : Message), ∃ state : Tape → MachineState,
    (o.run ((program commit opening).run .commit m) =ᵈ
      (($ᵗ Tape) >>= fun r => pure (commitExec price (state r), commitCalls))) ∧
    ∀ r, Final g o m r (state r)

def validCount (g : Group) (i : Index) (h : Nat) :=
  min (slots g h) (Late.levelCount h - (i.val / leaves g)*slots g h)

def perIndex (g : Group) (i : Index) :=
  (Finset.range (depth g)).sum (validCount g i)

def publicCalls (g : Group) (ps : Positions) := ps.sum (perIndex g)

def fullCost : Group → Nat | .twelve => 18 | .twentyFour => 38

theorem perIndex_le (g : Group) (i : Index) : perIndex g i ≤ fullCost g := by
  calc
    _ ≤ (Finset.range (depth g)).sum (slots g) :=
      Finset.sum_le_sum (fun h _ => Nat.min_le_left _ _)
    _ = fullCost g := by cases g <;> decide

theorem publicCalls_le (g : Group) (ps : Positions) : publicCalls g ps ≤ OPEN_BUDGET ps.card := by
  calc
    _ ≤ ps.sum (fun _ => fullCost g) := Finset.sum_le_sum (fun i _ => perIndex_le g i)
    _ = fullCost g * ps.card := by simp [Nat.mul_comm]
    _ ≤ 100 * ps.card := Nat.mul_le_mul_right _ (by cases g <;> decide : fullCost g ≤ 100)

/-- The last partial group costs eleven fewer queries per position at either depth. -/
theorem perIndex_exact (g : Group) (i : Index) :
    perIndex g i = fullCost g - (if i.val ≥ (LENGTH / leaves g) * leaves g then 11 else 0) := by
  have hi : i.val < 16777216 := i.isLt
  cases g with
  | twelve =>
    rw [perIndex,depth,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ]
    change 0 + min 12 (16777216-i.val/12*12) + min 4 (5592406-i.val/12*4) +
      min 2 (2796203-i.val/12*2) = 18 - (if i.val ≥ 16777212 then 11 else 0)
    split <;> omega
  | twentyFour =>
    rw [perIndex,depth,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ]
    change 0 + min 24 (16777216-i.val/24*24) + min 8 (5592406-i.val/24*8) +
      min 4 (2796203-i.val/24*4) + min 2 (1398102-i.val/24*2) =
      38 - (if i.val ≥ 16777200 then 11 else 0)
    split <;> omega

/-- Mathematical semantics of a rebuilt node, even for an arbitrary input trapdoor. -/
def rebuildDigest (H : Compression) (td : Late.Trapdoor) : Nat → Nat → Late.Digest
  | 0, j => if j < Late.levelCount 0 then H (Late.slice td (finalRowAddress j) 96) else 0
  | h+1, j =>
    if j < Late.levelCount (h+1) then
      let child := rebuildDigest H td h
      let k := S4.radix h * j
      let lane := fun n : Nat =>
        if n < S4.radix h ∧ k+n < Late.levelCount h then child (k+n)
        else Late.slice td (Late.unusedSlotAddr h j n) 32
      S4.retained S4.active (h+1) (H (lane 2 ++ lane 1 ++ lane 0))
    else 0

def selected (g : Group) (ps : Positions) (h j : Nat) : Prop :=
  h < depth g ∧ j < Late.levelCount h ∧ ∃ i ∈ ps, i.val / leaves g = j / slots g h

/-- Suggested opener-internal cut at word 1. Selected slots have been written; all
other trapdoor bytes agree with the input. Multiple positions may select one group. -/
structure Rebuilt (g : Group) (H : Compression) (ps : Positions)
    (before after : Late.Trapdoor) : Prop where
  nodes : ∀ h j, selected g ps h j →
    Late.slice after (Late.nodeAddress h j) 32 = rebuildDigest H before h j
  frame : ∀ a, tdAddress ≤ a → a < tdAddress+3355443200 →
    (∀ h j, selected g ps h j → a < Late.nodeAddress h j ∨ Late.nodeAddress h j+32 ≤ a) →
    Late.slice after a 1 = Late.slice before a 1

/-- The actual word-1 handoff. Observe memory by bytes (equivalently via aligned
words) and all registers, including sp. R4b word 0 was the displaced ADDI x6,x0,128. -/
def WriterEntry (g : Group) (commit opening : Image) (o : Oracle) (td : Late.Trapdoor)
    (ps : Positions) (s : MachineState) : Prop :=
  ∃ after, Rebuilt g o.compression ps td after ∧
    let initial := (program commit opening).initialState .opening (after,ps)
    s.pc = 4100 ∧ (∀ q, s.getReg q = (initial.setReg .x6 128).getReg q) ∧
    ∀ a : Nat, a < 2^36 → s.getByte (BitVec.ofNat 64 a) = initial.getByte (BitVec.ofNat 64 a)

/-- Opener prover's public contract. Termination, counts and batch time also cover
arbitrary trapdoors. Only the semantic output requires an honest fused trapdoor. -/
structure OpeningLaw (g : Group) (commit opening : Image) (batchCycles : Nat) where
  result : Oracle → Late.Trapdoor → Positions → Execution
  run : ∀ o td ps, o.run ((program commit opening).run .opening (td,ps)) =
    pure (result o td ps, publicCalls g ps)
  exit : ∀ o td ps, (result o td ps).exit = .success
  succeeded : ∀ o td ps, (program commit opening).openingSucceeded (result o td ps) = true
  counted : ∀ o td ps, (result o td ps).oracleCalls = publicCalls g ps
  price : ∀ o td (ps : Positions), ps.card = BATCH → (result o td ps).cycles ≤ batchCycles
  bytes : ∀ o m r td ps, FusedTrapdoor g o m r td →
    (program commit opening).readProof (result o td ps) = S4.actualOpening (tree o m r) (R4.pairSalts r) ps

/-- Both recommended commit images use the same opener image and contract. -/
abbrev RungAOpening (commit opening : Image) := OpeningLaw .twentyFour commit opening 136043

/-- Retarget the same proved opener without importing the other commit image. -/
def OpeningLaw.withCommit {g c op price} (law : OpeningLaw g c op price) (c' : Image) :
    OpeningLaw g c' op price where
  result := law.result
  run := law.run
  exit := law.exit
  succeeded := law.succeeded
  counted := law.counted
  price := law.price
  bytes := law.bytes

abbrev CompactSuffix (commit : Image) := FixedTapeCommit .twentyFour commit 841142282
abbrev RotatingSuffix (commit : Image) := FixedTapeCommit .twentyFour commit 840713321

/-- Assembly uses this per-tape equality with R4a's canonical opener encodings. -/
theorem sameTranscript {g commit opening price} (op : OpeningLaw g commit opening price)
    (o : Oracle) (m : Message) (r : Tape) (st : MachineState) (done_ : Final g o m r st)
    (ps : Positions) :
    (readBuffer st rootAddress 32,
      (program commit opening).readProof (op.result o (readBuffer st tdAddress 3355443200) ps)) =
    (Late.node (tree o m r) LOG_LENGTH 0, S4.actualOpening (tree o m r) (R4.pairSalts r) ps) := by
  exact Prod.ext done_.1 (op.bytes o m r _ ps done_.2)

end CommitGolfCandidate.RungA
