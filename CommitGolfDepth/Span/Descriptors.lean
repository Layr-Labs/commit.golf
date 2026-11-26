import CommitGolfDepth.Span.Memory
import CommitGolf.Parameters

/-! # Binary FORK ABI

ECALL selector t0=3 reads exactly two 64-byte child descriptors at a0. Each holds entry
PC, fuel, owned base, owned byte length, and a0 through a3. The table is snapshotted before
either child runs. Both children execute the same immutable image; no child can select
the legacy interpreter. Child registers start zero except these four arguments and sp,
which inherits the parent's sp. Registers and scheduler metadata are private model state.
After the FORK instruction, both child fuels are reserved from the remaining parent fuel.
Unused reservations are not refunded. Thus root fuel bounds total executed instructions,
including descendants; it is not a separate allowance per worker.
-/

namespace CommitGolfDepth.Span.SpanMachine
open CommitGolf RiscvZkvm.Rv64

def MAX_FORK_DEPTH : Nat := 32
def DESCRIPTOR_BYTES : Nat := 128

/-- Fixed model prices: sixteen descriptor word reads, two 32-register contexts, and
one launch vertex. Join is one synchronization vertex over shared disjoint RAM.
Permission enforcement and these primitives require a backend refinement before making
physical-cycle claims; these prices are an explicit challenge-machine choice. -/
def FORK_CYCLES : Nat := 16 + 2 * 32 + 1
def JOIN_CYCLES : Nat := 1

structure Child where
  entry : BitVec 64
  fuel : Nat
  region : Region
  arg0 : BitVec 64
  arg1 : BitVec 64
  arg2 : BitVec 64
  arg3 : BitVec 64

def readChild (s : MachineState) (base : Nat) : Child :=
  let word := fun i => s.mem (BitVec.ofNat 64 (base + 8 * i))
  ⟨word 0, (word 1).toNat, ⟨(word 2).toNat, (word 3).toNat⟩,
    word 4, word 5, word 6, word 7⟩

def Child.valid (p : Policy) (c : Child) : Bool :=
  c.region.valid && p.owned.contains c.region.base c.region.bytes &&
    p.canRead c.region.base c.region.bytes &&
    decide (0 < c.fuel ∧ c.fuel ≤ STEP_LIMIT ∧ 0x1000 ≤ c.entry.toNat ∧ c.entry.toNat % 4 = 0)

def forkChildren (p : Policy) (s : MachineState) : Option (Child × Child) :=
  let base := (s.getReg .x10).toNat
  if base % 8 = 0 ∧ p.canRead base DESCRIPTOR_BYTES = true then
    let left := readChild (readView p s) base
    let right := readChild (readView p s) (base + 64)
    if left.valid p && right.valid p && left.region.disjoint right.region then
      some (left, right)
    else none
  else none

/-- Every launched pair has disjoint, aligned owned regions inside the parent's
ownership, admissible entry PCs and bounded positive child fuel. -/
theorem forkChildren_sound (p : Policy) (s : MachineState) (left right : Child)
    (h : forkChildren p s = some (left, right)) :
    left.valid p = true ∧ right.valid p = true ∧ left.region.disjoint right.region = true := by
  unfold forkChildren at h
  dsimp only at h
  split at h
  next bounds =>
    split at h
    next valid =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      simpa only [Bool.and_eq_true, and_assoc] using valid
    next invalid => contradiction
  next bounds => contradiction

def childPolicy (parent : Policy) (own sibling : Region) : Policy :=
  ⟨own, sibling :: parent.forbidden⟩

@[simp] theorem childPolicy_inherits (p : Policy) (own sibling : Region) :
    (childPolicy p own sibling).forbidden = sibling :: p.forbidden := rfl

theorem childPolicy_sibling_hidden (p : Policy) (own sibling : Region) (a : BitVec 64)
    (h : sibling.containsWord a = true) :
    (childPolicy p own sibling).readableWord a = false := by
  apply Bool.eq_false_iff.mpr
  intro hr
  simp only [Policy.readableWord, Policy.canRead, childPolicy,
    List.all_cons, Bool.and_eq_true] at hr
  have disjoint := hr.2.1
  have apart : sibling.bytes = 0 ∨ 8 = 0 ∨ sibling.base + sibling.bytes ≤ a.toNat ∨
      a.toNat + 8 ≤ sibling.base := of_decide_eq_true disjoint
  have inside : sibling.base ≤ a.toNat ∧ a.toNat + 8 ≤ sibling.base + sibling.bytes :=
    of_decide_eq_true h
  omega

/-- Making the sibling's completed writes visible in shared RAM cannot alter the other
child's readable state. Together with `executeAtDepth_read_congr` this proves that either
canonical serialization has the same permitted child computation, with coupled coins
and the same fixed public oracle. -/
theorem childPolicy_overlay_invisible (p : Policy) (own sibling : Region)
    (parent worker : MachineState) :
    readView (childPolicy p own sibling) (overlay parent worker sibling) =
      readView (childPolicy p own sibling) parent := by
  unfold readView overlay
  congr 1
  funext a
  cases h : sibling.containsWord a with
  | false => simp [h]
  | true => simp [childPolicy_sibling_hidden p own sibling a h]

def childState (parent : MachineState) (c : Child) : MachineState :=
  let fresh := {parent with regs := fun _ => 0, pc := c.entry}
  let fresh := fresh.setReg .x2 (parent.getReg .x2)
  let fresh := fresh.setReg .x10 c.arg0
  let fresh := fresh.setReg .x11 c.arg1
  let fresh := fresh.setReg .x12 c.arg2
  fresh.setReg .x13 c.arg3

end CommitGolfDepth.Span.SpanMachine
