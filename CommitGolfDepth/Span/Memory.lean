import CommitGolf.Riscv

/-! # Protected shared memory

The fork machine adds an explicit permission primitive. Permission checks and masked word
views are abstract machine operations, as bounds checks are in the original machine; this
file does not claim their implementation has constant physical running time. Ownership
endpoints are eight-byte aligned, including for byte stores, which use word read/modify/write.
Children retain inherited forbidden regions. Their registers are private; readable memory
outside their write ownership is shared read-only. Logical join reconciles disjoint owned
words; it does not copy the entire owned region.
-/

namespace CommitGolfDepth.Span.SpanMachine
open CommitGolf RiscvZkvm.Rv64

structure Region where
  base : Nat
  bytes : Nat
  deriving DecidableEq

def Region.finish (r : Region) : Nat := r.base + r.bytes

def Region.valid (r : Region) : Bool :=
  decide (r.base % 8 = 0 ∧ r.bytes % 8 = 0 ∧ r.finish ≤ Riscv.MEMORY_BYTES)

def Region.contains (r : Region) (address bytes : Nat) : Bool :=
  decide (r.base ≤ address ∧ address + bytes ≤ r.finish)

def Region.containsWord (r : Region) (address : BitVec 64) : Bool :=
  r.contains address.toNat 8

def Region.disjoint (a b : Region) : Bool :=
  decide (a.bytes = 0 ∨ b.bytes = 0 ∨ a.finish ≤ b.base ∨ b.finish ≤ a.base)

theorem Region.disjoint_words (l r : Region) (a : BitVec 64)
    (hd : l.disjoint r = true) (hl : l.containsWord a = true) :
    r.containsWord a = false := by
  have hd' : l.bytes = 0 ∨ r.bytes = 0 ∨ l.base + l.bytes ≤ r.base ∨
      r.base + r.bytes ≤ l.base := of_decide_eq_true hd
  have hl' : l.base ≤ a.toNat ∧ a.toNat + 8 ≤ l.base + l.bytes := of_decide_eq_true hl
  apply Bool.eq_false_iff.mpr
  intro hr
  have hr' : r.base ≤ a.toNat ∧ a.toNat + 8 ≤ r.base + r.bytes := of_decide_eq_true hr
  omega

structure Policy where
  owned : Region
  forbidden : List Region

def rootPolicy : Policy := ⟨⟨0, Riscv.MEMORY_BYTES⟩, []⟩

/-- No address wraparound is permitted. Empty access intersects no forbidden region. -/
def Policy.canRead (p : Policy) (address bytes : Nat) : Bool :=
  decide (address + bytes ≤ Riscv.MEMORY_BYTES) &&
    p.forbidden.all (fun r => r.disjoint ⟨address, bytes⟩)

def Policy.canWrite (p : Policy) (address bytes : Nat) : Bool :=
  p.owned.contains address bytes && decide (address + bytes ≤ Riscv.MEMORY_BYTES)

def Policy.readableWord (p : Policy) (address : BitVec 64) : Bool :=
  p.canRead address.toNat 8

/-- Whole-word closure of a byte range. Subword loads/stores access these RAM cells. -/
def wordClosure (address bytes : Nat) : Region :=
  let base := 8 * (address / 8)
  ⟨base, if bytes = 0 then 0 else 8 * ((address + bytes + 7) / 8) - base⟩

def Policy.readAccess (p : Policy) (address bytes : Nat) : Bool :=
  let words := wordClosure address bytes
  p.canRead address bytes && p.canRead words.base words.bytes

def Policy.writeAccess (p : Policy) (address bytes : Nat) : Bool :=
  let words := wordClosure address bytes
  p.canWrite address bytes && p.canWrite words.base words.bytes

theorem Policy.canRead_subrange (p : Policy) (outer length address bytes : Nat)
    (h : p.canRead outer length = true)
    (lo : outer ≤ address) (hi : address + bytes ≤ outer + length) :
    p.canRead address bytes = true := by
  have both : decide (outer + length ≤ Riscv.MEMORY_BYTES) = true ∧
      p.forbidden.all (fun r => r.disjoint ⟨outer, length⟩) = true := by
    simpa only [Policy.canRead, Bool.and_eq_true] using h
  obtain ⟨bounded, disjoint⟩ := both
  have bounded' : outer + length ≤ Riscv.MEMORY_BYTES := of_decide_eq_true bounded
  simp only [Policy.canRead, Bool.and_eq_true]
  constructor
  · exact decide_eq_true (by omega)
  · apply List.all_eq_true.mpr
    intro region member
    have apart := (List.all_eq_true.mp disjoint) region member
    have apart' : region.bytes = 0 ∨ length = 0 ∨ region.finish ≤ outer ∨
        outer + length ≤ region.base := of_decide_eq_true apart
    exact decide_eq_true (by
      change region.bytes = 0 ∨ bytes = 0 ∨ region.finish ≤ address ∨ address + bytes ≤ region.base
      omega)

/-- Access guards explicitly include each touched word, rather than relying on an
unproved implication from byte-range alignment. -/
theorem Policy.readAccess_word (p : Policy) (address bytes : Nat) (word : BitVec 64)
    (h : p.readAccess address bytes = true)
    (lo : (wordClosure address bytes).base ≤ word.toNat)
    (hi : word.toNat + 8 ≤ (wordClosure address bytes).finish) :
    p.readableWord word = true := by
  have both : p.canRead address bytes = true ∧
      p.canRead (wordClosure address bytes).base (wordClosure address bytes).bytes = true := by
    simpa only [Policy.readAccess, Bool.and_eq_true] using h
  exact p.canRead_subrange _ _ _ _ both.2 lo hi

/-- A forbidden word cannot influence instruction semantics, queries, or descriptor parsing. -/
def readView (p : Policy) (s : MachineState) : MachineState :=
  {s with mem := fun a => if p.readableWord a then s.mem a else 0}

/-- Write restriction applies to every outcome, including fault and fuel exhaustion. -/
def protectWrites (p : Policy) (before after : MachineState) : MachineState :=
  {after with mem := fun a => if p.owned.containsWord a then after.mem a else before.mem a}

@[simp] theorem readView_readable (p : Policy) (s : MachineState) (a : BitVec 64)
    (h : p.readableWord a = true) : (readView p s).mem a = s.mem a := by
  simp [readView, h]

@[simp] theorem readView_forbidden (p : Policy) (s : MachineState) (a : BitVec 64)
    (h : p.readableWord a = false) : (readView p s).mem a = 0 := by
  simp [readView, h]

/-- Permitted byte reads use precisely the same underlying word as ordinary RV64. -/
theorem readView_getByte (p : Policy) (s : MachineState) (a : BitVec 64)
    (h : p.readableWord (alignToDword a) = true) :
    (readView p s).getByte a = s.getByte a := by
  simp only [MachineState.getByte, MachineState.getMem, readView, h, ↓reduceIte]

theorem readView_getHalfword (p : Policy) (s : MachineState) (a : BitVec 64)
    (h : p.readableWord (alignToDword a) = true) :
    (readView p s).getHalfword a = s.getHalfword a := by
  simp only [MachineState.getHalfword, MachineState.getMem, readView, h, ↓reduceIte]

theorem readView_getWord32 (p : Policy) (s : MachineState) (a : BitVec 64)
    (h : p.readableWord (alignToDword a) = true) :
    (readView p s).getWord32 a = s.getWord32 a := by
  simp only [MachineState.getWord32, MachineState.getMem, readView, h, ↓reduceIte]

@[simp] theorem protectWrites_owned (p : Policy) (s t : MachineState) (a : BitVec 64)
    (h : p.owned.containsWord a = true) : (protectWrites p s t).mem a = t.mem a := by
  simp [protectWrites, h]

@[simp] theorem protectWrites_frame (p : Policy) (s t : MachineState) (a : BitVec 64)
    (h : p.owned.containsWord a = false) : (protectWrites p s t).mem a = s.mem a := by
  simp [protectWrites, h]

theorem readView_idempotent (p : Policy) (s : MachineState) :
    readView p (readView p s) = readView p s := by
  unfold readView
  congr 1
  funext a
  cases h : p.readableWord a <;> simp [h]

theorem readView_protectWrites (p : Policy) (s t : MachineState) :
    readView p (protectWrites p s t) =
      protectWrites p (readView p s) (readView p t) := by
  unfold readView protectWrites
  congr 1
  funext a
  cases h : p.readableWord a <;> cases k : p.owned.containsWord a <;> simp [h, k]

/-- The protected transition's observable next view depends only on the current permitted
view. This applies to the actual instruction/syscall transition, rather than assuming that
arbitrary effectful computations commute. -/
def protectedStep (p : Policy) (step : MachineState → MachineState) (s : MachineState) :
    MachineState := protectWrites p s (step (readView p s))

theorem protectedStep_congr (p : Policy) (step : MachineState → MachineState)
    (s t : MachineState) (h : readView p s = readView p t) :
    readView p (protectedStep p step s) = readView p (protectedStep p step t) := by
  simp only [protectedStep, readView_protectWrites, h]

/-- The parent resumes with its own registers, and only child-owned memory changes.
Under disjoint aligned ownership this is logical reconciliation of shared RAM, not a copy.
The right arm is deliberately explicit; no host-provided wiring function is accepted. -/
def merge (parent left right : MachineState) (leftRegion rightRegion : Region) : MachineState :=
  {parent with mem := fun a =>
    if leftRegion.containsWord a then left.mem a
    else if rightRegion.containsWord a then right.mem a else parent.mem a}

/-- Visibility of a completed worker's writes in shared RAM; all registers remain those
of the observer. This is a mathematical overlay, not a physical memory-copy operation. -/
def overlay (observer worker : MachineState) (region : Region) : MachineState :=
  {observer with mem := fun a => if region.containsWord a then worker.mem a else observer.mem a}

/-- Successful logical join equals either legal serialization of the disjoint writes. -/
theorem merge_serial (parent left right : MachineState) (l r : Region)
    (hd : l.disjoint r = true) :
    merge parent left right l r = overlay (overlay parent left l) right r := by
  unfold merge overlay
  congr 1
  funext a
  cases hl : l.containsWord a with
  | false => simp [hl]
  | true => simp [hl, Region.disjoint_words l r a hd hl]

theorem overlay_commute (parent left right : MachineState) (l r : Region)
    (hd : l.disjoint r = true) :
    overlay (overlay parent left l) right r = overlay (overlay parent right r) left l := by
  unfold overlay
  congr 1
  funext a
  cases hl : l.containsWord a with
  | false => simp [hl]
  | true => simp [hl, Region.disjoint_words l r a hd hl]

theorem merge_frame (parent left right : MachineState) (l r : Region) (a : BitVec 64)
    (hl : l.containsWord a = false) (hr : r.containsWord a = false) :
    (merge parent left right l r).mem a = parent.mem a := by
  simp [merge, hl, hr]

theorem merge_left (parent left right : MachineState) (l r : Region) (a : BitVec 64)
    (hl : l.containsWord a = true) : (merge parent left right l r).mem a = left.mem a := by
  simp [merge, hl]

theorem merge_right (parent left right : MachineState) (l r : Region) (a : BitVec 64)
    (hl : l.containsWord a = false) (hr : r.containsWord a = true) :
    (merge parent left right l r).mem a = right.mem a := by
  simp [merge, hl, hr]

end CommitGolfDepth.Span.SpanMachine
