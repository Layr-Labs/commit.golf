import CommitGolfCandidate.ReconstructedCapGlobal
import CommitGolfCandidate.ReconstructedCapSchedule

namespace CommitGolfCandidate.Reconstruction.CapEvidence
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningPut OpeningCursor
open TwoPermutationPrototype.RV64
open HonestSizeRows (Rows)
open CapEmitNode (outside)
set_option maxRecDepth 16000

structure Buffer (s : MachineState) (fs : List Wire.Field) : Prop where
  cursor : s.getReg .x7=W (Wire.bits fs)
  output : Serialized (memoryView s) (Wire.pack fs)

theorem serial (s : MachineState) (m : Model) (fit : Fits s m) (fs : List Wire.Field) (valid : Serialized m.mem (Wire.pack fs)) :
    Serialized (memoryView s) (Wire.pack fs) := by
  intro j bound
  rw [fit.memory (base+j) (by unfold base;unfold capacity at bound;omega)]
  exact valid j bound

theorem direct (s t : MachineState) (fs : List Wire.Field) (old : Buffer s fs) (cursor : t.getReg .x7=s.getReg .x7)
    (same : ∀ j, j<capacity → memoryView t (base+j)=memoryView s (base+j)) : Buffer t fs := by
  refine ⟨cursor.trans old.cursor,?_⟩
  intro j inside;rw [same _ inside];exact old.output j inside

theorem slots_of_outside (s t : MachineState) (xs : List Nat) (sz : xs.length≤512) (old : CapSlots.Contains (memoryView s) xs)
    (same : ∀ q, q<2^33 → outside q → memoryView t q=memoryView s q) : CapSlots.Contains (memoryView t) xs := by
  intro j
  have bound := j.isLt
  have mem := same (CapSlots.cell j.val) (by change 8589934272+j.val/2<2^33;omega)
    (Or.inr (by change 1291846156+1044382656 < 8589934272+j.val/2;omega))
  exact (congrArg (fun w => extractWord32 w (CapSlots.half j.val)) mem).trans (old j)

theorem byte_of_outside (s t : MachineState) (k : Nat) (small : k<1024)
    (same : ∀ q, q<2^33 → outside q → memoryView t q=memoryView s q) :
    HonestFlagState.atByte t k=HonestFlagState.atByte s k := by
  let n := 4259840+k
  have hi : n<4260864 := by dsimp [n];omega
  have addr : W (8*(n/8)+n%8)=W n := congrArg W (Nat.div_add_mod n 8)
  have bytes (u : MachineState) : HonestFlagState.atByte u k=extractByte (memoryView u (n/8)) (n%8) := by
    change u.getByte (W n)=_
    rw [←addr,aligned_byte u (n/8) (n%8) (by omega)]
    simp only [Nat.div_eq_of_lt (show n%8<8 by omega),Nat.add_zero,Nat.mul_zero,Nat.mod_mod];rfl
  rw [bytes t,bytes s,same _ (by omega) (Or.inl (by unfold base;omega))]

theorem rows_of_outside (s t : MachineState) (f : Nat→Bool) (d j : Nat) (small : HonestCapPlan.pairs d≤256)
    (rows : Rows f d j s) (same : ∀ q, q<2^33 → outside q → memoryView t q=memoryView s q) : Rows f d j t :=
  HonestSizeRows.carry rows small (fun k hr => byte_of_outside s t k hr same)

theorem actual_regs (s : MachineState) (m : Model) (fit : Fits s m) (r : Reg) (v : Word) (eq : m.reg r=v) : s.getReg r=v :=
  (fit.registers r).trans eq

end CommitGolfCandidate.Reconstruction.CapEvidence
