import CommitGolfCandidate.ReconstructedHonestWideRecord
import CommitGolfCandidate.ReconstructedHonestWideCap

namespace CommitGolfCandidate.Reconstruction.HonestAllRecords
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestProtected HonestNames HonestWideRecord
open HonestWideMemory (context capacity start finish)
open HonestRecordMemory (W idx constant)
open CommitBlocks (addr)

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode execute

structure Ready (n i : Nat) (s : MachineState) : Prop where
  pc : s.pc=addr 143
  numeric : Holds context start s
  cursor : s.getReg .x7=W (3633*i)
  pointer : s.getReg .x11=W (idx+8*i)
  count : s.getReg .x12=W (n-i)

def values (n i : Nat) (s : MachineState) : Values :=
  ⟨W (3633*i),W (idx+8*i),W (n-i),s.getMem (W (idx+8*i))⟩

private theorem names {n i : Nat} {s : MachineState} (h : Ready n i s) : HonestNameKernel.holds
    (values n i s) (HonestNameShapes.current 143) s := by
  refine ⟨?_,by intro _ _ h; cases h⟩
  intro r x member
  change (r,x)∈[(Reg.x7,⟨.cursor,0⟩),(.x11,⟨.indices,0⟩),(.x12,⟨.count,0⟩)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h <;> cases h
  all_goals simp only [eval,origin,values,show (0:Word)=0#64 from rfl,BitVec.add_zero]
  · exact h.cursor
  · exact h.pointer
  · exact h.count

theorem index_in (i : Nat) (hi : i<capacity) : protects context (W (idx+8*i))=true := by
  simp only [protects,HonestWideMemory.context,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true,
    Bool.and_eq_true,decide_eq_true_eq]
  right; right; right
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [idx,capacity] at *; omega)]
  dsimp [idx,capacity] at *; omega

private theorem retry {n i : Nat} {s t : MachineState} (more : i+1<n) (lim : n≤capacity)
    (pc : t.pc=addr 143) (mem : Holds context finish t)
    (incr : HonestNameKernel.holds (values n i s) HonestNameShapes.expect t) : Ready n (i+1) t := by
  have cc := incr.1 .x7 ⟨.cursor,3633⟩ (by decide +kernel)
  have pp := incr.1 .x11 ⟨.indices,8⟩ (by decide +kernel)
  have nn := incr.1 .x12 ⟨.count,18446744073709551615⟩ (by decide +kernel)
  have cur : t.getReg .x7=W (3633*(i+1)) := by
    change t.getReg .x7=W (3633*i)+W 3633 at cc
    rw [←BitVec.ofNat_add] at cc
    simpa only [Nat.mul_add,Nat.mul_one] using cc
  have ptr : t.getReg .x11=W (idx+8*(i+1)) := by
    change t.getReg .x11=W (idx+8*i)+W 8 at pp
    rw [←BitVec.ofNat_add] at pp
    simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using pp
  have cnt : t.getReg .x12=W (n-(i+1)) := by
    change t.getReg .x12=W (n-i)+18446744073709551615#64 at nn
    have h : n-i=(n-(i+1))+1 := by omega
    have add : W (n-(i+1)+1)=W (n-(i+1))+W 1 := BitVec.ofNat_add _ _
    rw [nn,h,add,BitVec.add_assoc,show W 1+18446744073709551615#64=0#64 by decide +kernel,BitVec.add_zero]
  refine ⟨pc,⟨?_,mem.2⟩,cur,ptr,cnt⟩
  intro r v hit
  have r0 := mem.1
  simp only [start,List.mem_cons,List.not_mem_nil,or_false] at hit
  rcases hit with h|h|h|h|h|h|h|h|h|h <;> cases h
  all_goals first | (apply r0; decide +kernel) | skip
  · rw [cur]; change 0≤(3633*(i+1))%2^64 ∧ (3633*(i+1))%2^64≤60951622095
    dsimp [capacity] at lim; rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [ptr]; simp only [HonestRanges.Contains,BitVec.toNat_ofNat]; change n≤16777216 at lim; change 5905584160 ≤ (5905584160+8*(i+1))%2^64 ∧ (5905584160+8*(i+1))%2^64≤5905584160+8*(16777216-1); omega
  · rw [cnt]; simp only [HonestRanges.Contains,BitVec.toNat_ofNat]; change n≤16777216 at lim; change 1≤(n-(i+1))%2^64 ∧ (n-(i+1))%2^64≤16777216; omega

theorem iteration (numeric : Numeric) (symbolic : Symbolic) (n i : Nat) (less : i<n) (bound : n≤capacity)
    (s t : MachineState) (ready : Ready n i s)
    (path : HonestCuts.Reaches HonestWideKernel.image true HonestRecordCost.cut s t) :
    (if i+1<n then Ready n (i+1) t else t.pc=addr 1429 ∧ Holds context finish t) ∧
    HonestFlagEffect.Effect s t (some (HonestNameKernel.markAddr (values n i s))) ∧
    ∀ q, protects context q=true → t.getMem q=s.getMem q := by
  have result := record numeric symbolic (values n i s) s t true ready.pc ready.numeric (names ready)
    (index_in i (by omega)) rfl path
  obtain ⟨mem,regs,which,flag,unchanged⟩ := result
  refine ⟨?_,flag,unchanged⟩
  have iffOne : (values n i s).count=1 ↔ i+1=n := by
    change W (n-i)=1 ↔ i+1=n
    have num : (W (n-i)).toNat=n-i := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [capacity] at *; omega)]
    constructor
    · intro eq; rw [eq] at num; change 1=n-i at num; omega
    · intro eq; rw [show n-i=1 by omega]; rfl
  split
  · rename_i more
    rcases which with ⟨pc,h⟩|⟨pc,h⟩
    · exact retry more bound pc mem regs
    · have := iffOne.mp h; omega
  · rename_i done_
    rcases which with ⟨pc,h⟩|⟨pc,h⟩
    · exact False.elim (h (iffOne.mpr (by omega)))
    · exact ⟨pc,mem⟩

theorem first (trap : HonestInputs.Trapdoor) (ps : Positions) (pos : 0<ps.card) :
    Ready ps.card 0 (HonestInputs.first trap ps) := by
  have h := HonestInputs.first_record trap ps pos 0
  exact ⟨h.2.1,HonestWideMemory.initial trap ps pos,h.2.2.1,h.2.2.2.2.1,h.2.2.2.1⟩

theorem budget (numeric : Numeric) (symbolic : Symbolic) (n i : Nat) (less : i<n) (bound : n≤capacity)
    (s : MachineState) (ready : Ready n i s) : HonestCapPrices.Budget s true ((n-i)*1190+54870) := by
  suffices all : ∀ k i, n-i=k → i<n → ∀ s, Ready n i s → HonestCapPrices.Budget s true (k*1190+54870)
    from all _ i rfl less s ready
  intro k
  induction k with
  | zero => intro i h less; omega
  | succ k ih =>
    intro i h less s ready
    have tail := HonestRecordCost.record_path (k*1190+54870) s ready.pc true (by
      intro t walk
      have step := (iteration numeric symbolic n i less bound s t ready walk).1
      by_cases more : i+1<n
      · rw [ite_eq_left more] at step; exact ih (i+1) (by omega) more t step
      · rw [ite_eq_right more] at step
        exact HonestCapPrices.mono (by omega) (HonestWideCap.run t step.1 step.2))
    intro f r hr; exact (tail f r hr).trans (by rw [Nat.succ_mul]; omega)

end CommitGolfCandidate.Reconstruction.HonestAllRecords
