import CommitGolfCandidate.ReconstructedHonestRecordMemory

namespace CommitGolfCandidate.Reconstruction.HonestWideMemory
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestRanges HonestProtected HonestRegionStep
open HonestRecordMemory (W sp idx data proofBase constant spillValues)

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode

abbrev capacity : Nat := 16777216
theorem cardinality (ps : Positions) : ps.card ≤ capacity := by
  change ps.card ≤ LENGTH; simpa [Index] using Finset.card_le_univ ps

def fixed (q : Word) : Range :=
  if q.toNat%8=0 ∧ idx≤q.toNat ∧ q.toNat < idx+8*capacity then ⟨0,capacity-1⟩ else HonestRecordMemory.fixed q
def context : Context := ⟨[⟨sp-8,sp-8⟩,⟨sp-2312,sp-2224⟩,⟨data,data+399⟩,⟨idx,idx+8*capacity-1⟩],fixed,
  HonestRecordMemory.context.slots⟩
def Frozen (s : MachineState) := ∀ q, protects context q=true → Contains (fixed q) (s.getMem q)

theorem index_bound {s : MachineState} (frozen : Frozen s) (q : Word)
    (aligned : q.toNat%8=0) (lo : idx≤q.toNat) (hi : q.toNat < idx+8*capacity) :
    Contains (⟨0,capacity-1⟩ : Range) (s.getMem q) := by
  have known := frozen q (by
    simp only [protects,context,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    exact Or.inr (Or.inr (Or.inr ⟨lo,by omega⟩)))
  simpa only [fixed,ite_eq_left (And.intro aligned (And.intro lo hi))] using known

def start : Shape := ⟨[(.x0,constant 0),(.x2,constant (sp-2320)),(.x6,constant (sp-2160)),
  (.x7,⟨0,3633*(capacity-1)⟩),(.x8,constant sp),(.x11,⟨idx,idx+8*(capacity-1)⟩),
  (.x12,⟨1,capacity⟩),(.x22,constant 4294971424),(.x25,constant proofBase),(.x31,constant 2051)],[]⟩

def finish : Shape := ⟨[(.x0,constant 0),(.x2,constant (sp-2320)),(.x6,constant (sp-2160)),
  (.x7,⟨0,3633*capacity⟩),(.x8,constant sp),(.x11,⟨idx,idx+8*capacity⟩),
  (.x12,⟨0,capacity⟩),(.x22,constant 4294971424),(.x25,constant proofBase),(.x31,constant 2051)],[]⟩

theorem initial_index (trap : HonestInputs.Trapdoor) (ps : Positions) (pos : 0<ps.card)
    (q : Word) (aligned : q.toNat%8=0) (lo : idx≤q.toNat) (hi : q.toNat < idx+8*capacity) :
    Contains (⟨0,capacity-1⟩ : Range) ((HonestInputs.first trap ps).getMem q) := by
  let i := (q.toNat-idx)/8
  have small : i<capacity := by dsimp [i,idx,capacity] at *; omega
  have posEq : idx+8*i=q.toNat := by dsimp [i,idx] at *; omega
  have eq : q=W (idx+8*i) := by rw [posEq]; simp
  rw [eq]
  by_cases valid : i<ps.card
  · rw [HonestInputs.first_index trap ps i valid]
    have size := ((ps.sort (· ≤ ·))[i]'(by simpa using valid)).isLt
    change _ < 16777216 at size
    simp only [Contains,BitVec.toNat_ofNat,capacity]; omega
  · rw [HonestInputs.first_frame trap ps pos _ (by dsimp [idx]; omega) (by dsimp [idx,capacity] at *; omega),
      HonestInputs.initial_zero trap ps _ (Or.inr (by dsimp [idx]; omega)) (by dsimp [idx,capacity] at *; omega)]
    exact ⟨le_rfl,by decide⟩

private theorem scalar {v : Word} {n : Nat} (value : v=W n) : Contains (constant n) v := value ▸ precise _

theorem initial (trap : HonestInputs.Trapdoor) (ps : Positions) (pos : 0<ps.card) :
    Holds context start (HonestInputs.first trap ps) := by
  let s := HonestInputs.first trap ps
  have entries := HonestInputs.first_record trap ps pos 0
  have regs := HonestOpeningStart.entry_registers (HonestInputs.body trap ps)
  have extra := HonestOpeningStart.entry_constants (HonestInputs.body trap ps)
  have limit := cardinality ps
  have spill (i : Fin 12) : s.getMem (W (sp-2312+8*i.val))=W (spillValues[i.val]?.getD 0) := by fin_cases i <;> rfl
  refine ⟨?_,(by intro _ _ h; cases h),?_⟩
  · intro r v h
    simp only [start,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h|h|h|h|h|h|h|h|h <;> cases h
    · exact scalar rfl
    · exact scalar regs.2.1
    · exact scalar regs.2.2.2.1
    · rw [entries.2.2.1]; exact ⟨le_rfl,Nat.zero_le _⟩
    · exact scalar regs.2.2.1
    · rw [entries.2.2.2.2.1]; exact ⟨le_rfl,by decide⟩
    · rw [entries.2.2.2.1]; simp only [Contains,BitVec.toNat_ofNat]; dsimp [capacity] at *; omega
    · exact scalar regs.2.2.2.2.2.2.2.1
    · exact scalar regs.2.2.2.2.2.2.1
    · exact scalar extra.2.1
  · intro q region
    change Contains (fixed q) (s.getMem q)
    unfold fixed; split
    · rename_i indexed; exact initial_index trap ps pos q indexed.1 indexed.2.1 indexed.2.2
    · rename_i other
      unfold HonestRecordMemory.fixed
      by_cases align : q.toNat%8=0
      · simp only [align,ne_eq,not_true_eq_false,ite_false]
        by_cases ret : q.toNat=sp-8
        · rw [ite_eq_left ret]
          have address : q=W (sp-8) := BitVec.eq_of_toNat_eq (by rw [ret]; decide)
          rw [address]; exact scalar entries.2.2.2.2.2.2
        · rw [ite_eq_right ret]
          by_cases stack : sp-2312≤q.toNat ∧ q.toNat≤sp-2224
          · rw [ite_eq_left stack]
            let i : Fin 12 := ⟨(q.toNat-(sp-2312))/8,by dsimp [sp] at *; omega⟩
            have p : sp-2312+8*i.val=q.toNat := by
              change 68719474024+8*((q.toNat-68719474024)/8)=q.toNat
              change 68719474024≤q.toNat ∧ q.toNat≤68719474112 at stack; omega
            have a : q=W (sp-2312+8*i.val) := by rw [p]; simp
            have val := spill i; rw [←a] at val; exact scalar val
          · rw [ite_eq_right stack]
            by_cases table : data≤q.toNat ∧ q.toNat<data+400
            · rw [ite_eq_left table]
              let i := (q.toNat-data)/8
              have lim : i<50 := by dsimp [i,data] at *; omega
              by_cases low : i<25
              · change Contains (constant (if i<25 then _ else _)) (s.getMem q)
                rw [ite_eq_left low]
                have p : data+8*i=q.toNat := by dsimp [i,data] at *; omega
                have a : q=W (data+8*i) := by rw [p]; simp
                exact scalar ((congrArg s.getMem a).trans (HonestInputs.first_tables trap ps pos ⟨i,low⟩).1)
              · change Contains (constant (if i<25 then _ else _)) (s.getMem q)
                rw [ite_eq_right low]
                let j : Fin 25 := ⟨i-25,by omega⟩
                have p : data+200+8*j.val=q.toNat := by
                  change 2097152+200+8*((q.toNat-2097152)/8-25)=q.toNat
                  dsimp [i,data] at low table; omega
                have a : q=W (data+200+8*j.val) := by rw [p]; simp
                exact scalar ((congrArg s.getMem a).trans (HonestInputs.first_tables trap ps pos j).2)
            · rw [ite_eq_right table,ite_eq_right (show ¬(idx≤q.toNat ∧ q.toNat < idx+8*128) by
                intro h; exact other ⟨align,h.1,by dsimp [capacity,idx] at *; omega⟩)]
              exact arbitrary _
      · rw [ite_eq_left align]; exact arbitrary _

end CommitGolfCandidate.Reconstruction.HonestWideMemory
