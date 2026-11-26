import CommitGolfCandidate.ReconstructedHonestRegionBlocks
import CommitGolfCandidate.ReconstructedHonestInputs
import CommitGolfCandidate.ReconstructedHonestRecordCost

namespace CommitGolfCandidate.Reconstruction.HonestRecordMemory
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestRanges HonestProtected HonestRegionStep
open CommitBlocks (addr)

abbrev W := BitVec.ofNat 64
abbrev sp : Nat := 68719476336
abbrev idx : Nat := 5905584160
abbrev data : Nat := 2097152
abbrev proofBase : Nat := 10334769248

def constant (n : Nat) := point (W n)

def spillValues : List Nat := [65535,2863333376,2051,536870911,1073741823,5637148520,
  8589934591,17592186044415,70368744177663,281474976710655,2147483647,4294967295]

def fixed (q : Word) : Range :=
  let n := q.toNat
  if n%8≠0 then any
  else if n=sp-8 then constant 4176
  else if sp-2312≤n ∧ n≤sp-2224 then constant (spillValues[(n-(sp-2312))/8]?.getD 0)
  else if data≤n ∧ n<data+400 then
    let i := (n-data)/8
    constant (if i<25 then sameSize.lows[i]?.getD 0 else sameSize.widths[i-25]?.getD 0)
  else if idx≤n ∧ n < idx+8*128 then ⟨0,2^24-1⟩
  else any

def context : Context := ⟨[⟨sp-8,sp-8⟩,⟨sp-2312,sp-2224⟩,⟨data,data+399⟩,⟨idx,idx+1023⟩],fixed,
  [sp-2216,sp-2208,sp-2200,sp-2192,sp-2184,sp-2176,sp-2168].map W⟩

def common (i : Nat) : RegFacts := [(.x0,constant 0),(.x2,constant (sp-2320)),(.x6,constant (sp-2160)),
  (.x7,constant (3633*i)),(.x8,constant sp),(.x11,constant (idx+8*i)),(.x12,constant (128-i)),
  (.x22,constant 4294971424),(.x25,constant proofBase),(.x31,constant 2051)]

def start (i : Nat) : Shape := ⟨common i,[]⟩

private theorem scalar {v : Word} {n : Nat} (value : v=W n) : Contains (constant n) v :=
  value ▸ precise _

theorem first_shape (trap : HonestInputs.Trapdoor) (ps : Positions) (batch : ps.card=128) :
    Holds context (start 0) (HonestInputs.first trap ps) := by
  let s := HonestInputs.first trap ps
  have pos : 0<ps.card := by omega
  have entry := HonestInputs.first_record trap ps pos 0
  have regs := HonestOpeningStart.entry_registers (HonestInputs.body trap ps)
  have extra := HonestOpeningStart.entry_constants (HonestInputs.body trap ps)
  have spill (i : Fin 12) : s.getMem (W (sp-2312+8*i.val)) = W (spillValues[i.val]?.getD 0) := by
    fin_cases i <;> rfl
  refine ⟨?_,?_,?_⟩
  · intro r v mem
    simp only [start,common,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with h|h|h|h|h|h|h|h|h|h <;> cases h
    · exact scalar rfl
    · exact scalar regs.2.1
    · exact scalar regs.2.2.2.1
    · exact scalar entry.2.2.1
    · exact scalar regs.2.2.1
    · exact scalar extra.1
    · exact scalar (by simpa only [batch] using entry.2.2.2.1)
    · exact scalar regs.2.2.2.2.2.2.2.1
    · exact scalar regs.2.2.2.2.2.2.1
    · exact scalar extra.2.1
  · intro q v mem; cases mem
  · intro q inZone
    change Contains (fixed q) (s.getMem q)
    unfold fixed
    by_cases align : q.toNat%8=0
    · simp only [align,ne_eq,not_true_eq_false,ite_false]
      by_cases ret : q.toNat=sp-8
      · rw [ite_eq_left ret]
        have address : q=W (sp-8) := BitVec.eq_of_toNat_eq (by rw [ret]; decide)
        rw [address]; exact scalar entry.2.2.2.2.2.2
      · rw [ite_eq_right ret]
        by_cases stack : sp-2312≤q.toNat ∧ q.toNat≤sp-2224
        · rw [ite_eq_left stack]
          let i : Fin 12 := ⟨(q.toNat-(sp-2312))/8,by dsimp [sp] at *; omega⟩
          have pos : sp-2312+8*i.val=q.toNat := by
            change 68719474024+8*((q.toNat-68719474024)/8)=q.toNat
            change 68719474024≤q.toNat ∧ q.toNat≤68719474112 at stack
            omega
          have address : q=W (sp-2312+8*i.val) := by rw [pos]; simp
          have value := spill i
          rw [← address] at value
          exact scalar value
        · rw [ite_eq_right stack]
          by_cases table : data≤q.toNat ∧ q.toNat<data+400
          · rw [ite_eq_left table]
            let i := (q.toNat-data)/8
            have bound : i<50 := by dsimp [i,data] at *; omega
            by_cases low : i<25
            · change Contains (constant (if i<25 then _ else _)) (s.getMem q)
              rw [ite_eq_left low]
              have p : data+8*i=q.toNat := by dsimp [i,data] at *; omega
              have a : q=W (data+8*i) := by rw [p]; simp
              have value := (HonestInputs.first_tables trap ps pos ⟨i,low⟩).1
              exact scalar ((congrArg s.getMem a).trans value)
            · change Contains (constant (if i<25 then _ else _)) (s.getMem q)
              rw [ite_eq_right low]
              let j : Fin 25 := ⟨i-25,by omega⟩
              have p : data+200+8*j.val=q.toNat := by
                change 2097152+200+8*((q.toNat-2097152)/8-25)=q.toNat
                change ¬(q.toNat-2097152)/8<25 at low
                change 2097152≤q.toNat ∧ q.toNat<2097552 at table
                omega
              have a : q=W (data+200+8*j.val) := by rw [p]; simp
              have value := (HonestInputs.first_tables trap ps pos j).2
              exact scalar ((congrArg s.getMem a).trans value)
          · rw [ite_eq_right table]
            by_cases index : idx≤q.toNat ∧ q.toNat < idx+8*128
            · rw [ite_eq_left index]
              let i := (q.toNat-idx)/8
              have bound : i<ps.card := by dsimp [i,idx] at *; omega
              have p : idx+8*i=q.toNat := by dsimp [i,idx] at *; omega
              have a : q=W (idx+8*i) := by rw [p]; simp
              have h := HonestInputs.first_index trap ps i bound
              rw [(congrArg s.getMem a).trans h]
              have size := ((ps.sort (· ≤ ·))[i]'(by simpa using bound)).isLt
              change _ < 16777216 at size
              simp only [Contains,BitVec.toNat_ofNat]
              omega
            · rw [ite_eq_right index]; exact arbitrary _
    · rw [ite_eq_left align]; exact arbitrary _

end CommitGolfCandidate.Reconstruction.HonestRecordMemory
