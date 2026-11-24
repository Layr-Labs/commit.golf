import CommitGolfCandidate.ChainedCheckerDecodedInput

/-! Actual cryptographic entry, fresh occupancy table and raw-record dispatch. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192
attribute [local irreducible] execute

inductive CheckerCryptoPart where | init | guard | records
def CheckerCryptoPart.ops : CheckerCryptoPart → List Instr
  | .init => [.ADDI .x2 .x0 1,.SLLI .x2 .x2 12,.ADDI .x3 .x0 512]
  | .guard => [.ADDI .x6 .x0 498,.ADDI .x0 .x0 0]
  | .records => [.ADDI .x8 .x13 0,.ADDI .x9 .x11 0,.ADDI .x18 .x16 0,
      .ADDI .x19 .x14 4056,.LUI .x20 4096,.ADDI .x21 .x15 0,.ADD .x22 .x15 .x17,
      .LUI .x23 3,.LUI .x24 3,.ADDI .x24 .x24 256,.LUI .x25 4,.LUI .x26 1,
      .ADDI .x27 .x0 256,.LUI .x4 3,.ADDI .x4 .x4 4080,.LUI .x3 1,.ADDI .x3 .x3 4056]
def CheckerCryptoPart.start : CheckerCryptoPart → Nat | .init => 2367 | .guard => 2374 | .records => 2378
abbrev CheckerCryptoPart.count : CheckerCryptoPart → Nat | .init => 3 | .guard => 2 | .records => 17
@[irreducible] def checkerCryptoPrefix (part : CheckerCryptoPart) (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun index before => execInstrBr before (part.ops.getD index .EBREAK)) n
theorem checker_crypto_zero (part : CheckerCryptoPart) (s : MachineState) : checkerCryptoPrefix part 0 s=s := by
  rw [checkerCryptoPrefix]; rfl
theorem checker_crypto_succ (part : CheckerCryptoPart) (n : Nat) (s : MachineState) :
    checkerCryptoPrefix part (n+1) s=execInstrBr (checkerCryptoPrefix part n s) (part.ops.getD n .EBREAK) := by
  unfold checkerCryptoPrefix; rfl
theorem checker_crypto_part_at (part : CheckerCryptoPart) :
    OpsAt chainedCheckerImage (4096+BitVec.ofNat 64 (4*part.start)) part.ops := by
  cases part
  · exact chained_checker_slice_at 2367 3 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  · exact chained_checker_slice_at 2374 2 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  · exact chained_checker_slice_at 2378 17 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem checker_crypto_prefix_pc (part : CheckerCryptoPart) (n : Nat) (s : MachineState) (small : n≤part.count) :
    (checkerCryptoPrefix part n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  have step (t : MachineState) (i : Nat) (inside : i<part.count) :
      (execInstrBr t (part.ops.getD i .EBREAK)).pc=t.pc+4 := by
    cases part <;> simp only [CheckerCryptoPart.count] at inside <;> interval_cases i <;> rfl
  induction n with
  | zero => rw [checker_crypto_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_crypto_succ,step _ _ (by omega),ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 4=BitVec.ofNat 64 (4*(n+1))
    rw [←BitVec.ofNat_add]
    congr 1
theorem checker_crypto_prefix_memory (part : CheckerCryptoPart) (n : Nat) (s : MachineState)
    (small : n≤part.count) (query : Word) : (checkerCryptoPrefix part n s).getMem query=s.getMem query := by
  have step (t : MachineState) (i : Nat) (inside : i<part.count) :
      (execInstrBr t (part.ops.getD i .EBREAK)).getMem query=t.getMem query := by
    cases part <;> simp only [CheckerCryptoPart.count] at inside <;> interval_cases i <;> rfl
  induction n with
  | zero => rw [checker_crypto_zero]
  | succ n ih => rw [checker_crypto_succ,step _ _ (by omega),ih (by omega)]
theorem checker_crypto_prefix_execution (part : CheckerCryptoPart) (s : MachineState)
    (pc : s.pc=4096+BitVec.ofNat 64 (4*part.start)) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (part.count+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerCryptoPrefix part part.count s) coins
          return result.charge part.count 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_crypto_zero part s]
  apply execute_unit_steps (states := fun n => checkerCryptoPrefix part n s)
  intro i inside
  refine ⟨.base (part.ops.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_crypto_part_at part i (by cases part <;> exact inside)
    rw [checker_crypto_prefix_pc part i s (by omega),pc]
  · rw [checker_crypto_succ]
    cases part <;> simp only [CheckerCryptoPart.count] at inside <;> interval_cases i <;> rfl
  · cases part <;> simp only [CheckerCryptoPart.count] at inside <;> interval_cases i <;> rfl

def checkerCryptoClearOps : List Instr :=
  [.SD .x2 .x0 0,.ADDI .x2 .x2 8,.ADDI .x3 .x3 4095,.BNE .x3 .x0 8180]
@[irreducible] def checkerCryptoClearPrefix (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun index before => execInstrBr before (checkerCryptoClearOps.getD index .EBREAK)) n
theorem checker_crypto_clear_zero (s : MachineState) : checkerCryptoClearPrefix 0 s=s := by rw [checkerCryptoClearPrefix]; rfl
theorem checker_crypto_clear_succ (n : Nat) (s : MachineState) : checkerCryptoClearPrefix (n+1) s=
    execInstrBr (checkerCryptoClearPrefix n s) (checkerCryptoClearOps.getD n .EBREAK) := by unfold checkerCryptoClearPrefix; rfl
theorem checker_crypto_clear_at : OpsAt chainedCheckerImage (4096+4*2370) checkerCryptoClearOps :=
  chained_checker_slice_at 2370 4 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
private theorem crypto_branch_register (s : MachineState) (reg : Reg) :
    (execInstrBr s (.BNE .x3 .x0 8180)).getReg reg=s.getReg reg := by
  change (if _ then s.setPC _ else s.setPC _).getReg reg=_
  split <;> exact MachineState.getReg_setPC
private theorem crypto_branch_memory (s : MachineState) (query : Word) :
    (execInstrBr s (.BNE .x3 .x0 8180)).getMem query=s.getMem query := by
  change (if _ then s.setPC _ else s.setPC _).getMem query=_
  split <;> exact MachineState.getMem_setPC
theorem checker_crypto_clear_pointer (s : MachineState) : (checkerCryptoClearPrefix 4 s).getReg .x2=s.getReg .x2+8 := by
  rw [checker_crypto_clear_succ]
  change (execInstrBr (checkerCryptoClearPrefix 3 s) (.BNE .x3 .x0 8180)).getReg .x2=_
  rw [crypto_branch_register,checkerCryptoClearPrefix]; rfl
theorem checker_crypto_clear_count (s : MachineState) : (checkerCryptoClearPrefix 4 s).getReg .x3=s.getReg .x3-1 := by
  rw [checker_crypto_clear_succ]
  change (execInstrBr (checkerCryptoClearPrefix 3 s) (.BNE .x3 .x0 8180)).getReg .x3=_
  rw [crypto_branch_register,checkerCryptoClearPrefix]
  change s.getReg .x3+signExtend12 4095=_
  rw [BitVec.sub_eq_add_neg]; rfl
theorem checker_crypto_clear_register (s : MachineState) (reg : Reg) (kept : reg∉[.x2,.x3]) :
    (checkerCryptoClearPrefix 4 s).getReg reg=s.getReg reg := by
  rw [checker_crypto_clear_succ]
  change (execInstrBr (checkerCryptoClearPrefix 3 s) (.BNE .x3 .x0 8180)).getReg reg=_
  rw [crypto_branch_register,checkerCryptoClearPrefix]
  cases reg <;> simp at kept <;> rfl
theorem checker_crypto_clear_memory (s : MachineState) (query : Word) :
    (checkerCryptoClearPrefix 4 s).getMem query=if query=s.getReg .x2 then 0#64 else s.getMem query := by
  rw [checker_crypto_clear_succ]
  change (execInstrBr (checkerCryptoClearPrefix 3 s) (.BNE .x3 .x0 8180)).getMem query=_
  rw [crypto_branch_memory,checkerCryptoClearPrefix]
  change (if query==s.getReg .x2+signExtend12 0 then 0#64 else s.mem query)=_
  simp only [show signExtend12 0=0#64 by rfl,BitVec.add_zero,beq_iff_eq,MachineState.getMem]
theorem checker_crypto_clear_prefix_pc (n : Nat) (s : MachineState) (small : n≤3) :
    (checkerCryptoClearPrefix n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  interval_cases n <;> rw [checkerCryptoClearPrefix]
  · exact (BitVec.add_zero _).symm
  · rfl
  · change s.pc+4+4=s.pc+8; rw [BitVec.add_assoc]; rfl
  · change s.pc+4+4+4=s.pc+12; simp only [BitVec.add_assoc]; rfl
theorem checker_crypto_clear_execution (s : MachineState) (pc : s.pc=4096+4*2370)
    (valid : accessValid (s.getReg .x2) 8=true) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (4+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerCryptoClearPrefix 4 s) coins
          return result.charge 4 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_crypto_clear_zero s]
  apply execute_unit_steps (states := fun n => checkerCryptoClearPrefix n s)
  intro i inside
  refine ⟨.base (checkerCryptoClearOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_crypto_clear_at i inside
    rw [checker_crypto_clear_prefix_pc i s (by omega),pc]
  · rw [checker_crypto_clear_succ]
    interval_cases i
    · change (if accessValid ((checkerCryptoClearPrefix 0 s).getReg .x2+0) 8 then _ else _)=_
      rw [checker_crypto_clear_zero]
      exact ite_eq_left (by simpa using valid)
    all_goals rfl
  · interval_cases i <;> rfl
theorem checker_crypto_clear_next_count (s : MachineState) (count : Nat)
    (counter : s.getReg .x3=BitVec.ofNat 64 (count+1)) :
    (checkerCryptoClearPrefix 4 s).getReg .x3=BitVec.ofNat 64 count := by
  rw [checker_crypto_clear_count,counter]
  change BitVec.ofNat 64 (count+1)-BitVec.ofNat 64 1=_
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega),Nat.add_sub_cancel]
theorem checker_crypto_clear_next_pc (s : MachineState) (count : Nat) (small : count<512)
    (pc : s.pc=4096+4*2370) (counter : s.getReg .x3=BitVec.ofNat 64 (count+1)) :
    (checkerCryptoClearPrefix 4 s).pc=if count=0 then 4096+4*2374 else 4096+4*2370 := by
  have next : (checkerCryptoClearPrefix 3 s).getReg .x3=BitVec.ofNat 64 count := by
    have same := crypto_branch_register (checkerCryptoClearPrefix 3 s) .x3
    have got := checker_crypto_clear_next_count s count counter
    rw [checker_crypto_clear_succ] at got
    exact same.symm.trans got
  rw [checker_crypto_clear_succ]
  change (if _ then (checkerCryptoClearPrefix 3 s).setPC _ else (checkerCryptoClearPrefix 3 s).setPC _).pc=_
  simp only [show (checkerCryptoClearPrefix 3 s).getReg .x0=0#64 from rfl]
  by_cases last : count=0
  · rw [ite_eq_right (by simp only [next,last]; decide)]
    change (checkerCryptoClearPrefix 3 s).pc+4=_
    rw [checker_crypto_clear_prefix_pc 3 s (by decide),pc,ite_eq_left last]; rfl
  · have different := word_of_nat_ne count 0 (by omega) (by decide) last
    rw [ite_eq_left (by simpa only [next] using bne_iff_ne.mpr different)]
    change (checkerCryptoClearPrefix 3 s).pc+signExtend13 8180=_
    rw [checker_crypto_clear_prefix_pc 3 s (by decide),pc,ite_eq_right last]; rfl

@[irreducible] def checkerCryptoClearRows : Nat → MachineState → MachineState
  | 0,s => s
  | count+1,s => checkerCryptoClearRows count (checkerCryptoClearPrefix 4 s)
theorem checker_crypto_clear_rows_zero (s : MachineState) : checkerCryptoClearRows 0 s=s := by rw [checkerCryptoClearRows]
theorem checker_crypto_clear_rows_succ (n : Nat) (s : MachineState) :
    checkerCryptoClearRows (n+1) s=checkerCryptoClearRows n (checkerCryptoClearPrefix 4 s) := by rw [checkerCryptoClearRows]
theorem checker_crypto_clear_rows_register (n : Nat) (s : MachineState) (reg : Reg) (kept : reg∉[.x2,.x3]) :
    (checkerCryptoClearRows n s).getReg reg=s.getReg reg := by
  induction n generalizing s with
  | zero => rw [checker_crypto_clear_rows_zero]
  | succ n ih => rw [checker_crypto_clear_rows_succ,ih,checker_crypto_clear_register _ _ kept]
theorem checker_crypto_clear_rows_frame (n : Nat) (s : MachineState) (query : Word)
    (away : ∀ index, index<n → query≠s.getReg .x2+BitVec.ofNat 64 (8*index)) :
    (checkerCryptoClearRows n s).getMem query=s.getMem query := by
  induction n generalizing s with
  | zero => rw [checker_crypto_clear_rows_zero]
  | succ n ih =>
    rw [checker_crypto_clear_rows_succ,ih,checker_crypto_clear_memory,ite_eq_right]
    · simpa using away 0 (by omega)
    · intro index inside
      rw [checker_crypto_clear_pointer]
      change query≠s.getReg .x2+BitVec.ofNat 64 8+BitVec.ofNat 64 (8*index)
      rw [byte_offset_add]
      convert away (index+1) (by omega) using 1
      exact congrArg (fun offset => s.getReg .x2+BitVec.ofNat 64 offset) (by omega)
theorem checker_crypto_clear_rows_execution (n base : Nat) (s : MachineState) (small : n≤512)
    (pc : s.pc=if n=0 then 4096+4*2374 else 4096+4*2370)
    (pointer : s.getReg .x2=BitVec.ofNat 64 base) (aligned : base%8=0)
    (room : base+8*n≤8192) (counter : s.getReg .x3=BitVec.ofNat 64 n) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (4*n+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerCryptoClearRows n s) coins
          return result.charge (4*n) 0) := by
  induction n generalizing s base with
  | zero => simp [checker_crypto_clear_rows_zero,Execution.charge]
  | succ n ih =>
    have valid : accessValid (s.getReg .x2) 8=true := by
      rw [pointer]
      have fit : base<2^64 := by omega
      simp [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit,MEMORY_BYTES,aligned]
      omega
    have next : (checkerCryptoClearPrefix 4 s).getReg .x2=BitVec.ofNat 64 (base+8) := by
      rw [checker_crypto_clear_pointer,pointer]; exact (BitVec.ofNat_add _ _).symm
    have here : s.pc=4096+4*2370 := by simpa using pc
    rw [show 4*(n+1)+fuel=4+(4*n+fuel) by omega,checker_crypto_clear_execution s here valid,
      ih (base+8) _ (by omega) (checker_crypto_clear_next_pc s n (by omega) here counter) next
        (by omega) (by omega) (checker_crypto_clear_next_count s n counter),←checker_crypto_clear_rows_succ]
    simp [Execution.charge,Nat.mul_succ,Nat.add_comm,Nat.add_left_comm]

theorem checker_crypto_clear_rows_content (n base : Nat) (s : MachineState)
    (pointer : s.getReg .x2=BitVec.ofNat 64 base) (room : base+8*n≤8192) :
    ∀ node, node<n → (checkerCryptoClearRows n s).getMem (BitVec.ofNat 64 (base+8*node))=0#64 := by
  induction n generalizing s base with
  | zero => intro node inside; omega
  | succ n ih =>
    intro node inside
    rw [checker_crypto_clear_rows_succ]
    have next : (checkerCryptoClearPrefix 4 s).getReg .x2=BitVec.ofNat 64 (base+8) := by
      rw [checker_crypto_clear_pointer,pointer]; exact (BitVec.ofNat_add _ _).symm
    cases node with
    | zero =>
      rw [checker_crypto_clear_rows_frame]
      · rw [checker_crypto_clear_memory,pointer]; simp
      · intro index before
        rw [next,←BitVec.ofNat_add]
        exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
    | succ node =>
      have result := ih (base+8) _ next (by omega) node (by omega)
      have address : base+8*(node+1)=(base+8)+8*node := by omega
      simpa only [address] using result
theorem checker_crypto_clear_rows_control (n : Nat) (s : MachineState) (small : n≤512)
    (pc : s.pc=if n=0 then 4096+4*2374 else 4096+4*2370) (counter : s.getReg .x3=BitVec.ofNat 64 n) :
    (checkerCryptoClearRows n s).pc=4096+4*2374 ∧ (checkerCryptoClearRows n s).getReg .x3=0#64 := by
  induction n generalizing s with
  | zero => rw [checker_crypto_clear_rows_zero]; exact ⟨by simpa using pc,counter⟩
  | succ n ih =>
    have here : s.pc=4096+4*2370 := by simpa using pc
    rw [checker_crypto_clear_rows_succ]
    exact ih _ (by omega) (checker_crypto_clear_next_pc s n (by omega) here counter) (checker_crypto_clear_next_count s n counter)

def CheckerCryptoPart.writes : CheckerCryptoPart → List Reg
  | .init => [.x2,.x3]
  | .guard => [.x6]
  | .records => [.x3,.x4,.x8,.x9,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27]
theorem checker_crypto_prefix_register (part : CheckerCryptoPart) (n : Nat) (s : MachineState)
    (small : n≤part.count) (reg : Reg) (kept : reg∉part.writes) :
    (checkerCryptoPrefix part n s).getReg reg=s.getReg reg := by
  have step (t : MachineState) (i : Nat) (inside : i<part.count) :
      (execInstrBr t (part.ops.getD i .EBREAK)).getReg reg=t.getReg reg := by
    cases part <;> simp only [CheckerCryptoPart.count] at inside
    all_goals interval_cases i <;> cases reg <;> simp [CheckerCryptoPart.writes] at kept <;> rfl
  induction n with
  | zero => rw [checker_crypto_zero]
  | succ n ih => rw [checker_crypto_succ,step _ _ (by omega),ih (by omega)]
theorem checker_crypto_init_pointer (s : MachineState) : (checkerCryptoPrefix .init 3 s).getReg .x2=4096#64 := by
  rw [checkerCryptoPrefix]; rfl
theorem checker_crypto_init_count (s : MachineState) : (checkerCryptoPrefix .init 3 s).getReg .x3=512#64 := by
  rw [checkerCryptoPrefix]; rfl
theorem checker_crypto_guard_record_size (s : MachineState) : (checkerCryptoPrefix .guard 2 s).getReg .x6=498#64 := by
  rw [checkerCryptoPrefix]; rfl
@[irreducible] def checkerCryptoClearedState (s : MachineState) : MachineState :=
  checkerCryptoClearRows 512 (checkerCryptoPrefix .init 3 s)
theorem checker_crypto_cleared_eq (s : MachineState) : checkerCryptoClearedState s=
    checkerCryptoClearRows 512 (checkerCryptoPrefix .init 3 s) := by rw [checkerCryptoClearedState]
theorem checker_crypto_cleared_execution (s : MachineState) (pc : s.pc=4096+4*2367) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2051+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerCryptoClearedState s) coins
          return result.charge 2051 0) := by
  have next : (checkerCryptoPrefix .init 3 s).pc=4096+4*2370 := by
    rw [checker_crypto_prefix_pc .init 3 s (by decide),pc]; rfl
  rw [checker_crypto_cleared_eq,show 2051+fuel=3+(4*512+fuel) by omega,
    checker_crypto_prefix_execution .init s pc,
    checker_crypto_clear_rows_execution 512 4096 _ (by decide) (by simpa using next)
      (checker_crypto_init_pointer s) (by decide) (by decide) (checker_crypto_init_count s)]
  simp [Execution.charge,←Nat.add_assoc,CheckerCryptoPart.count]
theorem checker_crypto_cleared_pc (s : MachineState) (pc : s.pc=4096+4*2367) :
    (checkerCryptoClearedState s).pc=4096+4*2374 := by
  rw [checker_crypto_cleared_eq]
  apply (checker_crypto_clear_rows_control 512 _ (by decide) ?_ (checker_crypto_init_count s)).1
  rw [checker_crypto_prefix_pc .init 3 s (by decide),pc]; rfl
theorem checker_crypto_cleared_register (s : MachineState) (reg : Reg) (kept : reg∉[.x2,.x3]) :
    (checkerCryptoClearedState s).getReg reg=s.getReg reg := by
  rw [checker_crypto_cleared_eq,checker_crypto_clear_rows_register _ _ _ kept,
    checker_crypto_prefix_register .init 3 s (by decide) reg kept]
theorem checker_crypto_cleared_content (s : MachineState) (node : Nat) (inside : node<512) :
    (checkerCryptoClearedState s).getMem (BitVec.ofNat 64 (4096+8*node))=0#64 := by
  rw [checker_crypto_cleared_eq]
  exact checker_crypto_clear_rows_content 512 4096 _ (checker_crypto_init_pointer s) (by decide) node inside
theorem checker_crypto_cleared_memory (s : MachineState) (query : Word)
    (away : ∀ node, node<512 → query≠BitVec.ofNat 64 (4096+8*node)) :
    (checkerCryptoClearedState s).getMem query=s.getMem query := by
  rw [checker_crypto_cleared_eq,checker_crypto_clear_rows_frame,
    checker_crypto_prefix_memory .init 3 s (by decide)]
  intro node inside
  rw [checker_crypto_init_pointer]
  rw [←BitVec.ofNat_add]
  exact away node inside

@[irreducible] def checkerCryptoGuardedState (s : MachineState) : MachineState :=
  (checkerCryptoPrefix .guard 2 s).setPC (4096+4*2378)
theorem checker_crypto_guarded_eq (s : MachineState) : checkerCryptoGuardedState s=
    (checkerCryptoPrefix .guard 2 s).setPC (4096+4*2378) := by rw [checkerCryptoGuardedState]
theorem checker_crypto_guarded_execution (s : MachineState) (pc : s.pc=4096+4*2374)
    (enough : ¬BitVec.ult (s.getReg .x17) 498#64) (nonempty : s.getReg .x16≠0#64) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (4+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerCryptoGuardedState s) coins
          return result.charge 4 0) := by
  let before := checkerCryptoPrefix .guard 2 s
  have firstPC : before.pc=4096+4*2376 := by rw [checker_crypto_prefix_pc .guard 2 s (by decide),pc]; rfl
  have fetch0 : fetch chainedCheckerImage before=some (.base (.BLTU .x17 .x6 1448)) :=
    chained_checker_ops_at 2376 (by rw [chained_checker_ops_length]; decide) before firstPC
  have step0 : ordinaryStep before (.base (.BLTU .x17 .x6 1448))=some (before.setPC (4096+4*2377)) := by
    change some (if BitVec.ult (before.getReg .x17) (before.getReg .x6) then _ else _)=_
    have length : before.getReg .x17=s.getReg .x17 := checker_crypto_prefix_register .guard 2 s (by decide) .x17 (by decide)
    rw [length,checker_crypto_guard_record_size,ite_eq_right enough]
    rw [firstPC]; rfl
  have fetch1 : fetch chainedCheckerImage (before.setPC (4096+4*2377))=some (.base (.BEQ .x16 .x0 1428)) :=
    chained_checker_ops_at 2377 (by rw [chained_checker_ops_length]; decide) _ (by rfl)
  have step1 : ordinaryStep (before.setPC (4096+4*2377)) (.base (.BEQ .x16 .x0 1428))=
      some (checkerCryptoGuardedState s) := by
    change some (if before.getReg .x16==0#64 then _ else _)=_
    have count : before.getReg .x16=s.getReg .x16 := checker_crypto_prefix_register .guard 2 s (by decide) .x16 (by decide)
    rw [count,ite_eq_right (by simpa only [beq_iff_eq] using nonempty),checker_crypto_guarded_eq]
    rfl
  rw [show 4+fuel=2+((fuel+1)+1) by omega,checker_crypto_prefix_execution .guard s pc,checking_manifest_image,
    execute_ordinary_step _ _ _ _ _ coins fetch0 step0,execute_ordinary_step _ _ _ _ _ coins fetch1 step1]
  simp [Execution.charge,←Nat.add_assoc,CheckerCryptoPart.count,instructionCycles]
theorem checker_crypto_guarded_register (s : MachineState) (reg : Reg) (kept : reg≠.x6) :
    (checkerCryptoGuardedState s).getReg reg=s.getReg reg := by
  rw [checker_crypto_guarded_eq,MachineState.getReg_setPC,checker_crypto_prefix_register .guard 2 s (by decide) reg]
  simpa only [CheckerCryptoPart.writes,List.mem_singleton] using kept
theorem checker_crypto_guarded_memory (s : MachineState) (query : Word) :
    (checkerCryptoGuardedState s).getMem query=s.getMem query := by
  rw [checker_crypto_guarded_eq,MachineState.getMem_setPC,checker_crypto_prefix_memory .guard 2 s (by decide)]

@[irreducible] def checkerCryptoRecordState (s : MachineState) : MachineState :=
  checkerCryptoPrefix .records 17 (checkerCryptoGuardedState (checkerCryptoClearedState s))
theorem checker_crypto_record_state_eq (s : MachineState) : checkerCryptoRecordState s=
    checkerCryptoPrefix .records 17 (checkerCryptoGuardedState (checkerCryptoClearedState s)) := by rw [checkerCryptoRecordState]
theorem checker_crypto_record_execution (s : MachineState) (pc : s.pc=4096+4*2367)
    (enough : ¬BitVec.ult (s.getReg .x17) 498#64) (nonempty : s.getReg .x16≠0#64) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2072+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerCryptoRecordState s) coins
          return result.charge 2072 0) := by
  have guardPC := checker_crypto_cleared_pc s pc
  have enough' : ¬BitVec.ult ((checkerCryptoClearedState s).getReg .x17) 498#64 := by
    rwa [checker_crypto_cleared_register s .x17 (by decide)]
  have count' : (checkerCryptoClearedState s).getReg .x16≠0#64 := by
    rwa [checker_crypto_cleared_register s .x16 (by decide)]
  rw [checker_crypto_record_state_eq,show 2072+fuel=2051+(4+(17+fuel)) by omega,checker_crypto_cleared_execution s pc,
    checker_crypto_guarded_execution _ guardPC enough' count',checker_crypto_prefix_execution .records _ (by rw [checker_crypto_guarded_eq]; rfl)]
  simp [Execution.charge,←Nat.add_assoc,CheckerCryptoPart.count]
theorem checker_crypto_record_pc (s : MachineState) : (checkerCryptoRecordState s).pc=4096+4*2395 := by
  rw [checker_crypto_record_state_eq,checker_crypto_prefix_pc .records 17 _ (by decide),checker_crypto_guarded_eq]
  rfl
theorem checker_crypto_record_kept (s : MachineState) (reg : Reg)
    (kept : reg∉[.x2,.x3,.x4,.x6,.x8,.x9,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27]) :
    (checkerCryptoRecordState s).getReg reg=s.getReg reg := by
  cases reg <;> simp at kept
  all_goals rw [checker_crypto_record_state_eq,checker_crypto_prefix_register .records 17 _ (by decide) _ (by decide),
    checker_crypto_guarded_register _ _ (by decide),checker_crypto_cleared_register _ _ (by decide)]
theorem checker_crypto_record_memory (s : MachineState) (query : Word)
    (away : ∀ node, node<512 → query≠BitVec.ofNat 64 (4096+8*node)) :
    (checkerCryptoRecordState s).getMem query=s.getMem query := by
  rw [checker_crypto_record_state_eq,checker_crypto_prefix_memory .records 17 _ (by decide),
    checker_crypto_guarded_memory,checker_crypto_cleared_memory s query away]
theorem checker_crypto_record_marks (s : MachineState) (node : Nat) (inside : node<512) :
    (checkerCryptoRecordState s).getMem (BitVec.ofNat 64 (4096+8*node))=0#64 := by
  rw [checker_crypto_record_state_eq,checker_crypto_prefix_memory .records 17 _ (by decide),
    checker_crypto_guarded_memory,checker_crypto_cleared_content s node inside]
theorem checker_crypto_record_byte (s : MachineState) (address : Nat) (above : 8192≤address) (fit : address<2^64) :
    (checkerCryptoRecordState s).getByte (BitVec.ofNat 64 address)=s.getByte (BitVec.ofNat 64 address) := by
  have aligned : (checkerCryptoRecordState s).getMem (BitVec.ofNat 64 (8*(address/8)))=
      s.getMem (BitVec.ofNat 64 (8*(address/8))) := by
    apply checker_crypto_record_memory
    intro node inside
    exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
  have small : address%8<8 := Nat.mod_lt _ (by decide)
  have joined : 8*(address/8)+address%8=address := by omega
  have after := aligned_byte (checkerCryptoRecordState s) (address/8) (address%8) (by omega)
  have before := aligned_byte s (address/8) (address%8) (by omega)
  simp only [joined,Nat.div_eq_of_lt small,Nat.mul_zero,Nat.add_zero,Nat.mod_mod] at after before
  rw [after,before,aligned]

theorem checker_decoded_record_size (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) : ¬BitVec.ult (s.getReg .x17) 498#64 := by
  have cardinal : input.positions.card≤16777216 := by
    have bound : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    exact bound
  have nodes : (checkerInputFooterNodes input).length≤256 :=
    checker_footer_frontier_count ((input.positions.sort (· ≤ ·)).map capGroup) 1 8
  have fit : (checkerInputRawRecords input).length+30*(checkerInputFooterNodes input).length<2^64 := by
    rw [checker_input_raw_records_length]
    omega
  rw [ready.length]
  simp only [BitVec.ult_iff_toNat_lt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit]
  change ¬ (checkerInputRawRecords input).length+30*(checkerInputFooterNodes input).length<498
  rw [checker_input_raw_records_length]
  omega
theorem checker_decoded_record_execution (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2072+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerCryptoRecordState s) coins
          return result.charge 2072 0) := by
  apply checker_crypto_record_execution s ready.pc (checker_decoded_record_size input nonempty footer s ready)
  have count := ready.abi ⟨3,by decide⟩
  change s.getReg .x16=(Artifact.submission.initialState .check input).getReg .x16 at count
  exact fun zero => checker_seed_input_nonempty input nonempty (count.symm.trans zero)
theorem checker_crypto_record_abi (input : CheckInput)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) (slot : Fin 4) :
    (checkerCryptoRecordState s).getReg (checkerSavedReg slot)=
      (Artifact.submission.initialState .check input).getReg (checkerSavedReg slot) := by
  rw [checker_crypto_record_kept s (checkerSavedReg slot) (by fin_cases slot <;> decide)]
  exact ready.abi slot
theorem checker_crypto_record_input_memory (input : CheckInput)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) :
    BytesAt (checkerCryptoRecordState s) (BitVec.ofNat 64 checkingRawBase)
      (checkerInputRawRecords input++rawFieldsBytes (footerRawFields (checkerInputFooterNodes input) footer)) := by
  have cardinal : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  have nodes : (checkerInputFooterNodes input).length≤256 :=
    checker_footer_frontier_count ((input.positions.sort (· ≤ ·)).map capGroup) 1 8
  have low : 8192≤checkingRawBase := by decide +kernel
  have room := checking_raw_before_metadata input.positions.card cardinal
  have metaFit := checking_metadata_room
  intro index inside
  have length : index<(checkerInputRawRecords input).length+30*(checkerInputFooterNodes input).length := by
    simpa only [List.length_append,footer_raw_fields_length] using inside
  rw [checker_input_raw_records_length] at length
  rw [←BitVec.ofNat_add,checker_crypto_record_byte s _ (by omega) (by omega)]
  have before := ready.memory index inside
  rwa [←BitVec.ofNat_add] at before
theorem checker_crypto_record_public (input : CheckInput)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) (query : Nat) (above : 8192≤query) (before : query<checkingRawBase) :
    (checkerCryptoRecordState s).getByte (BitVec.ofNat 64 query)=
      (Artifact.submission.initialState .check input).getByte (BitVec.ofNat 64 query) := by
  have fit : checkingRawBase<2^64 := by decide +kernel
  rw [checker_crypto_record_byte s query above (by omega)]
  exact ready.publicBytes query above before

theorem checker_crypto_input_cases (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776) :
    (∃ cycles, cycles≤49724+2387*input.positions.card ∧
      CheckerRejectedBlock (Artifact.submission.initialState .check input) cycles) ∨
    (∃ footer before cycles, cycles≤49724+2387*input.positions.card ∧
      RunsCheckerFooterBlock (Artifact.submission.initialState .check input) (checkerCryptoRecordState before) cycles ∧
      CheckerDecodedInput input footer before) := by
  rcases checker_decoded_input_cases input nonempty lower upper with rejected | decoded
  · obtain ⟨cycles,bound,rejects⟩ := rejected
    exact Or.inl ⟨cycles,by omega,rejects⟩
  · obtain ⟨footer,before,cycles,bound,ran,ready⟩ := decoded
    exact Or.inr ⟨footer,before,cycles+2072,by omega,
      RunsCheckerFooterBlock.next ran (checker_decoded_record_execution input nonempty footer before ready),ready⟩

private def cryptoRecordDestination (index : Nat) : Reg :=
  [.x8,.x9,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x24,.x25,.x26,.x27,.x4,.x4,.x3,.x3].getD index .x0
private theorem crypto_record_step_kept (s : MachineState) (index : Fin 17) (reg : Reg)
    (kept : reg≠cryptoRecordDestination index.val) :
    (execInstrBr s (CheckerCryptoPart.records.ops.getD index.val .EBREAK)).getReg reg=s.getReg reg := by
  fin_cases index <;> cases reg <;> simp [cryptoRecordDestination] at kept <;> rfl
private theorem crypto_record_suffix (s : MachineState) (start stop : Nat) (reg : Reg)
    (ordered : start≤stop) (small : stop≤17)
    (kept : ∀ index : Fin 17, start ≤ index.val → index.val<stop → reg≠cryptoRecordDestination index.val) :
    (checkerCryptoPrefix .records stop s).getReg reg=(checkerCryptoPrefix .records start s).getReg reg := by
  induction stop with
  | zero =>
    have eq : start=0 := by omega
    subst start
    rfl
  | succ stop ih =>
    by_cases last : start=stop+1
    · rw [last]
    · have untouched : reg≠cryptoRecordDestination stop :=
        kept ⟨stop,by omega⟩ (by change start≤stop; omega) (by change stop<stop+1; omega)
      rw [checker_crypto_succ,crypto_record_step_kept _ ⟨stop,by omega⟩ reg untouched]
      exact ih (by omega) (by omega) (fun index low high => kept index low (by omega))
private def cryptoRecordLastWrite : Reg → Fin 17
  | .x3 => 16 | .x4 => 14 | .x8 => 0 | .x9 => 1 | .x18 => 2 | .x19 => 3 | .x20 => 4
  | .x21 => 5 | .x22 => 6 | .x23 => 7 | .x24 => 9 | .x25 => 10 | .x26 => 11 | .x27 => 12
  | _ => 0
private theorem crypto_record_last_write (s : MachineState) (reg : Reg) (written : reg∈CheckerCryptoPart.records.writes) :
    (checkerCryptoPrefix .records 17 s).getReg reg=
      (execInstrBr (checkerCryptoPrefix .records (cryptoRecordLastWrite reg).val s)
        (CheckerCryptoPart.records.ops.getD (cryptoRecordLastWrite reg).val .EBREAK)).getReg reg := by
  rw [←checker_crypto_succ]
  apply crypto_record_suffix s _ 17 reg (by have := (cryptoRecordLastWrite reg).isLt; omega) (by decide)
  cases reg <;> simp [CheckerCryptoPart.writes] at written
  all_goals decide +kernel

def checkerCryptoRecordValue (s : MachineState) : Reg → Word
  | .x3 => 4056 | .x4 => 12272
  | .x8 => s.getReg .x13 | .x9 => s.getReg .x11 | .x18 => s.getReg .x16
  | .x19 => s.getReg .x14+signExtend12 4056
  | .x20 => 16777216 | .x21 => s.getReg .x15 | .x22 => s.getReg .x15+s.getReg .x17
  | .x23 => 12288 | .x24 => 12544 | .x25 => 16384 | .x26 => 4096 | .x27 => 256
  | reg => s.getReg reg
theorem checker_crypto_record_value (s : MachineState) (reg : Reg) :
    (checkerCryptoPrefix .records 17 s).getReg reg=checkerCryptoRecordValue s reg := by
  by_cases written : reg∈CheckerCryptoPart.records.writes
  · rw [crypto_record_last_write s reg written]
    cases reg <;> simp [CheckerCryptoPart.writes] at written
    case x3 =>
      change (checkerCryptoPrefix .records 16 s).getReg .x3+signExtend12 4056=4056#64
      rw [checker_crypto_succ]
      change 4096#64+signExtend12 4056=4056#64
      rfl
    case x4 =>
      change (checkerCryptoPrefix .records 14 s).getReg .x4+signExtend12 4080=12272#64
      rw [checker_crypto_succ]
      change 12288#64+signExtend12 4080=12272#64
      rfl
    case x24 =>
      change (checkerCryptoPrefix .records 9 s).getReg .x24+256=12544#64
      rw [checker_crypto_succ]
      rfl
    case x8 =>
      change (checkerCryptoPrefix .records 0 s).getReg .x13+0#64=s.getReg .x13
      rw [checker_crypto_zero,BitVec.add_zero]
    case x9 =>
      change (checkerCryptoPrefix .records 1 s).getReg .x11+0#64=s.getReg .x11
      rw [checker_crypto_prefix_register .records 1 s (by decide) .x11 (by decide),BitVec.add_zero]
    case x18 =>
      change (checkerCryptoPrefix .records 2 s).getReg .x16+0#64=s.getReg .x16
      rw [checker_crypto_prefix_register .records 2 s (by decide) .x16 (by decide),BitVec.add_zero]
    case x19 =>
      change (checkerCryptoPrefix .records 3 s).getReg .x14+signExtend12 4056=s.getReg .x14+signExtend12 4056
      rw [checker_crypto_prefix_register .records 3 s (by decide) .x14 (by decide)]
    case x21 =>
      change (checkerCryptoPrefix .records 5 s).getReg .x15+0#64=s.getReg .x15
      rw [checker_crypto_prefix_register .records 5 s (by decide) .x15 (by decide),BitVec.add_zero]
    case x22 =>
      change (checkerCryptoPrefix .records 6 s).getReg .x15+(checkerCryptoPrefix .records 6 s).getReg .x17=s.getReg .x15+s.getReg .x17
      rw [checker_crypto_prefix_register .records 6 s (by decide) .x15 (by decide),checker_crypto_prefix_register .records 6 s (by decide) .x17 (by decide)]
    all_goals rfl
  · rw [checker_crypto_prefix_register .records 17 s (by decide) reg written]
    cases reg <;> simp [CheckerCryptoPart.writes] at written <;> rfl

theorem checker_crypto_record_assigned (s : MachineState) (reg : Reg) (written : reg∈CheckerCryptoPart.records.writes) :
    (checkerCryptoRecordState s).getReg reg=checkerCryptoRecordValue s reg := by
  rw [checker_crypto_record_state_eq,checker_crypto_record_value]
  cases reg <;> simp [CheckerCryptoPart.writes] at written
  all_goals simp [checkerCryptoRecordValue,checker_crypto_guarded_register,checker_crypto_cleared_register]

end CommitGolfCandidate.Chained.Native
