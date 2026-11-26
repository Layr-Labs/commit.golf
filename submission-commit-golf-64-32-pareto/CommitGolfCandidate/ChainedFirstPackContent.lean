import CommitGolfCandidate.ChainedFirstPackValue
import CommitGolfCandidate.Memory

/-! Memory refinement of the first-stage packer, through a PC-free data view. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private structure PackData where
  regs : Reg → Word
  mem : Word → Word

private def packView (s : MachineState) : PackData := ⟨s.getReg,s.getMem⟩

private def packAssign (s : PackData) (reg : Reg) (value : Word) : PackData :=
  ⟨fun query => if query == reg then value else s.regs query,s.mem⟩

private def packStore (s : PackData) (address value : Word) : PackData :=
  ⟨s.regs,fun query => if query == address then value else s.mem query⟩

private theorem assign_regs (s : PackData) (reg : Reg) (value : Word) (query : Reg) :
    (packAssign s reg value).regs query = if query == reg then value else s.regs query := rfl

private theorem assign_mem (s : PackData) (reg : Reg) (value : Word) :
    (packAssign s reg value).mem = s.mem := rfl

private theorem store_regs (s : PackData) (address value : Word) :
    (packStore s address value).regs = s.regs := rfl

private theorem store_mem (s : PackData) (address value query : Word) :
    (packStore s address value).mem query = if query == address then value else s.mem query := rfl

private theorem view_pc (s : MachineState) (pc : Word) : packView (s.setPC pc) = packView s := rfl

private theorem view_reg (s : MachineState) (reg : Reg) (value : Word) (nonzero : reg ≠ .x0) :
    packView (s.setReg reg value) = packAssign (packView s) reg value := by
  apply congrArg₂ PackData.mk
  · funext query
    by_cases same : query = reg
    · subst query
      simp [MachineState.getReg_setReg_eq nonzero]
    · simp [packView,MachineState.getReg_setReg_ne,Ne.symm same,same]
  · funext query
    exact MachineState.getMem_setReg

private theorem view_mem (s : MachineState) (address value : Word) :
    packView (s.setMem address value) = packStore (packView s) address value := by
  apply congrArg₂ PackData.mk
  · funext query
    cases query <;> rfl
  · rfl

private def packDataStep (s : PackData) : Instr → PackData
  | .LD dst src offset => packAssign s dst (s.mem (s.regs src+signExtend12 offset))
  | .SD dst src offset => packStore s (s.regs dst+signExtend12 offset) (s.regs src)
  | .SLLI dst src amount => packAssign s dst (s.regs src <<< amount.toNat)
  | .SRLI dst src amount => packAssign s dst (s.regs src >>> amount.toNat)
  | .OR dst left right => packAssign s dst (s.regs left ||| s.regs right)
  | _ => s

private theorem step_view (s : MachineState) (i : Fin 31) :
    packView (execInstrBr s (firstPackOp i.val)) = packDataStep (packView s) (firstPackOp i.val) := by
  fin_cases i <;>
    simp only [firstPackOp,firstPackOps,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some] <;>
    dsimp only [execInstrBr,packDataStep] <;>
    first
    | rw [view_pc,view_reg _ _ _ (by decide)]; rfl
    | rw [view_pc,view_mem]; rfl
    | rfl

private def dataPrefix (s : PackData) (count : Nat) : PackData :=
  (firstPackOps.take count).foldl packDataStep s

private theorem prefix_next (s : MachineState) (count : Nat) (inside : count < 31) :
    firstPackPrefix s (count+1) = execInstrBr (firstPackPrefix s count) (firstPackOp count) := by
  interval_cases count <;> rfl

private theorem data_next (s : PackData) (count : Nat) (inside : count < 31) :
    dataPrefix s (count+1) = packDataStep (dataPrefix s count) (firstPackOp count) := by
  interval_cases count <;> rfl

private theorem prefix_view (s : MachineState) (count : Nat) (inside : count ≤ 31) :
    packView (firstPackPrefix s count) = dataPrefix (packView s) count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [prefix_next s count (by omega),step_view _ ⟨count,by omega⟩,
      ih (by omega),data_next _ count (by omega)]

private theorem data_word (s : PackData) (left right : BitVec 238) (i : Fin 8)
    (inputs : ∀ k : Fin 8, s.mem (s.regs .x14+BitVec.ofNat 64 (8*k.val)) =
      if k.val < 4 then childWord left k.val else childWord right (k.val-4)) :
    (dataPrefix s 31).mem (s.regs .x10+BitVec.ofNat 64 (8*i.val)) =
      firstPackedWord (s.regs .x17) left right i.val := by
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,Fin.val_zero,Fin.val_succ,
    Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,BitVec.add_zero] at inputs
  rcases inputs with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  fin_cases i <;>
    simp [dataPrefix,firstPackOps,packDataStep,assign_regs,assign_mem,store_regs,store_mem,
      firstPackedWord,signExtend12,BitVec.add_right_inj,h0,h1,h2,h3,h4,h5,h6,h7]

private theorem data_register (s : PackData) (query : Reg)
    (kept : query ∉ ([.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29] : List Reg)) :
    (dataPrefix s 31).regs query = s.regs query := by
  have constraints : query ≠ .x20 ∧ query ≠ .x21 ∧ query ≠ .x22 ∧ query ≠ .x23 ∧
      query ≠ .x24 ∧ query ≠ .x25 ∧ query ≠ .x26 ∧ query ≠ .x27 ∧ query ≠ .x28 ∧ query ≠ .x29 := by
    simpa using kept
  rcases constraints with ⟨h20,h21,h22,h23,h24,h25,h26,h27,h28,h29⟩
  simp [dataPrefix,firstPackOps,packDataStep,assign_regs,store_regs,
    h20,h21,h22,h23,h24,h25,h26,h27,h28,h29]

private theorem data_outside (s : PackData) (query : Word)
    (outside : ∀ k : Fin 8, query ≠ s.regs .x10+BitVec.ofNat 64 (8*k.val)) :
    (dataPrefix s 31).mem query = s.mem query := by
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,Fin.val_zero,Fin.val_succ,
    Nat.reduceAdd,Nat.reduceMul,BitVec.add_zero] at outside
  rcases outside with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  simp [dataPrefix,firstPackOps,packDataStep,assign_regs,assign_mem,store_regs,store_mem,
    signExtend12,h0,h1,h2,h3,h4,h5,h6,h7]

attribute [local irreducible] firstPackPrefix

theorem first_pack_stored_word (s : MachineState) (left right : BitVec 238) (i : Fin 8)
    (inputs : ∀ k : Fin 8, s.getMem (s.getReg .x14+BitVec.ofNat 64 (8*k.val)) =
      if k.val < 4 then childWord left k.val else childWord right (k.val-4)) :
    (firstPackPrefix s 31).getMem (s.getReg .x10+BitVec.ofNat 64 (8*i.val)) =
      firstPackedWord (s.getReg .x17) left right i.val := by
  have projection := congrArg (fun view => view.mem) (prefix_view s 31 (by decide))
  change (packView (firstPackPrefix s 31)).mem _ = _
  rw [projection]
  exact data_word (packView s) left right i inputs

theorem first_pack_register (s : MachineState) (query : Reg)
    (kept : query ∉ ([.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29] : List Reg)) :
    (firstPackPrefix s 31).getReg query = s.getReg query := by
  have projection := congrArg (fun view => view.regs) (prefix_view s 31 (by decide))
  change (packView (firstPackPrefix s 31)).regs query = _
  rw [projection]
  exact data_register (packView s) query kept

theorem first_pack_memory_outside (s : MachineState) (query : Word)
    (outside : ∀ k : Fin 8, query ≠ s.getReg .x10+BitVec.ofNat 64 (8*k.val)) :
    (firstPackPrefix s 31).getMem query = s.getMem query := by
  have projection := congrArg (fun view => view.mem) (prefix_view s 31 (by decide))
  change (packView (firstPackPrefix s 31)).mem query = _
  rw [projection]
  exact data_outside (packView s) query outside

end CommitGolfCandidate.Chained.Native
