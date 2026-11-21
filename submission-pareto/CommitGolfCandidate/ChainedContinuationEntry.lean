import CommitGolfCandidate.ChainedContinuationContent

/-! Entry branch, header, full-width loop and final mask as one native call. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

theorem LoopArgs.header {s : MachineState} {buffer : Word} (args : LoopArgs s buffer) :
    LoopArgs (ordinaryPrefix s 1 8) buffer := by
  have kept (reg : Reg) (a : reg ≠ .x29) (b : reg ≠ .x30) := header_register s reg a b
  exact ⟨(kept .x10 (by decide) (by decide)).trans args.source,
    (kept .x12 (by decide) (by decide)).trans args.target,
    (kept .x5 (by decide) (by decide)).trans args.selector,
    (kept .x11 (by decide) (by decide)).trans args.size,
    (kept .x13 (by decide) (by decide)).trans args.kind,
    args.aligned,args.inputValid,args.outputValid,args.access⟩

def continuationPrepared (base : Word) (remaining : Nat) (s : MachineState) : MachineState :=
  if remaining = 0 then s.setPC (base+60) else ordinaryPrefix (s.setPC (base+4)) 1 8

def continuationFullTrace (base buffer : Word) (remaining : Nat) (s : MachineState) :
    OracleComp World MachineState := do
  let out ← loopTrace buffer remaining (continuationPrepared base remaining s)
  return ordinaryPrefix out 15 4

theorem continuation_entry_execution (image : Image) (base buffer : Word)
    (code : ContinuationAt image base) (remaining : Nat) (small : remaining ≤ 7)
    (s : MachineState) (args : LoopArgs s buffer)
    (counter : s.getReg .x18 = BitVec.ofNat 64 remaining) (pc : s.pc = base)
    (valid : ∀ k : Fin 8, accessValid (buffer+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (fuel : Nat) (coins : Bool) :
    execute image (continuationInstructions remaining+fuel) s coins =
      (do let out ← continuationFullTrace base buffer remaining s
          let result ← execute image fuel out coins
          return result.charge (continuationCycles remaining) remaining) := by
  have v24 : accessValid (buffer+24) 8 = true := valid ⟨3,by decide⟩
  have source24 : accessValid (s.getReg .x10+24) 8 = true := by rw [args.source]; exact v24
  by_cases empty : remaining = 0
  · subst remaining
    have zero : s.getReg .x18 = 0 := counter
    simpa only [continuationInstructions,continuationCycles,ite_true,continuationFullTrace,
      continuationPrepared,loopTrace,pure_bind] using
      empty_continuation_execution image base code s pc zero source24 fuel coins
  · have raw : s.getReg .x18 ≠ 0 := by
      rw [counter]
      intro same
      have equality := congrArg BitVec.toNat same
      change remaining % 2^64 = 0 at equality
      omega
    let next := s.setPC (base+4)
    have branch : ordinaryStep s (.base (.BEQ .x18 .x0 60)) = some next := by
      have nonzero : s.regs .x18 ≠ 0 := raw
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,next,
        MachineState.getReg]
      intro equal
      exact (nonzero equal).elim
    have fetched : fetch image s = some (.base (.BEQ .x18 .x0 60)) := by
      apply code ⟨0,by decide⟩
      simpa using pc
    have nextArgs : LoopArgs next buffer :=
      ⟨args.source,args.target,args.selector,args.size,args.kind,args.aligned,
        args.inputValid,args.outputValid,args.access⟩
    have headerArgs := nextArgs.header
    have headerCounter : (ordinaryPrefix next 1 8).getReg .x18 = BitVec.ofNat 64 remaining :=
      (header_register next .x18 (by decide) (by decide)).trans counter
    have headerPc : (ordinaryPrefix next 1 8).pc =
        if remaining = 0 then base+60 else base+36 := by
      rw [header_pc,ite_eq_right empty]
      change base+4+32 = base+36
      rw [BitVec.add_assoc]
      rfl
    have v40 : accessValid (next.getReg .x10+40) 8 = true := by
      change accessValid (s.getReg .x10+40) 8 = true
      rw [args.source]
      exact valid ⟨5,by decide⟩
    have v48 : accessValid (next.getReg .x10+48) 8 = true := by
      change accessValid (s.getReg .x10+48) 8 = true
      rw [args.source]
      exact valid ⟨6,by decide⟩
    have v56 : accessValid (next.getReg .x10+56) 8 = true := by
      change accessValid (s.getReg .x10+56) 8 = true
      rw [args.source]
      exact valid ⟨7,by decide⟩
    have v32 : accessValid (next.getReg .x10+32) 8 = true := by
      change accessValid (s.getReg .x10+32) 8 = true
      rw [args.source]
      exact args.access
    rw [continuationInstructions,ite_eq_right empty,
      show 13+6*remaining+fuel = (8+(6*remaining+4+fuel))+1 by omega,
      execute_ordinary_step image _ _ _ _ coins fetched branch,
      header_execution image base code next rfl v32 v40 v48 v56,
      loop_mask_execution image base buffer code remaining small _ headerArgs headerCounter headerPc v24]
    have tally : 1+(4+(8+13*remaining)) = 13+13*remaining := by omega
    simp [continuationFullTrace,continuationPrepared,continuationCycles,empty,next,
      Execution.charge,instructionCycles,Nat.add_left_comm,Nat.add_comm,tally]

end CommitGolfCandidate.Chained.Native
