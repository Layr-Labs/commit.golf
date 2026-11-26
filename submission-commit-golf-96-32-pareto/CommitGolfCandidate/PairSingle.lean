import CommitGolfCandidate.PairHashParent
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 180000
attribute [local irreducible] readBuffer execute

private theorem fillPC (s : MachineState) (r : Bool) (pc : s.pc=if r then 5436 else 5476) :
    (filled r s).pc=if r then 5468 else 5508 := by
  cases r <;> simp [filled,fillRightState,fillLeftState,fillRightOps,fillLeftOps,execInstrBr,MachineState.setPC,pc]

theorem fillOne (o : Oracle) (p : Fin 128) (r : Bool) (m : MachineState) (a : Args p m)
    (pc : m.pc=if r then 5436 else 5476) :
    ∃ t,Runs o m t (if r then 9 else 8) 0 ∧ t.pc=5508 ∧ Carries m t ∧
      Written m t (sourceRow p.val+(if r then 32 else 0)) (digestAt m (inSlot p.val)) := by
  let z:=filled r m
  have lit := fillData m p a r
  have safe:=safeFill m p a
  have atEnd:=fillPC m r pc
  cases r
  · exact ⟨z,pureBlockRuns (fun fuel=>fillLeftRun m pc safe.1 fuel false),atEnd,lit⟩
  · exact ⟨z.setPC 5508,runs_trans (pureBlockRuns (fun fuel=>fillRightRun m pc safe.2.1 fuel false)) (jump318 o z atEnd),
      rfl,carriesTrans lit.1 (carriesPC _ _),⟨(read_buffer_memory_congr (z.setPC 5508) z rfl _ _).trans lit.2.atDst,
      fun x bx away => (byteMem (s:=z) (t:=z.setPC 5508) rfl x).trans (lit.2.outside x bx away)⟩⟩

theorem singlePrepared (o : Oracle) (input : CheckInput) (p : Fin 128) (r : Bool) (s m : MachineState)
    (same : SameData s m) (a : Args p s) (pc : m.pc=if r then 5436 else 5476)
    (gap : digestAt s (sourceRow p.val+64)=0)
    (formula : parentAt o.compression input p.val =
      (if r then combine o.compression (digestAt s (sourceRow p.val)) (digestAt s (inSlot p.val))
       else combine o.compression (digestAt s (inSlot p.val)) (digestAt s (sourceRow p.val+32)))) :
    ∃ t,Runs o m t (if r then 9 else 8) 0 ∧ Prepared o input p s t := by
  obtain ⟨t,steps,tpc,keep,w⟩:=fillOne o p r m (a.transfer same.regs) pc
  have source : ∀ x,digestAt m x=digestAt s x := read_buffer_memory_congr m s same.mem
    |> fun eqn x => eqn x 32
  have bp:=p.isLt
  have g : digestAt t (sourceRow p.val+64)=0 := by
    apply (quietDigest w.outside _ (by unfold sourceRow;omega) _).trans ((source _).trans gap)
    cases r <;> simp only [Bool.false_eq_true,if_false,if_true] <;> unfold Separate <;> omega
  refine ⟨t,steps,tpc,carriesTrans same.regs keep,?_,?_⟩
  · intro x bx sep
    have sep' : Separate x 1 (sourceRow p.val+(if r then 32 else 0)) 32 := by
      cases r <;> simp only [Bool.false_eq_true,if_false,if_true] <;> unfold Separate at * <;> omega
    exact (w.outside x bx sep').trans (byteMem same.mem x)
  · rw [formula];cases r
    · have low := w.atDst.trans (source _)
      have high := (quietDigest w.outside (sourceRow p.val+32) (by unfold sourceRow;omega)
        (Or.inr (by simp))).trans (source _)
      exact parentValue o t p _ _ (by simpa using low) high g
    · have high := w.atDst.trans (source _)
      have low := (quietDigest w.outside (sourceRow p.val) (by unfold sourceRow;omega) (Or.inl (by simp))).trans (source _)
      exact parentValue o t p _ _ low high g

theorem copySupplied (o : Oracle) (input : CheckInput) (p : Fin 128) (s m : MachineState) (same : SameData s m)
    (a : Args p s) (pc : m.pc=5536)
    (value : digestAt s (inSlot p.val)=parentAt o.compression input p.val) :
    ∃ z, Runs o m z 8 0 ∧ PairEffect o.compression input p.val s z := by
  let z:=useParentState m
  have am:=a.transfer same.regs
  have w : Written m z (outSlot p.val) (digestAt m (inSlot p.val)) := by
    have bp:=p.isLt
    apply copyWritten
    · rw [parentCopyMem,am.slots,am.dest]
    all_goals (try simp only [inSlot,outSlot,Separate]) <;> omega
  have run : Runs o m z 8 0 := pureBlockRuns (fun fuel=>useParentRun m pc (safeFill m p am).2.2 fuel false)
  refine ⟨z,run,?_,carriesTrans same.regs ?_,w.atDst.trans ((read_buffer_memory_congr _ _ same.mem _ _).trans value),
    fun x bx _ sep=>(w.outside x bx sep).trans (byteMem same.mem x)⟩
  · simp [z,useParentState,useParentOps,execInstrBr,pc,MachineState.setPC]
  · intro reg hr
    simp only [pairRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
end CommitGolfCandidate.PairCap.Batch
