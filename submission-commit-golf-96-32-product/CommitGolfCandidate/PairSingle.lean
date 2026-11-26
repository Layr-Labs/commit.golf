import CommitGolfCandidate.PairHashParent
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 180000
attribute [local irreducible] readBuffer execute copy30 CKB2Half.halfRun

theorem fillRight (o : Oracle) (p : Fin 128) (m : MachineState) (a : Args p m) (pc : m.pc=6912) :
    ∃ t,Runs o m t 32 0 ∧ t.pc=7168 ∧ Carries m t ∧
      Written m t (sourceRow p.val+32) (widen (readBuffer m (inSlot p.val) 30)) := by
  have bp:=p.isLt
  obtain ⟨run,keep,cpc,w⟩ := slotCopy o m p a 704 .x23 32 (sourceRow p.val) (by decide) a.source (by decide)
    (by unfold sourceRow;omega) (by unfold sourceRow;omega) (by decide) pc
    (ckb2Loads 704 (by decide)) ckb2StoresRight ckb2ZeroRight
  let z := copy30 .x19 .x23 m 32
  have zpc : z.pc=7036 := by change (copy30 .x19 .x23 m 32).pc=_;rw [cpc,pc];rfl
  exact ⟨z.setPC 7168,runs_trans run (ckb2j735 o z zpc),rfl,carriesTrans keep (carriesPC _ _),
    ⟨(read_buffer_memory_congr (z.setPC 7168) z rfl _ _).trans w.atDst,
      fun x bx away => (byteMem (s:=z) (t:=z.setPC 7168) rfl x).trans (w.outside x bx away)⟩⟩

theorem fillLeft (o : Oracle) (p : Fin 128) (m : MachineState) (a : Args p m) (pc : m.pc=7044) :
    ∃ t,Runs o m t 31 0 ∧ t.pc=7168 ∧ Carries m t ∧
      Written m t (sourceRow p.val+0) (widen (readBuffer m (inSlot p.val) 30)) := by
  have bp:=p.isLt
  obtain ⟨run,keep,cpc,w⟩ := slotCopy o m p a 737 .x23 0 (sourceRow p.val) (by decide) a.source (by decide)
    (by unfold sourceRow;omega) (by unfold sourceRow;omega) (by decide) pc
    (ckb2Loads 737 (by decide)) ckb2StoresLeft ckb2ZeroLeft
  exact ⟨copy30 .x19 .x23 m 0,run,by rw [cpc,pc];rfl,keep,w⟩

theorem fillOne (o : Oracle) (p : Fin 128) (r : Bool) (m : MachineState) (a : Args p m)
    (pc : m.pc=if r then 6912 else 7044) :
    ∃ t,Runs o m t (if r then 32 else 31) 0 ∧ t.pc=7168 ∧ Carries m t ∧
      Written m t (sourceRow p.val+(if r then 32 else 0)) (widen (readBuffer m (inSlot p.val) 30)) := by
  cases r
  · exact fillLeft o p m a pc
  · exact fillRight o p m a pc

theorem singlePrepared (o : Oracle) (input : CheckInput) (p : Fin 128) (r : Bool) (s m : MachineState)
    (same : SameData s m) (a : Args p s) (pc : m.pc=if r then 6912 else 7044)
    (gap : digestAt s (sourceRow p.val+64)=0)
    (formula : (childrenAt o.compression input p.val).parent o.compression (supplied input p.val) =
      (if r then combine o.compression (digestAt s (sourceRow p.val)) (widen (readBuffer s (inSlot p.val) 30))
       else combine o.compression (widen (readBuffer s (inSlot p.val) 30)) (digestAt s (sourceRow p.val+32)))) :
    ∃ t,Runs o m t (if r then 32 else 31) 0 ∧ Prepared o input p s t := by
  obtain ⟨t,steps,tpc,keep,w⟩:=fillOne o p r m (a.transfer same.regs) pc
  have source : ∀ x,digestAt m x=digestAt s x := read_buffer_memory_congr m s same.mem
    |> fun eqn x => eqn x 32
  have slot := slotSource s m same p
  rw [slot] at w
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
    · have low := w.atDst
      have high := (quietDigest w.outside (sourceRow p.val+32) (by unfold sourceRow;omega)
        (Or.inr (by simp))).trans (source _)
      exact parentValue o t p _ _ (by simpa using low) high g
    · have high := w.atDst
      have low := (quietDigest w.outside (sourceRow p.val) (by unfold sourceRow;omega) (Or.inl (by simp))).trans (source _)
      exact parentValue o t p _ _ low high g

theorem copySupplied (o : Oracle) (input : CheckInput) (p : Fin 128) (s m : MachineState) (same : SameData s m)
    (a : Args p s) (pc : m.pc=7200)
    (value : widen (readBuffer s (inSlot p.val) 30)=parentAt o.compression input p.val) :
    ∃ z, Runs o m z 31 0 ∧ PairEffect o.compression input p.val s z := by
  have am:=a.transfer same.regs
  have bp:=p.isLt
  obtain ⟨run,keep,cpc,w⟩ := slotCopy o m p am 776 .x24 0 (outSlot p.val) (by decide) am.dest (by decide)
    (by unfold outSlot;omega) (by unfold outSlot;omega) (by decide) pc
    (ckb2Loads 776 (by decide)) ckb2StoresParent ckb2ZeroParent
  rw [Nat.add_zero, slotSource s m same p] at w
  refine ⟨copy30 .x19 .x24 m 0,run,⟨by rw [cpc,pc];rfl,carriesTrans same.regs keep,w.atDst.trans value,
    fun x bx _ sep=>(w.outside x bx sep).trans (byteMem same.mem x)⟩⟩
end CommitGolfCandidate.PairCap.Batch
