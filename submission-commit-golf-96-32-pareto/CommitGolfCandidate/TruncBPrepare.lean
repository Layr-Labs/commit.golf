import CommitGolfCandidate.TruncBEffects
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 200000

structure Args (p : Fin 128) (s : MachineState) : Prop where
  slots : s.getReg .x19=BitVec.ofNat 64 (inSlot p.val)
  flags : s.getReg .x22=BitVec.ofNat 64 (flag (2*p.val))
  source : s.getReg .x23=BitVec.ofNat 64 (sourceRow p.val)
  dest : s.getReg .x24=BitVec.ofNat 64 (outSlot p.val)

theorem Args.transfer {s t : MachineState} {p : Fin 128} (a : Args p s) (k : Carries s t) : Args p t :=
  ⟨(k _ (by decide)).trans a.slots,(k _ (by decide)).trans a.flags,
    (k _ (by decide)).trans a.source,(k _ (by decide)).trans a.dest⟩

structure SameData (s t : MachineState) : Prop where
  regs : Carries s t
  mem : t.mem=s.mem

theorem SameData.atPC {s t : MachineState} (h : SameData s t) (pc : Word) : SameData s (t.setPC pc) :=
  ⟨carriesTrans h.regs (carriesPC _ _),h.mem⟩

def flagL (s : MachineState) (p : Fin 128) := byteAt s (flag (2*p.val))
def flagR (s : MachineState) (p : Fin 128) := byteAt s (flag (2*p.val+1))

theorem loadFlags (o : Oracle) (s : MachineState) (p : Fin 128) (a : Args p s) (pc : s.pc=5316) :
    Runs o s (marksState s) 2 0 ∧ SameData s (marksState s) ∧ (marksState s).pc=5324 ∧
    (marksState s).getReg .x6=(flagL s p).zeroExtend 64 ∧ (marksState s).getReg .x7=(flagR s p).zeroExtend 64 := by
  have inc : BitVec.ofNat 64 (flag (2*p.val))+1#64=BitVec.ofNat 64 (flag (2*p.val+1)) := by
    rw [show flag (2*p.val+1)=flag (2*p.val)+1 by unfold flag;omega];exact (BitVec.ofNat_add _ 1).symm
  have safe : safeSteps marksOps s := by
    intro ⟨j,h⟩;change j<2 at h
    interval_cases j
    · change accessValid (s.getReg .x22+0#64) 1 = true
      rw [a.flags,BitVec.add_zero];exact (show ∀ p : Fin 128,accessValid (BitVec.ofNat 64 (flag (2*p.val))) 1 by decide) p
    · change accessValid (s.getReg .x22+1#64) 1=true
      rw [a.flags,inc];exact (show ∀ p : Fin 128,accessValid (BitVec.ofNat 64 (flag (2*p.val+1))) 1 by decide) p
  refine ⟨pureBlockRuns (fun fuel=>marksRun s pc safe fuel false),⟨?_,rfl⟩,?_,?_,?_⟩
  · intro r hr;simp only [pairRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · simp [marksState,marksOps,execInstrBr,pc,MachineState.setPC]
  · change (s.getByte (s.getReg .x22+0#64)).zeroExtend 64=_
    rw [BitVec.add_zero,a.flags];rfl
  · change (s.getByte (s.getReg .x22+1#64)).zeroExtend 64=_
    rw [a.flags,inc];rfl

def filled (right : Bool) (s : MachineState) := if right then fillRightState s else fillLeftState s

theorem fillData (s : MachineState) (p : Fin 128) (a : Args p s) (right : Bool) :
    Carries s (filled right s) ∧ Written s (filled right s) (sourceRow p.val+(if right then 32 else 0)) (digestAt s (inSlot p.val)) := by
  constructor
  · intro r hr;simp only [pairRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    cases right <;> rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [filled,fillRightState,fillLeftState,fillRightOps,fillLeftOps,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setMem,MachineState.setPC]
  · have bp:=p.isLt
    apply copyWritten
    · cases right
      · have h:=fillLeftMem s;rw [a.slots,a.source] at h;exact h
      · have h:=fillRightMem s;rw [a.slots,a.source] at h
        change (fillRightState s).mem=(copyAt s (BitVec.ofNat 64 (inSlot p.val)) (BitVec.ofNat 64 (sourceRow p.val+32))).mem
        rw [BitVec.ofNat_add (sourceRow p.val) 32];exact h
    all_goals cases right <;> (try simp only [Bool.false_eq_true,ite_false,ite_true,inSlot,sourceRow,Separate]) <;> omega

theorem safeFill (s : MachineState) (p : Fin 128) (a : Args p s) :
    safeSteps fillLeftOps s ∧ safeSteps fillRightOps s ∧ safeSteps useParentOps s := by
  have src : ∀ j : Fin 4,accessValid (s.getReg .x19+BitVec.ofNat 64 (8*j.val)) 8 := by
    rw [a.slots];exact (show ∀ p : Fin 128,∀ j : Fin 4,accessValid (BitVec.ofNat 64 (inSlot p.val)+BitVec.ofNat 64 (8*j.val)) 8 by decide) p
  refine ⟨safeFillleft _ src ?_,safeFillright _ src ?_,safeUseparent _ src ?_⟩
  · rw [a.source];exact (show ∀ p : Fin 128,∀ j : Fin 4,accessValid (BitVec.ofNat 64 (sourceRow p.val)+BitVec.ofNat 64 (0+8*j.val)) 8 by decide) p
  · rw [a.source];exact (show ∀ p : Fin 128,∀ j : Fin 4,accessValid (BitVec.ofNat 64 (sourceRow p.val)+BitVec.ofNat 64 (32+8*j.val)) 8 by decide) p
  · rw [a.dest];exact (show ∀ p : Fin 128,∀ j : Fin 4,accessValid (BitVec.ofNat 64 (outSlot p.val)+BitVec.ofNat 64 (0+8*j.val)) 8 by decide) p

end CommitGolfCandidate.Trunc.Batch
