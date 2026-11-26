import CommitGolfCandidate.TruncBRowMemory
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 250000

def liveRegs := [Reg.x8,.x19,.x21,.x24,.x25,.x26,.x27,.x30]
def Keeps (s t : MachineState) := ∀ r ∈ liveRegs,t.getReg r=s.getReg r

theorem testKeeps (s : MachineState) : Keeps s (tested s) := by
  intro r hr
  simp only [liveRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    apply (congrFun (testPreserves s).1 _).trans <;> rfl

theorem storeKeeps (s : MachineState) : Keeps s (storeState s) := by
  intro r hr
  simp only [liveRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [storeState,storeOps,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,MachineState.setByte,MachineState.setMem]

def cmpDone (s : MachineState) := execInstrBr (PairCap.top_checkRootWordsState (tested s) 294 4) (.JAL .x0 44)

theorem cmpKeeps (s : MachineState) : Keeps (tested s) (cmpDone s) := by
  intro r hr
  have cond : r≠.x6 ∧ r≠.x7 := by
    simp only [liveRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  simpa only [cmpDone,execInstrBr,MachineState.setReg,MachineState.getReg_setPC] using
    (PairCap.top_check_root_words_preserves (tested s) 294 4 r cond.1 cond.2).1

def finishRow (fresh : Bool) (s : MachineState) := if fresh then copied s else compared s

def postBody (fresh : Bool) (s : MachineState) := if fresh then storeState (tested s) else cmpDone s

theorem bodyKeeps (fresh : Bool) (s : MachineState) : Keeps s (postBody fresh s) := by
  intro r hr
  cases fresh
  · exact (cmpKeeps s r hr).trans (testKeeps s r hr)
  · exact (storeKeeps (tested s) r hr).trans (testKeeps s r hr)

attribute [local irreducible] storeState PairCap.top_checkRootWordsState bucketState
theorem bodyPC (s : MachineState) (fresh : Bool) (pc : s.pc=5220) (u : Fin 256) (idx : s.getReg .x20=BitVec.ofNat 64 u.val)
    (flagged : fresh = decide ((bucketState s).getReg .x7=0))
    (agree : fresh=false → ∀ j<4, (tested s).getMem ((tested s).getReg .x21+BitVec.ofNat 64 (8*j)) =
                              (tested s).getMem ((tested s).getReg .x23+BitVec.ofNat 64 (8*j))) :
    (postBody fresh s).pc=5364 := by
  have bp := (bucketInfo s pc u idx).1
  have loc : (tested s).pc = if (bucketState s).getReg .x7=0 then 5324 else 5272 := by
    unfold tested afterTest execInstrBr
    simp only [beq_iff_eq,show (bucketState s).getReg .x0 = 0 from rfl]
    split <;> simp_all [MachineState.setPC,signExtend13]
  cases fresh
  · have v : (bucketState s).getReg .x7≠0 := by simpa using flagged.symm
    rw [if_neg v] at loc
    have done := PairCap.top_check_root_words_pc _ 294 (Or.inl rfl) loc 4 (by decide) (agree rfl)
    simpa [postBody,cmpDone,execInstrBr,MachineState.setPC,signExtend21,done]
  · have v : (bucketState s).getReg .x7=0 := by simpa using flagged.symm
    rw [if_pos v] at loc
    change (storeState (tested s)).pc=5364
    exact storePC (tested s) loc

end CommitGolfCandidate.Trunc.Batch
