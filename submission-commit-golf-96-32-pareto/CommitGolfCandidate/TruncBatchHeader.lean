import CommitGolfCandidate.TruncDispatch
import CommitGolfCandidate.TruncWireRegisters
import CommitGolfCandidate.TruncBBatchSteps
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 180000

def shortLengthOps : List Instr := [.ADDI .x6 .x0 33,.SLLI .x6 .x6 11,.ADDI .x6 .x6 512]
def shortGate (s : MachineState) := shortLengthOps.foldl execInstrBr s
def afterGate (s : MachineState) := execInstrBr (shortGate s) (.BNE .x6 .x17 6880)

theorem readShortLength (s : MachineState) (pc : s.pc=loc 409) :
    Trunc.Runs (Trunc.submission.image .check) s (afterGate s) 4 4 := by
  have head : Trunc.Runs (Trunc.submission.image .check) s (shortGate s) 3 3 :=
    plainBlock shortLengthOps 409 (by decide) (by decide) (by intro k;fin_cases k <;> rfl) s pc
      (by intro k;fin_cases k <;> rfl)
  have gatePC : (shortGate s).pc=loc 412 := by
    simp [shortGate,shortLengthOps,execInstrBr,MachineState.setPC,pc,loc]
  have final := one (im:=Trunc.submission.image .check) 412 (shortGate s) (afterGate s) (.BNE .x6 .x17 6880)
    (by decide) gatePC (by rfl) rfl rfl
  exact chain head final

theorem gatePC (s : MachineState) (pc : s.pc=loc 409) :
    (afterGate s).pc=(if s.getReg .x17=68096 then loc 413 else loc 84) := by
  have pp : (shortGate s).pc=loc 412 := by simp [shortGate,shortLengthOps,execInstrBr,pc,loc,MachineState.setPC]
  have r6 : (shortGate s).getReg .x6=68096 := by simp [shortGate,shortLengthOps,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,signExtend12]
  have r17 : (shortGate s).getReg .x17=s.getReg .x17 := rfl
  by_cases eq : s.getReg .x17=68096#64
  · simp [afterGate,execInstrBr,r6,r17,eq,pp,loc,MachineState.setPC]
  · simp [afterGate,execInstrBr,r6,r17,eq,Ne.symm eq,pp,loc,signExtend13,MachineState.setPC]

theorem gateKeeps (s : MachineState) (r : Reg) (h : r≠.x6) : (afterGate s).getReg r=s.getReg r := by
  simp only [afterGate,shortGate,shortLengthOps,List.foldl,execInstrBr]
  split <;> simp only [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)]

theorem gateMem (s : MachineState) : (afterGate s).mem=s.mem := by
  unfold afterGate;simp only [execInstrBr];split <;> rfl

def afterDecode (s : MachineState) := Wire.unpackedEnd (afterGate (Trunc.dispatched s))
def expandedFirst (s : MachineState) :=
  readyState (execInstrBr (lengthState (afterDecode s)) (.BNE .x6 .x17 7628))

private theorem wideHeader (s : MachineState) (pc : s.pc=loc 222) (size : s.getReg .x17=71680) :
    Trunc.Runs (Trunc.submission.image .check) s (readyState (execInstrBr (lengthState s) (.BNE .x6 .x17 7628))) 10 10 := by
  have pp : (lengthState s).pc=4996 := by simp [lengthState,lengthOps,pc,loc,execInstrBr,MachineState.setPC]
  have regs : (lengthState s).getReg .x6=71680#64 := by simp [lengthState,lengthOps,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,signExtend12]
  have n : (lengthState s).getReg .x17=71680#64 := size
  have branch : (execInstrBr (lengthState s) (.BNE .x6 .x17 7628)).pc=5000 := by
    simp [execInstrBr,regs,n,MachineState.setPC,pp]
  have e : Trunc.Runs (Trunc.submission.image .check) (lengthState s) (execInstrBr (lengthState s) (.BNE .x6 .x17 7628)) 1 1 :=
    one 225 _ _ _ (by decide) pp (by rfl) rfl rfl
  exact chain (chain (lengthRun s pc) e) (readyRun _ branch)

theorem headerRun (s : MachineState) (pc : s.pc=4096) (b : s.getReg .x16=128) (size : s.getReg .x17=68096) :
    Trunc.Runs (Trunc.submission.image .check) s (expandedFirst s) 70957 70957 := by
  have dpc : (Trunc.dispatched s).pc=loc 409 := by change (if _ then _ else _)=_;rw [if_pos b];rfl
  have g:=readShortLength _ dpc
  have p : (afterGate (Trunc.dispatched s)).pc=loc 413 := by
    rw [gatePC _ dpc,if_pos ((dispatchFrame s).2.2.2.2.2.2.1.trans size)]
  have data:= (Wire.phases true (afterGate (Trunc.dispatched s)) p).1
  have same : Wire.unpackedEnd (afterGate (Trunc.dispatched s))=
      Wire.endState true (Wire.secondPhase true (afterGate (Trunc.dispatched s))) := by
    unfold Wire.unpackedEnd Wire.secondPhase Wire.firstPhase
    have forget (x : MachineState) (px : x.pc=loc 413) : x.setPC (loc 413)=x := by cases x;simp_all [MachineState.setPC]
    rw [forget _ p];rfl
  have wide:=wideHeader (afterDecode s) (Wire.unpackedPC _) (Wire.unpackedLen _)
  rw [←same] at data
  exact chain (chain (chain (Trunc.patchedDispatch s pc) g) data) wide

theorem expandedRegs (s : MachineState) (b : s.getReg .x16=128) :
    let r:=expandedFirst s
    r.pc=5024 ∧ r.getReg .x27=128 ∧ r.getReg .x24=s.getReg .x13 ∧ r.getReg .x8=s.getReg .x14 ∧
    r.getReg .x25=s.getReg .x15 ∧ r.getReg .x26=s.getReg .x11 ∧ r.getReg .x19=s.getReg .x15+67584 ∧
    r.getReg .x21=256 ∧ r.getReg .x30=16 ∧ r.mem=(afterDecode s).mem := by
  let t:=afterDecode s
  have pp : t.pc=loc 222:=Wire.unpackedPC _
  have len : t.getReg .x17=71680:=Wire.unpackedLen _
  have endReg (r : Reg) (h : Wire.Preserved r) :
      t.getReg r=(Trunc.dispatched s).getReg r :=
    (Wire.unpackedKeeps _ _ h).trans (gateKeeps _ _ h.1)
  obtain ⟨rt,idx,v,pf,k,_⟩:=dispatchFrame s
  have describe (u : MachineState) (p : u.pc=loc 222) (l : u.getReg .x17=71680) :
      let z:=readyState (execInstrBr (lengthState u) (.BNE .x6 .x17 7628))
      z.pc=5024 ∧ z.getReg .x27=u.getReg .x27 ∧ z.getReg .x24=u.getReg .x24 ∧ z.getReg .x8=u.getReg .x8 ∧
        z.getReg .x25=u.getReg .x25 ∧ z.getReg .x26=u.getReg .x26 ∧ z.getReg .x19=u.getReg .x25+67584 ∧
        z.getReg .x21=256 ∧ z.getReg .x30=16 ∧ z.mem=u.mem := by
    simp [readyState,readyOps,lengthState,lengthOps,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,signExtend12,loc] at p l ⊢
    simp [p,l,MachineState.setPC,MachineState.getReg,MachineState.setReg]
  have g:=describe t pp len
  simp only [endReg _ (by unfold Wire.Preserved;decide : Wire.Preserved .x24),
    endReg _ (by unfold Wire.Preserved;decide : Wire.Preserved .x8),
    endReg _ (by unfold Wire.Preserved;decide : Wire.Preserved .x25),
    endReg _ (by unfold Wire.Preserved;decide : Wire.Preserved .x26),
    endReg _ (by unfold Wire.Preserved;decide : Wire.Preserved .x27),rt,idx,v,pf,k,b] at g
  exact g
end CommitGolfCandidate.Trunc.Batch
