import CommitGolfCandidate.PairEffects
namespace CommitGolfCandidate.PairCap.Batch
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

theorem loadFlags (o : Oracle) (s : MachineState) (p : Fin 128) (a : Args p s) (pc : s.pc=6892) :
    Runs o s (marksState s) 2 0 ∧ SameData s (marksState s) ∧ (marksState s).pc=6900 ∧
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
  refine ⟨pureBlockRuns (fun fuel=>ckb2MarksRun s pc safe fuel false),⟨?_,rfl⟩,?_,?_,?_⟩
  · intro r hr;simp only [pairRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · simp [marksState,marksOps,execInstrBr,pc,MachineState.setPC]
  · change (s.getByte (s.getReg .x22+0#64)).zeroExtend 64=_
    rw [BitVec.add_zero,a.flags];rfl
  · change (s.getByte (s.getReg .x22+1#64)).zeroExtend 64=_
    rw [a.flags,inc];rfl

/-- (A96) the 30-byte slot `p` copied to `D+b` (via `dst`) by the 31 words at `start`. -/
theorem slotCopy (o : Oracle) (s : MachineState) (p : Fin 128) (a : Args p s) (start : Nat) (dst : Reg)
    (b D : Nat) (dstNe : dst ≠ .x6) (target : s.getReg dst = BitVec.ofNat 64 D)
    (bBound : b+32 ≤ 2048) (aligned : (D+b)%8=0) (low : D+b+32 ≤ 32768)
    (hs : start+31 ≤ 814) (pc : s.pc = BitVec.ofNat 64 (4096+4*start))
    (loads : ∀ j<15, (Late.Check.Normal.checkerImage.code[start+2*j]?).bind decodeInstruction =
      some (.base (.LHU .x6 .x19 (BitVec.ofNat 12 (0+2*j)))))
    (stores : ∀ j<15, (Late.Check.Normal.checkerImage.code[start+2*j+1]?).bind decodeInstruction =
      some (.base (.SH dst .x6 (BitVec.ofNat 12 (b+2*j)))))
    (zero : (Late.Check.Normal.checkerImage.code[start+30]?).bind decodeInstruction =
      some (.base (.SH dst .x0 (BitVec.ofNat 12 (b+30))))) :
    Runs o s (copy30 .x19 dst s b) 31 0 ∧ Carries s (copy30 .x19 dst s b) ∧
      (copy30 .x19 dst s b).pc = s.pc + BitVec.ofNat 64 124 ∧
      Written s (copy30 .x19 dst s b) (D+b) (widen (readBuffer s (inSlot p.val) 30)) := by
  have bp:=p.isLt
  have src : s.getReg .x19 = BitVec.ofNat 64 (inSlot p.val) := a.slots
  refine ⟨ckb2CopyRuns o s start .x19 dst b (inSlot p.val) D (by decide) dstNe src target bBound
      (by unfold inSlot;omega) (by omega) (by unfold inSlot MEMORY_BYTES;omega) (by unfold MEMORY_BYTES;omega)
      hs pc loads stores zero,?_,copy30PC _ _ _ _,?_⟩
  · intro r hr
    apply copy30Register
    simp only [pairRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · exact copy30Written .x19 dst s b (inSlot p.val) D (by decide) dstNe src target bBound
      (by unfold inSlot;omega) (by omega) (by unfold inSlot;omega) (by omega) (by unfold inSlot;omega)

theorem slotSource (s t : MachineState) (same : SameData s t) (p : Fin 128) :
    readBuffer t (inSlot p.val) 30 = readBuffer s (inSlot p.val) 30 :=
  read_buffer_memory_congr _ _ same.mem _ _

end CommitGolfCandidate.PairCap.Batch
