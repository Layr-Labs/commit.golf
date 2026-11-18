import CommitGolfCandidate.PhaseBody
namespace TwoPermutationPrototype.PhaseOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate GroupedOpening
open Opening (sortedIndex markBase)
set_option maxRecDepth 30000
set_option maxHeartbeats 3600000
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local irreducible] execute

def siblingEnd : List Instr := [.ADDI .x21 .x21 30,.SRLI .x6 .x6 1]
def tailStart (s : MachineState) := straight s siblingEnd

theorem original_data (old : MachineState) : tailStart (afterCopy old 17)=recordData old := by rfl

theorem original_tail (raw : MachineState) :
    straight raw lastOps=recordTailPrefix (tailStart raw) 5 := by rfl

theorem safe_mark (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor))
    (pos : Positions) (old : MachineState) (o : Nat) (present : o<pos.card)
    (boundary : RecordBoundary s td pos old o) :
    accessValid (Opening.recordMarkAddress (recordData old)) 8=true := by
  let i:=sortedIndex pos o present
  let g:=Sampling.capGroup i
  let markAddr:=markBase+8*g
  have data:=execute_record_data s layout td pos old o present (boundary.start present)
  have groupBounds : g<512 := (Opening.lower_cap_range i).2
  have fit : markAddr<trapdoorBase := by
    have sameBase : Opening.trapdoorBase=trapdoorBase := rfl
    have room:=Opening.marks_before_trapdoor
    unfold markAddr;omega
  have a : Opening.recordMarkAddress (recordData old)=addr markAddr :=
    Opening.record_mark_address _ g ((data.register .x26 (by decide)).trans boundary.marks) data.cursor.node
  rw [a]
  apply Opening.aligned_access
  · have baseAligned : markBase%8=0 := by decide
    unfold markAddr
    omega
  · have room : trapdoorBase+8≤MEMORY_BYTES := by decide
    omega

theorem ready_last (raw : MachineState) (safe : accessValid (Opening.recordMarkAddress (tailStart raw)) 8=true) :
    readyOps lastOps raw := by
  simpa [lastOps,readyOps,tailStart,siblingEnd,straight,Opening.recordMarkAddress,
    memoryArgumentsValid,memAccess,execInstrBr,signExtend12] using safe

attribute [local irreducible] execInstrBr recordTailPrefix recordData afterCopy tailStart straight

theorem common_tail_step (state : MachineState) (i : Nat) (bounded : i<6) :
    recordTailPrefix state (i+1) = execInstrBr (recordTailPrefix state i) (recordTailInstructions[i]?.getD .EBREAK) := by
  have inside : i < recordTailInstructions.length := by change i<7;omega
  rw [recordTailPrefix,recordTailPrefix,List.take_succ_eq_append_getElem inside,List.foldl_append,
    List.getElem?_eq_getElem inside]
  rfl

theorem branch_rel (marked : MachineState) (fin : Bool) :
    Rel (afterLatch (execInstrBr marked (.BEQ .x18 .x0 8)) fin) marked := by
  cases fin <;> by_cases z : (marked.getReg .x18 == marked.getReg .x0)=true
  all_goals simp only [afterLatch,execInstrBr,z,ite_true,ite_false,Bool.false_eq_true]
  all_goals exact ⟨rfl,fun _ _ => rfl⟩

theorem reference_latch (w : MachineState) (fin : Bool) :
    Rel (afterLatch (recordTailPrefix w 6) fin) (recordTailPrefix w 5) := by
  have eq:=common_tail_step w 5 (by decide)
  have item : recordTailInstructions[5]?.getD .EBREAK=.BEQ .x18 .x0 8 := by decide
  rw [item] at eq
  rw [eq]
  exact branch_rel _ _


theorem tail_reference (old : MachineState) (fin : Bool) :
    Rel (runRecord old fin) (straight (afterCopy old 17) lastOps) := by
  rw [original_tail,original_data]
  exact reference_latch _ fin

def latchPC (p : Fin 4) := lastPC p+lastOps.length
def nextPhase (p : Fin 4) : Fin 4 := ⟨(p.val+1)%4,Nat.mod_lt _ (by decide)⟩
def nextRow (p : Fin 4) (fin : Bool) := if fin then 649 else phasePC (nextPhase p)
def jumpRow (p : Fin 4) (fin : Bool) := latchPC p + (if fin then 2 else 1)
def jumpImm (p : Fin 4) (fin : Bool) : BitVec 21 :=
  (BitVec.ofNat 21 (4*nextRow p fin) - BitVec.ofNat 21 (4*jumpRow p fin))
def finishRecord (p : Fin 4) (fin : Bool) (s : MachineState) := s.setPC (addr (4096+4*nextRow p fin))

theorem latch_geometry (p : Fin 4) (fin : Bool) :
    761≤latchPC p ∧ latchPC p<2680 ∧
    decodeAt (latchPC p)=some (.BEQ .x18 .x0 8) ∧
    761≤jumpRow p fin ∧ jumpRow p fin<2680 ∧
    decodeAt (jumpRow p fin)=some (.JAL .x0 (jumpImm p fin)) ∧
    addr (4096+4*latchPC p)+(if fin then signExtend13 8 else 4)=addr (4096+4*jumpRow p fin) ∧
    addr (4096+4*jumpRow p fin)+signExtend21 (jumpImm p fin)=addr (4096+4*nextRow p fin) := by
  exact (show ∀ q : Fin 4, ∀ b : Bool,
    761≤latchPC q ∧ latchPC q<2680 ∧ decodeAt (latchPC q)=some (.BEQ .x18 .x0 8) ∧
    761≤jumpRow q b ∧ jumpRow q b<2680 ∧ decodeAt (jumpRow q b)=some (.JAL .x0 (jumpImm q b)) ∧
    addr (4096+4*latchPC q)+(if b then signExtend13 8 else 4)=addr (4096+4*jumpRow q b) ∧
    addr (4096+4*jumpRow q b)+signExtend21 (jumpImm q b)=addr (4096+4*nextRow q b) by decide) p fin

theorem latch_run (pi : Image) (p : Fin 4) (fin : Bool) (s : MachineState)
    (pc : s.pc=addr (4096+4*latchPC p)) (matchFin : (s.getReg .x18=0#64) ↔ fin=true) :
    PairRun (stitched pi) s (finishRecord p fin s) 2 := by
  obtain ⟨bl,bu,bd,jl,ju,jd,baddr,jaddr⟩:=latch_geometry p fin
  let j:=s.setPC (addr (4096+4*jumpRow p fin))
  have f:=stitched_fetch pi _ _ s bl bu bd pc
  have b : ordinaryStep s (.base (.BEQ .x18 .x0 8))=some j := by
    have w : s.getReg .x0=0#64 := rfl
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,execInstrBr,w,beq_iff_eq,matchFin,pc]
    cases fin <;> simp_all [j]
  have fj:=stitched_fetch pi _ _ j jl ju jd rfl
  have jmp : ordinaryStep j (.base (.JAL .x0 (jumpImm p fin)))=some (finishRecord p fin s) := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,execInstrBr]
    change some (s.setPC (addr (4096+4*jumpRow p fin)+signExtend21 (jumpImm p fin))) = _
    rw [jaddr];rfl
  have a : PairRun (stitched pi) s j 1 := by
    intro k coins
    simpa only [Nat.add_comm 1 k,instructionCycles] using CommitGolfCandidate.execute_ordinary_step _ _ _ _ k coins f b
  have z : PairRun (stitched pi) j (finishRecord p fin s) 1 := by
    intro k coins
    simpa only [Nat.add_comm 1 k,instructionCycles] using CommitGolfCandidate.execute_ordinary_step _ _ _ _ k coins fj jmp
  exact a.next z

#print axioms latch_run
#print axioms tail_reference
end TwoPermutationPrototype.PhaseOpening
