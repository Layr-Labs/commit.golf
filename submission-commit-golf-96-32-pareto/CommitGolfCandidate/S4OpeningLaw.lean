import CommitGolfCandidate.S4NormalFinish
import CommitGolfCandidate.S4SlotTiles
import CommitGolfCandidate.S4Resources
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Machine (W Runs proofBase)
open Late (Trapdoor pcAt)

def batchExitOps : List Machine.Sym.Calc:=[.addi .x11 .x0 34,.slli .x11 .x11 11,.addi .x11 .x11 778,.addi .x5 .x0 1,.addi .x10 .x0 0]
private theorem exitCode : (Machine.Fragment.arithmetic batchExitOps).valid .opening 5269 5274 := by decide
def batchEnd (s : MachineState) := Machine.Sym.evaluated batchExitOps s

theorem exitBatch (s : MachineState) (pc : s.pc=pcAt 5269) (fuel : Nat) :
    execute Machine.Code.opening.image (fuel+6) s true=pure ⟨.success,batchEnd s,6,0⟩ ∧
    (batchEnd s).mem=s.mem ∧ (batchEnd s).getReg .x11=W 70410 := by
  obtain ⟨run,regs,mem,atEnd⟩:=Machine.evalMath .opening batchExitOps 5269 5274 s pc exitCode
    (fun c h=>bne_iff_ne.mp (List.all_eq_true.mp (by decide : batchExitOps.all (fun c=>c.dst != .x0)=true) c h))
    (fun _ h=>by cases h)
  have halt:=Machine.stop (by decide : 5274<Machine.Code.opening.count) atEnd (by rfl) ((regs .x5).trans rfl) fuel true
  rw [show (Machine.Sym.evaluated batchExitOps s).getReg .x10=0 from (regs .x10).trans rfl,if_pos rfl] at halt
  refine ⟨?_,mem,(regs .x11).trans rfl⟩
  rw [show fuel+6=(fuel+1)+batchExitOps.length from rfl,run,halt,pure_bind];rfl

set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem rowPrices : rowTotal rowSteps 128=78143 ∧ rowTotal rowCost 128=79679 := by decide

set_option maxRecDepth 3000 in
private theorem capPrices : rowTotal fullTilePrice 21=5753 ∧ slotSum 3=92 ∧ slotPC true 3=5269 := by decide

theorem donePayload (td : Trapdoor) (ps : Positions) (batch : ps.card=128) : batchPayload td ps 171=rawOutput td ps := by
  have bound : (indices ps).length≤128:=by rw [indices,Finset.length_sort,batch]
  unfold rawOutput batchPayload;dsimp only;rw [if_pos (show ps.card=BATCH from batch),returnedRecords,List.take_of_length_le bound];rfl

private theorem batchTrace (td : Trapdoor) (ps : Positions) (batch : ps.card=128) :
    ∃ t,Runs .opening (initial td ps) t 84006 85542 ∧ t.pc=pcAt 5269 ∧ Contains t proofBase (rawOutput td ps) := by
  obtain ⟨s,rstart,begin⟩:=batchEntry td ps batch
  obtain ⟨v,rowEnd,records⟩:=rows td ps s batch rstart 128 le_rfl
  obtain ⟨setupDone,setup⟩:=slotEntry td ps v batch rowEnd
  obtain ⟨u,tailStart,tiles⟩:=slotTiles td ps batch _ setupDone 21 le_rfl
  obtain ⟨t,last,tail⟩:=lanes td ps batch (21 : Fin 22) 3 (by decide) u tailStart
  rw [rowPrices.1,rowPrices.2] at records
  rw [capPrices.1] at tiles
  rw [capPrices.2.1] at tail
  exact ⟨t,(((begin.trans records).trans setup).trans tiles).trans tail,
    last.pc.trans (congrArg pcAt capPrices.2.2),(donePayload td ps batch) ▸ last.bytes⟩

private theorem abi (c : Submission) (td : BitVec (8*c.sizes.trapdoor)) (ps : Positions) :
    c.run .opening (td,ps)=execute (c.image .opening) (c.steps .opening) (c.initialState .opening (td,ps)) true := rfl

attribute [local irreducible] execute

theorem batchOpened (td : Trapdoor) (ps : Positions) (batch : ps.card=128) :
    ∃ e,Opened td ps e ∧ e.cycles=85548 := by
  obtain ⟨t,run,pc,data⟩:=batchTrace td ps batch
  let e : Execution:=⟨.success,batchEnd t,85548,0⟩
  let slack:=1099511627776-84012
  obtain ⟨halt,mem,len⟩:=exitBatch t pc slack
  have size : (rawOutput td ps).length=70410:=by rw [←donePayload td ps batch,batchPayloadSize td ps batch] <;> decide
  refine ⟨e,⟨?_,rfl,?_,?_⟩,rfl⟩
  · rw [abi];change execute Machine.Code.opening.image 1099511627776 (initial td ps) true=_
    rw [show 1099511627776=(slack+6)+84006 by decide,run (slack+6) true,halt,pure_bind];rfl
  · change true && decide (((batchEnd t).getReg .x11).toNat≤17179869184)=true
    rw [len];decide
  · exact reportBytes (batchEnd t) (rawOutput td ps) 85548 (size.symm ▸ len)
      (by rw [size];exact (by decide : 70410≤17179869184)) (data.mem mem)

private theorem allOpened (td : Trapdoor) (ps : Positions) :
    ∃ e,Opened td ps e ∧ (ps.card=BATCH → e.cycles≤85548) := by
  by_cases b : ps.card=128
  · obtain ⟨e,works,price⟩:=batchOpened td ps b
    exact ⟨e,works,fun _=>price.le⟩
  · obtain ⟨e,works⟩:=ordinaryOpened td ps b
    exact ⟨e,works,fun yes=>False.elim (b yes)⟩

noncomputable def machineOpening : OpeningLaw where
  result td ps:=(allOpened td ps).choose
  run td ps:=(allOpened td ps).choose_spec.1.run
  success td ps:=(allOpened td ps).choose_spec.1.success
  exit td ps:=(allOpened td ps).choose_spec.1.exit
  priced td ps:=(allOpened td ps).choose_spec.2
  output td t s ps agree:=(allOpened td ps).choose_spec.1.bytes.trans (rawOutputCorrect td ps t s agree)
theorem machineHides : Late.submission.scheme.Hiding HIDING_ERROR := machineHiding machineOpening
end CommitGolfCandidate.S4.Open
