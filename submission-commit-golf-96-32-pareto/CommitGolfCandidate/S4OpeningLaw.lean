import CommitGolfCandidate.S4CodecAdapter
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

private def finishOps : List Machine.Sym.Calc :=
  [.addi .x11 .x0 34,.slli .x11 .x11 11,.addi .x11 .x11 448,.addi .x5 .x0 1,.addi .x10 .x0 0]

private theorem finishPacked (s : MachineState) (pc : s.pc=pcAt 5269) (dest : s.getReg .x19=W (proofBase+70410))
    (xs : Proof) (len : xs.length=70410) (data : Contains s proofBase xs) :
    ∃ t, (∀ fuel,execute Machine.Code.opening.image (fuel+10489) s true=pure ⟨.success,t,10489,0⟩) ∧
      t.getReg .x11=W 70080 ∧ Contains t proofBase (Carry.packed xs) := by
  obtain ⟨pre,regs,mem,ip⟩:=Machine.evalMath .opening batchExitOps 5269 5274 s pc exitCode
    (fun c h=>bne_iff_ne.mp (List.all_eq_true.mp (by decide : batchExitOps.all (fun c=>c.dst != .x0)=true) c h))
    (fun _ h=>by cases h)
  let u:=batchEnd s
  have go:=Machine.jump .opening 5274 5876 u ip (by decide)
  let v:=u.setPC (pcAt 5876)
  have input : Codec.Input false v:=⟨(regs .x19).trans dest,(regs .x11).trans rfl⟩
  obtain ⟨w,frame,endPC,body⟩:=Codec.run Codec.byteSites false v rfl input
  have output:=Codec.packedProof v w xs len (data.mem mem) frame.memory
  obtain ⟨post,lastRegs,finalMem,haltPC⟩:=Machine.evalMath .opening finishOps 16353 16358 w endPC (by decide)
    (fun c h=>bne_iff_ne.mp (List.all_eq_true.mp (by decide : finishOps.all (fun c=>c.dst != .x0)=true) c h))
    (fun _ h=>by cases h)
  let t:=Machine.Sym.evaluated finishOps w
  have trace : Runs .opening s t 10488 10488:=((pre.trans go).trans body).trans post
  refine ⟨t,?_,(lastRegs .x11).trans rfl,output.mem finalMem⟩
  intro fuel
  have halt:=Machine.stop (by decide : 16358<Machine.Code.opening.count) haltPC (by rfl) ((lastRegs .x5).trans rfl) fuel true
  rw [show (Machine.Sym.evaluated finishOps w).getReg .x10=0 from (lastRegs .x10).trans rfl,if_pos rfl] at halt
  rw [show fuel+10489=(fuel+1)+10488 by omega,trace,halt,pure_bind];rfl

set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem rowPrices : rowTotal rowSteps 128=78143 ∧ rowTotal rowCost 128=80063 := by decide

set_option maxRecDepth 3000 in
private theorem capPrices : rowTotal fullTilePrice 21=5753 ∧ slotSum 3=92 ∧ slotPC true 3=5269 := by decide

theorem donePayload (td : Trapdoor) (ps : Positions) (batch : ps.card=128) : batchPayload td ps 171=rawOutput td ps := by
  have bound : (indices ps).length≤128:=by rw [indices,Finset.length_sort,batch]
  unfold rawOutput batchPayload;dsimp only;rw [if_pos (show ps.card=BATCH from batch),returnedRecords,List.take_of_length_le bound];rfl

private theorem batchTrace (td : Trapdoor) (ps : Positions) (batch : ps.card=128) :
    ∃ t,Runs .opening (initial td ps) t 84006 85926 ∧ t.pc=pcAt 5269 ∧ t.getReg .x19=W (proofBase+70410) ∧ Contains t proofBase (rawOutput td ps) := by
  obtain ⟨s,rstart,begin⟩:=batchEntry td ps batch
  obtain ⟨v,rowEnd,records⟩:=rows td ps s batch rstart 128 le_rfl
  obtain ⟨setupDone,setup⟩:=slotEntry td ps v batch rowEnd
  obtain ⟨u,tailStart,tiles⟩:=slotTiles td ps batch _ setupDone 21 le_rfl
  obtain ⟨t,last,tail⟩:=lanes td ps batch (21 : Fin 22) 3 (by decide) u tailStart
  rw [rowPrices.1,rowPrices.2] at records
  rw [capPrices.1] at tiles
  rw [capPrices.2.1] at tail
  exact ⟨t,(((begin.trans records).trans setup).trans tiles).trans tail,
    last.pc.trans (congrArg pcAt capPrices.2.2),last.dest,(donePayload td ps batch) ▸ last.bytes⟩

private theorem abi (c : Submission) (td : BitVec (8*c.sizes.trapdoor)) (ps : Positions) :
    c.run .opening (td,ps)=execute (c.image .opening) (c.steps .opening) (c.initialState .opening (td,ps)) true := rfl

attribute [local irreducible] execute

set_option maxRecDepth 10000 in
theorem batchOpened (td : Trapdoor) (ps : Positions) (batch : ps.card=128) :
    ∃ e,Opened td ps e ∧ e.cycles=96415 := by
  obtain ⟨s,path,pc,dest,data⟩:=batchTrace td ps batch
  have size : (rawOutput td ps).length=70410:=by rw [←donePayload td ps batch,batchPayloadSize td ps batch] <;> decide
  obtain ⟨t,halt,len,bytes⟩:=finishPacked s pc dest _ size data
  let e : Execution:=⟨.success,t,96415,0⟩
  let slack:=1099511627776-94495
  refine ⟨e,⟨?_,rfl,?_,?_⟩,rfl⟩
  · rw [abi];change execute Machine.Code.opening.image 1099511627776 (initial td ps) true=_
    rw [show 1099511627776=(slack+10489)+84006 by decide,path (slack+10489) true,halt slack,pure_bind];rfl
  · change true && decide ((t.getReg .x11).toNat≤17179869184)=true;rw [len];decide
  · rw [codedOutput,if_pos (show ps.card=BATCH from batch)]
    apply reportBytes t _ 96415 _ _ bytes
    · rw [Carry.packed_length];exact len
    · rw [Carry.packed_length];decide

private theorem allOpened (td : Trapdoor) (ps : Positions) :
    ∃ e,Opened td ps e ∧ (ps.card=BATCH → e.cycles≤96415) := by
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
  output td t s ps agree:=(allOpened td ps).choose_spec.1.bytes.trans (codedCorrect td ps t s agree)
end CommitGolfCandidate.S4.Open
