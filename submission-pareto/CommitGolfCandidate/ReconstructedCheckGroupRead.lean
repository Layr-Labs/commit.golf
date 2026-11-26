import CommitGolfCandidate.ReconstructedCheckCapWords

namespace CommitGolfCandidate.Reconstruction.CheckGroupRead
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckParentRun CheckCursorImage CheckStream
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000

def code : Array CheckLink.Op := #[
  .plain (.basic (.arith (.srli .x15 .x24 3))),
  .plain (.andi .x15 .x15 4088),
  .plain (.basic (.arith (.rr .add .x15 .x15 .x27))),
  .plain (.basic (.ld .x17 .x15 0)),
  .plain (.andi .x16 .x24 63),
  .plain (.basic (.arith (.rr .shr .x17 .x17 .x24))),
  .plain (.basic (.arith (.addi .x5 .x0 34))),
  .plain (.basic (.branch .lt .x16 .x5 20)),
  .plain (.basic (.ld .x15 .x15 8)),
  .plain (.basic (.arith (.rr .sub32 .x16 .x0 .x16))),
  .plain (.basic (.arith (.rr .shl .x15 .x15 .x16))),
  .plain (.basic (.arith (.rr .bitOr .x17 .x15 .x17)))]

theorem decoded : ∀ s : MachineState,∀ op,decode 558 code s.pc=some op→fetch image s=some op.instr :=
  decode_sound 558 code (by decide) (by unfold agree;decide +kernel)

def start (r : Nat) : State where
  regs:=fun reg=>match reg with
    | .x24=>ptr 1 r
    | .x27=>ptr 4 0
    | _=>.reg reg
  pc:=CommitBlocks.addr 558
  writes:=[]

def run (r : Nat) := CheckCursorOps.run CheckHeaderPlan.table (decode 558 code) (CommitBlocks.addr 570) 13 (start r)
def done (r : Nat) := (run r).getD ⟨0,start r⟩
def preserve := [Reg.x0,.x1,.x2,.x3,.x4,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,
  .x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30,.x31]

def receipt (r : Nat) :=
  let m:=(done r).state
  (run r).isSome && decide (m.get .x17=CheckHeaderPlan.field r 31 ∧ m.writes=[] ∧ (done r).ticks≤12) &&
    preserve.all (fun reg=>decide (m.get reg=(start r).get reg))

theorem checked (r : Fin 64) : receipt r=true := (by decide +kernel : ∀ k : Fin 64,receipt k=true) r

/-- The grouped 31-bit reader takes its crossing path precisely for displacements 34 through 63. -/
theorem positive (o : Oracle) (s : MachineState) (g : Reader) (r : Fin 64) (stream : Nat)
    (good : Placed g) (source : Source s g stream) (pc : s.pc=CommitBlocks.addr 558)
    (cursor : s.getReg .x24=BitVec.ofNat 64 (64*g.block+r.val)) (proof : s.getReg .x27=BitVec.ofNat 64 g.proofBase) :
    ∃ n t,n≤12 ∧ CheckRecorded.Segment o n s t [] ∧ t.pc=CommitBlocks.addr 570 ∧
      (t.getReg .x17).toNat%2^31=HonestStream.get stream (64*g.block+r.val) 31 ∧
      (∀ p,t.getMem p=s.getMem p) ∧ (∀ v∈preserve,t.getReg v=s.getReg v) := by
  let e:=env s g
  have init : Matches e (start r) s := by
    refine ⟨pc,?_,fun _=>rfl⟩
    intro reg;cases reg <;> try rfl
    · change s.getReg .x24=physical (env s g) (loc 1 r.val);rw [point];exact cursor
    · change s.getReg .x27=physical (env s g) (loc 4 0);rw [point];exact proof
  have ok:=checked r
  simp only [receipt,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
  obtain ⟨⟨defined,result,mem,cost⟩,keep⟩:=ok
  have replay : run r=some (done r) := by unfold done;cases h:run r <;> simp_all
  obtain ⟨t,seg,hm,_,pos⟩:=CheckCursorOps.run_sound o e (context s g (block_bound g good)) _ (header_layout s g good)
    _ decoded _ 13 _ s init (fun _ h=>by cases h) _ replay
  refine ⟨_,t,cost,seg,pos,?_,?_,?_⟩
  · rw [hm.regs,result]
    exact CheckField.bits e stream g.block r.val 31 (by decide) (by have:=r.isLt;omega) (by have:=r.isLt;omega)
      (input s g stream source)
  · intro p;rw [hm.mem,mem];rfl
  · intro v h;rw [hm.regs,keep v h,←init.regs]

end CommitGolfCandidate.Reconstruction.CheckGroupRead

