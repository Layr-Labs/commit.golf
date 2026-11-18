import CommitGolfCandidate.GroupedScan
import CommitGolfCandidate.TwoPermutationCommitSetup
namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt)
set_option maxRecDepth 32000
set_option maxHeartbeats 1800000
attribute [local irreducible] execute image writeBits
def setupOps : List Instr :=
  [.ADDI .x8 .x11 0,.ADDI .x9 .x12 0,.ADDI .x18 .x10 0,.LUI .x19 131072,
   .ADD .x21 .x9 .x19,.SLLI .x22 .x19 3,.ADD .x22 .x21 .x22,.ADDI .x24 .x22 0,
   .ADDI .x20 .x21 2056,.ADDI .x20 .x20 2056,.ADDI .x23 .x20 3872,.ADDI .x25 .x20 3648,
   .ADDI .x5 .x0 2,.ADDI .x10 .x24 8,.ADDI .x11 .x0 24,.ECALL,
   .ADDI .x26 .x20 3424,.ADDI .x5 .x0 0,.ADDI .x11 .x0 200,
   .ADDI .x13 .x0 1,.JAL .x0 183064]
/-- Setup continued after the tile latch (words 45,786..45,797): the A-leaf slot offsets, the latch bound,
the two restore registers (x1 = next leaf base - quartet block, x2 = x1 + 56) and the chain link x3 = -2912. -/
def extraOps : List Instr :=
  [.ADDI .x10 .x18 56,.ADDI .x27 .x20 112,.ADDI .x28 .x23 112,.ADDI .x29 .x25 112,.ADDI .x30 .x26 112,
   .ADDI .x6 .x8 56,.SUB .x1 .x0 .x20,.ADDI .x2 .x1 1096,.ADDI .x1 .x1 1040,.ADDI .x3 .x0 (-2048),.ADDI .x3 .x3 (-864),
   .JAL .x0 1914048]
private theorem setup_decoded : ∀ i : Fin 21, Manifest.decodeBase (codeWord (0+i.val)) =
    some ((setupOps[i.val]?).getD .EBREAK) := by decide +kernel
theorem fetch_setup (s : MachineState) (i : Fin 21) (pc : s.pc=wordPC (0+i.val)) :
    fetch image s=some (.base ((setupOps[i.val]?).getD .EBREAK)) :=
  fetch_decoded s _ (by have := i.isLt;omega) pc _ (setup_decoded i)
private theorem extra_decoded : ∀ i : Fin 12, Manifest.decodeBase (codeWord (45786+i.val)) =
    some ((extraOps[i.val]?).getD .EBREAK) := by decide +kernel
theorem fetch_extra (s : MachineState) (i : Fin 12) (pc : s.pc=wordPC (45786+i.val)) :
    fetch image s=some (.base ((extraOps[i.val]?).getD .EBREAK)) :=
  fetch_decoded s _ (by have := i.isLt;omega) pc _ (extra_decoded i)

def prePrefix (s : MachineState) (i : Nat) := (setupOps.take i).foldl execInstrBr s
theorem pre_run (s : MachineState) (pc : s.pc=wordPC 0) (fuel : Nat) :
    execute image (15+fuel) s true = (do
      let e ← execute image fuel (prePrefix s 15) true; return e.charge 15 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := prePrefix s)
  intro i hi
  refine ⟨.base ((setupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (prePrefix s i).pc=wordPC (0+i) := by
      interval_cases i <;> simp only [prePrefix,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    have cell := fetch_setup (prePrefix s i) ⟨0+i,by omega⟩ (by simpa only [Nat.zero_add,Nat.add_assoc] using here)
    interval_cases i <;> exact cell
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def postOps : List Instr := setupOps.drop 16 ++ extraOps
def postPC (i : Nat) : Nat := if i≤4 then 16+i else 45786+(i-5)
def postPrefix (s : MachineState) (i : Nat) := (postOps.take i).foldl execInstrBr s
theorem post_run (s : MachineState) (pc : s.pc=wordPC 16) (fuel : Nat) :
    execute image (17+fuel) s true = (do
      let e ← execute image fuel (postPrefix s 17) true; return e.charge 17 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := postPrefix s)
  intro i hi
  refine ⟨.base ((postOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (postPrefix s i).pc=wordPC (postPC i) := by
      interval_cases i <;> simp only [postPrefix,postOps,postPC,setupOps,extraOps,List.drop,List.take,List.foldl,
        List.append,List.cons_append,List.nil_append,execInstrBr,MachineState.setPC,pc] <;> rfl
    by_cases low : i≤4
    · have cell := fetch_setup (postPrefix s i) ⟨16+i,by omega⟩ (by simpa only [postPC,if_pos low,Nat.zero_add] using here)
      interval_cases i <;> exact cell
    · have cell := fetch_extra (postPrefix s i) ⟨i-5,by omega⟩ (by simpa only [postPC,if_neg low] using here)
      interval_cases i <;> first | omega | exact cell
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

structure SeedRegs (s : MachineState) : Prop where
  pc : s.pc=wordPC 15
  selector : s.getReg .x5=2
  target : s.getReg .x10=BitVec.ofNat 64 (8*qSalt 0+8)
  size : s.getReg .x11=24
  output : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  message : s.getReg .x18=4096
  stride : s.getReg .x19=536870912
  quartet : s.getReg .x21=wordAddress (qSource 0)
  salt : s.getReg .x22=wordAddress (qSalt 0)
  sentinel : s.getReg .x24=wordAddress (qSource 4194304)
  slot0 : s.getReg .x20=wordAddress (slotGap 0)
  slot1 : s.getReg .x23=wordAddress (slotGap 1)
  slot2 : s.getReg .x25=wordAddress (slotGap 2)

private def seedChunk (block : Nat) (s : MachineState) := ((setupOps.drop (5*block)).take 5).foldl execInstrBr s

private structure Seed1 (s : MachineState) : Prop where
  pc : s.pc=wordPC 5
  output : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  message : s.getReg .x18=4096
  stride : s.getReg .x19=536870912
  quartet : s.getReg .x21=wordAddress (qSource 0)

private theorem seedBlock1 (s : MachineState) (h : CommitEntry s) : Seed1 (seedChunk 0 s) := by
  constructor <;> dsimp [seedChunk,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [h.pc,show s.regs .x10=4096 from h.message,
    show s.regs .x11=4294971392 from h.commitment,
    show s.regs .x12=4294971424 from h.heap]
  all_goals rfl

private structure Seed2 (s : MachineState) : Prop where
  pc : s.pc=wordPC 10
  output : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  message : s.getReg .x18=4096
  stride : s.getReg .x19=536870912
  quartet : s.getReg .x21=wordAddress (qSource 0)
  salt : s.getReg .x22=wordAddress (qSalt 0)
  sentinel : s.getReg .x24=wordAddress (qSource 4194304)
  slot0 : s.getReg .x20=wordAddress (slotGap 0)

private theorem seedBlock2 (s : MachineState) (h : Seed1 s) : Seed2 (seedChunk 1 s) := by
  constructor <;> dsimp [seedChunk,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [h.pc,show s.regs .x8=4294971392 from h.output,
    show s.regs .x9=4294971424 from h.heap,
    show s.regs .x18=4096 from h.message,
    show s.regs .x19=536870912 from h.stride,
    show s.regs .x21=wordAddress (qSource 0) from h.quartet]
  all_goals rfl

private theorem seedBlock3 (s : MachineState) (h : Seed2 s) : SeedRegs (seedChunk 2 s) := by
  constructor <;> dsimp [seedChunk,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [h.pc,show s.regs .x8=4294971392 from h.output,
    show s.regs .x9=4294971424 from h.heap,
    show s.regs .x18=4096 from h.message,
    show s.regs .x19=536870912 from h.stride,
    show s.regs .x21=wordAddress (qSource 0) from h.quartet,
    show s.regs .x22=wordAddress (qSalt 0) from h.salt,
    show s.regs .x24=wordAddress (qSource 4194304) from h.sentinel,
    show s.regs .x20=wordAddress (slotGap 0) from h.slot0]
  all_goals rfl

theorem seed_registers (s : MachineState) (entry : CommitEntry s) : SeedRegs (prePrefix s 15) :=
  seedBlock3 _ (seedBlock2 _ (seedBlock1 s entry))


abbrev Key := BitVec 192

def readyState (s : MachineState) (key : Key) :=
  postPrefix (writeBits (prePrefix s 15) (wordAddress (qSalt 0)+8) key) 17

private theorem post_live_frame (w pre : MachineState) (r : SeedRegs pre)
    (pc : w.pc=wordPC 16) (keep : ∀ reg,w.getReg reg=pre.getReg reg) :
    Live (postPrefix w 17) 0 := by
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,rfl⟩,?_,?_,?_,?_,?_,?_⟩
  · change w.getReg .x18+signExtend12 56=_
    rw [keep,r.message];decide
  · exact (keep .x20).trans r.slot0
  · exact (keep .x23).trans r.slot1
  · exact (keep .x25).trans r.slot2
  · change w.getReg .x20+signExtend12 3424=_
    rw [keep,r.slot0];rfl
  · change w.getReg .x20+signExtend12 112=_
    rw [keep,r.slot0];rfl
  · change w.getReg .x23+signExtend12 112=_
    rw [keep,r.slot1];rfl
  · change w.getReg .x25+signExtend12 112=_
    rw [keep,r.slot2];rfl
  · change (w.getReg .x20+signExtend12 3424)+signExtend12 112=_
    rw [keep,r.slot0];rfl
  · change (w.getReg .x0-w.getReg .x20)+signExtend12 1040=_
    rw [keep .x20,r.slot0]
    show (0#64-wordAddress (slotGap 0))+signExtend12 1040#12=-wordAddress 603979652
    decide
  · change (w.getReg .x0-w.getReg .x20)+signExtend12 1096=_
    rw [keep .x20,r.slot0]
    show (0#64-wordAddress (slotGap 0))+signExtend12 1096#12=-wordAddress 603979645
    decide
  · show (0#64+signExtend12 2048#12)+signExtend12 3232#12=-wordAddress 364
    decide
  · exact (keep .x24).trans r.sentinel
  · rw [show startPC 0=wordPC 21 from rfl]
    simp only [postPrefix,postOps,setupOps,extraOps,List.drop,List.take,List.foldl,List.append,List.cons_append,
      List.nil_append,execInstrBr,MachineState.setPC,pc]
    rfl
  · change w.getReg .x8+signExtend12 56=_
    rw [keep,r.output];rfl
  · exact (keep .x8).trans r.output
  · exact (keep .x9).trans r.heap
  · exact (keep .x19).trans r.stride
  · exact (keep .x21).trans r.quartet

theorem ready_live (s : MachineState) (e : CommitEntry s) (k : Key) : Live (readyState s k) 0 := by
  let pre := prePrefix s 15
  have r:=seed_registers s e
  refine post_live_frame _ pre r ?_ (fun reg => writeBits_register ..)
  rw [written_pc,r.pc];rfl

private theorem draw_run (pre : MachineState) (r : SeedRegs pre) (n : Nat) :
    execute image (1+n) pre true = (do
      let k ← liftM ($ᵗ Key : ProbComp Key)
      let z ← execute image n (writeBits pre (wordAddress (qSalt 0)+8) k) true
      return z.charge 4 0) := by
  have src : pre.getReg .x10=wordAddress (qSalt 0)+8 := r.target
  have valid : randomArgumentsValid pre=true := by rw [randomArgumentsValid,src,r.size];decide
  have cell : fetch image pre=some (.base .ECALL) := fetch_setup pre ⟨15,by decide⟩ r.pc
  have raw : execute image (1+n) pre true = (do
      let k ← liftM ($ᵗ BitVec (8*(pre.getReg .x11).toNat) : ProbComp (BitVec (8*(pre.getReg .x11).toNat)))
      let z ← execute image n (writeBits pre (pre.getReg .x10) k) true
      return z.charge (1+((pre.getReg .x11).toNat+7)/8) 0) := by
    rw [Nat.add_comm 1 n,execute,cell]
    simp only [r.selector,valid];rfl
  rw [r.size,src] at raw;exact raw

attribute [local irreducible] prePrefix postPrefix

theorem setup_run (s : MachineState) (e : CommitEntry s) (fuel : Nat) :
    execute image (33+fuel) s true = (do
      let key ← liftM ($ᵗ Key : ProbComp Key)
      let z ← execute image fuel (readyState s key) true
      return z.charge 36 0) := by
  have r:=seed_registers s e
  rw [show 33+fuel=15+(1+(17+fuel)) by omega,pre_run s e.pc,draw_run _ r]
  simp only [bind_assoc];apply bind_congr;intro k
  rw [post_run _ (by rw [written_pc,r.pc];rfl)]
  simp only [readyState,bind_assoc,pure_bind,Execution.charge]
  apply bind_congr;intro z;cases z;simp [Nat.add_assoc] <;> omega

end TwoPermutationPrototype.Grouped
