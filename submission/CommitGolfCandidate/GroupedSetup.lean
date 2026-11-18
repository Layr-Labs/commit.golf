import CommitGolfCandidate.GroupedScan
import CommitGolfCandidate.GroupedQImage
import CommitGolfCandidate.TwoPermutationCommitSetup
namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt)
set_option maxRecDepth 32000
set_option maxHeartbeats 1800000
attribute [local irreducible] execute image writeBits
def setupOps : List Instr :=
  [.ADDI .x8 .x11 0,.ADDI .x9 .x12 0,.ADDI .x18 .x10 0,.LUI .x19 131072,
   .LUI .x21 278528,.ADD .x21 .x9 .x21,.LUI .x22 376832,.ADD .x24 .x21 .x22,
   .LUI .x23 1,.LUI .x7 1,.ADDI .x7 .x7 2048,.ADD .x20 .x21 .x7,
   .ADDI .x5 .x0 2,.ADDI .x10 .x24 8,.ADDI .x11 .x0 24,.ECALL,
   .ADD .x25 .x24 .x7,.ADDI .x5 .x0 0,.ADDI .x11 .x0 200,
   .ADDI .x13 .x0 1,.ADDI .x10 .x18 0]
private theorem setup_decoded : ∀ i : Fin 21, Manifest.decodeBase (codeWord (0+i.val)) =
    some ((setupOps[i.val]?).getD .EBREAK) := by decide +kernel
theorem fetch_setup (s : MachineState) (i : Fin 21) (pc : s.pc=wordPC (0+i.val)) :
    fetch image s=some (.base ((setupOps[i.val]?).getD .EBREAK)) :=
  fetch_decoded s _ (by have := i.isLt;omega) pc _ (setup_decoded i)

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

def postPrefix (s : MachineState) (i : Nat) := ((setupOps.drop 16).take i).foldl execInstrBr s
theorem post_run (s : MachineState) (pc : s.pc=wordPC 16) (fuel : Nat) :
    execute image (5+fuel) s true = (do
      let e ← execute image fuel (postPrefix s 5) true; return e.charge 5 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := postPrefix s)
  intro i hi
  refine ⟨.base (((setupOps.drop 16)[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (postPrefix s i).pc=wordPC (16+i) := by
      interval_cases i <;> simp only [postPrefix,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    have cell := fetch_setup (postPrefix s i) ⟨16+i,by omega⟩ (by simpa only [Nat.zero_add,Nat.add_assoc] using here)
    interval_cases i <;> exact cell
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def qStartPrefix (s : MachineState) (i : Nat) := (quadSetupOps.take i).foldl execInstrBr s
theorem qStart_run (s : MachineState) (pc : s.pc=wordPC 45591) (fuel : Nat) :
    execute image (3+fuel) s true = (do
      let e ← execute image fuel (qStartPrefix s 3) true; return e.charge 3 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := qStartPrefix s)
  intro i hi
  refine ⟨.base ((quadSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (qStartPrefix s i).pc=wordPC (45591+i) := by
      interval_cases i <;> simp only [qStartPrefix,quadSetupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    have cell := fetch_quadSetup (qStartPrefix s i) ⟨0+i,by omega⟩ (by simpa only [Nat.zero_add,Nat.add_assoc] using here)
    interval_cases i <;> exact cell
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def upStartPrefix (s : MachineState) (i : Nat) := (upperSetupOps.take i).foldl execInstrBr s
theorem upStart_run (s : MachineState) (pc : s.pc=wordPC 70172) (fuel : Nat) :
    execute image (6+fuel) s true = (do
      let e ← execute image fuel (upStartPrefix s 6) true; return e.charge 6 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := upStartPrefix s)
  intro i hi
  refine ⟨.base ((upperSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (upStartPrefix s i).pc=wordPC (70172+i) := by
      interval_cases i <;> simp only [upStartPrefix,upperSetupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    have cell := fetch_upperSetup (upStartPrefix s i) ⟨0+i,by omega⟩ (by simpa only [Nat.zero_add,Nat.add_assoc] using here)
    interval_cases i <;> exact cell
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
  cursor : s.getReg .x20=wordAddress (qSource 0)+2048
  sentinel : s.getReg .x24=wordAddress (qSource 4194304)
  bigStride : s.getReg .x23=4096
  bias : s.getReg .x7=2048

private def seedChunk (block : Nat) (s : MachineState) := ((setupOps.drop (5*block)).take 5).foldl execInstrBr s

private structure Seed1 (s : MachineState) : Prop where
  pc : s.pc=wordPC 5
  output : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  message : s.getReg .x18=4096
  stride : s.getReg .x19=536870912
  quartetHigh : s.getReg .x21=1140850688

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
  sentinel : s.getReg .x24=wordAddress (qSource 4194304)
  bigStride : s.getReg .x23=4096
  temp : s.getReg .x7=4096

private theorem seedBlock2 (s : MachineState) (h : Seed1 s) : Seed2 (seedChunk 1 s) := by
  constructor <;> dsimp [seedChunk,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [h.pc,show s.regs .x8=4294971392 from h.output,
    show s.regs .x9=4294971424 from h.heap,
    show s.regs .x18=4096 from h.message,
    show s.regs .x19=536870912 from h.stride,
    show s.regs .x21=1140850688 from h.quartetHigh]
  all_goals rfl

private theorem seedBlock3 (s : MachineState) (h : Seed2 s) : SeedRegs (seedChunk 2 s) := by
  constructor <;> dsimp [seedChunk,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [h.pc,show s.regs .x8=4294971392 from h.output,
    show s.regs .x9=4294971424 from h.heap,
    show s.regs .x18=4096 from h.message,
    show s.regs .x19=536870912 from h.stride,
    show s.regs .x21=wordAddress (qSource 0) from h.quartet,
    show s.regs .x24=wordAddress (qSource 4194304) from h.sentinel,
    show s.regs .x23=4096 from h.bigStride,
    show s.regs .x7=4096 from h.temp]
  all_goals rfl

theorem seed_registers (s : MachineState) (entry : CommitEntry s) : SeedRegs (prePrefix s 15) :=
  seedBlock3 _ (seedBlock2 _ (seedBlock1 s entry))


abbrev Key := BitVec 192

def readyState (s : MachineState) (key : Key) :=
  postPrefix (writeBits (prePrefix s 15) (wordAddress (qSalt 0)+8) key) 5

private theorem post_live_frame (w pre : MachineState) (r : SeedRegs pre)
    (pc : w.pc=wordPC 16) (keep : ∀ reg,w.getReg reg=pre.getReg reg) :
    Live (postPrefix w 5) 0 := by
  refine ⟨⟨?_,?_,?_,?_,?_,rfl,rfl,rfl⟩,?_,?_,?_,?_,?_,?_⟩
  · change w.getReg .x18+0=_
    rw [keep,r.message];rfl
  · exact (keep .x20).trans r.cursor
  · exact (keep .x23).trans r.bigStride
  · exact (keep .x24).trans r.sentinel
  · trivial
  · change w.pc+4+4+4+4+4=_
    rw [pc];rfl
  · change w.getReg .x24+w.getReg .x7=_
    rw [keep,keep,r.sentinel,r.bias]
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
    execute image (21+fuel) s true = (do
      let key ← liftM ($ᵗ Key : ProbComp Key)
      let z ← execute image fuel (readyState s key) true
      return z.charge 24 0) := by
  have r:=seed_registers s e
  rw [show 21+fuel=15+(1+(5+fuel)) by omega,pre_run s e.pc,draw_run _ r]
  simp only [bind_assoc];apply bind_congr;intro k
  rw [post_run _ (by rw [written_pc,r.pc];rfl)]
  simp only [readyState,bind_assoc,pure_bind,Execution.charge]
  apply bind_congr;intro z;cases z;simp [Nat.add_assoc] <;> omega

end TwoPermutationPrototype.Grouped
