import CommitGolfCandidate.QuartetCommitQStep
import CommitGolfCandidate.TwoPermutationPackedParents
namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
attribute [local irreducible] execute image writeBits

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
    execute image (6+fuel) s true = (do
      let e ← execute image fuel (postPrefix s 6) true; return e.charge 6 0) := by
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
theorem qStart_run (s : MachineState) (pc : s.pc=wordPC 45224) (fuel : Nat) :
    execute image (3+fuel) s true = (do
      let e ← execute image fuel (qStartPrefix s 3) true; return e.charge 3 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := qStartPrefix s)
  intro i hi
  refine ⟨.base ((quadSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (qStartPrefix s i).pc=wordPC (45224+i) := by
      interval_cases i <;> simp only [qStartPrefix,quadSetupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    have cell := fetch_quadSetup (qStartPrefix s i) ⟨0+i,by omega⟩ (by simpa only [Nat.zero_add,Nat.add_assoc] using here)
    interval_cases i <;> exact cell
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def upStartPrefix (s : MachineState) (i : Nat) := (upperSetupOps.take i).foldl execInstrBr s
theorem upStart_run (s : MachineState) (pc : s.pc=wordPC 46765) (fuel : Nat) :
    execute image (6+fuel) s true = (do
      let e ← execute image fuel (upStartPrefix s 6) true; return e.charge 6 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := upStartPrefix s)
  intro i hi
  refine ⟨.base ((upperSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (upStartPrefix s i).pc=wordPC (46765+i) := by
      interval_cases i <;> simp only [upStartPrefix,upperSetupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    have cell := fetch_upperSetup (upStartPrefix s i) ⟨0+i,by omega⟩ (by simpa only [Nat.zero_add,Nat.add_assoc] using here)
    interval_cases i <;> exact cell
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

structure SeedRegs (s : MachineState) : Prop where
  pc : s.pc=wordPC 15
  selector : s.getReg .x5=2
  target : s.getReg .x10=wordAddress (qSalt 0)
  size : s.getReg .x11=268435456
  output : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  message : s.getReg .x18=4096
  stride : s.getReg .x19=536870912
  quartet : s.getReg .x21=wordAddress (qSource 0)
  cursor : s.getReg .x20=wordAddress (qSource 0)+2048
  salt : s.getReg .x22=wordAddress (qSalt 0)
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
  bigStride : s.getReg .x23=4096
  temp : s.getReg .x7=4096

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
    show s.regs .x23=4096 from h.bigStride,
    show s.regs .x7=4096 from h.temp]
  all_goals rfl

theorem seed_registers (s : MachineState) (entry : CommitEntry s) : SeedRegs (prePrefix s 15) :=
  seedBlock3 _ (seedBlock2 _ (seedBlock1 s entry))

def qReady (s : MachineState) {bits : Nat} (coins : BitVec bits) :=
  postPrefix (writeBits (prePrefix s 15) (wordAddress (qSalt 0)) coins) 6

theorem q_draw_run (s : MachineState) (r : SeedRegs s) (fuel : Nat) :
    execute image (1+fuel) s true = (do
      let answer ← liftM ($ᵗ BitVec (8*(s.getReg .x11).toNat) : ProbComp (BitVec (8*(s.getReg .x11).toNat)))
      let e ← execute image fuel (writeBits s (wordAddress (qSalt 0)) answer) true
      return e.charge 33554433 0) := by
  have fetched : fetch image s=some (.base .ECALL) := fetch_setup s ⟨15,by decide⟩ r.pc
  have valid : randomArgumentsValid s=true := by rw [randomArgumentsValid,r.target,r.size];decide
  have cost : 1+((s.getReg .x11).toNat+7)/8=33554433 := by rw [r.size];rfl
  rw [Nat.add_comm 1 fuel,execute,fetched]
  simp only [r.selector,valid,r.target,cost];rfl

theorem q_setup_run (s : MachineState) (entry : CommitEntry s) (fuel : Nat) :
    execute image (22+fuel) s true = (do
      let answer ← liftM ($ᵗ BitVec (8*((prePrefix s 15).getReg .x11).toNat) :
        ProbComp (BitVec (8*((prePrefix s 15).getReg .x11).toNat)))
      let e ← execute image fuel (qReady s answer) true;return e.charge 33554454 0) := by
  have r:=seed_registers s entry
  rw [show 22+fuel=15+(1+(6+fuel)) by omega,pre_run s entry.pc,q_draw_run _ r]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support;intro answer _
  rw [post_run _ (by rw [written_pc,r.pc];rfl)]
  simp [qReady,Execution.charge,← Nat.add_assoc]

structure StartLeafRegs (s : MachineState) : Prop where
  pc : s.pc=wordPC 22
  source : s.getReg .x10=4096
  cursor : s.getReg .x20=wordAddress (qSource 0)+2048
  salt : s.getReg .x22=wordAddress (qSalt 0)+2048
  bigStride : s.getReg .x23=4096
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1
  sentinel : s.getReg .x25=wordAddress (qSource 4194304)+2048
  quartet : s.getReg .x21=wordAddress (qSource 0)
  stop : s.getReg .x24=wordAddress (qSource 4194304)
  output : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  stride : s.getReg .x19=536870912

private theorem post_registers (pre : MachineState) (r : SeedRegs pre) {bits : Nat} (coins : BitVec bits) :
    StartLeafRegs (postPrefix (writeBits pre (wordAddress (qSalt 0)) coins) 6) := by
  let before := writeBits pre (wordAddress (qSalt 0)) coins
  have saved (reg : Reg) : before.getReg reg=pre.getReg reg := CommitGolfCandidate.writeBits_register .. 
  change StartLeafRegs (postPrefix before 6)
  constructor
  · change before.pc+4+4+4+4+4+4=_
    rw [show before.pc=pre.pc+4 from written_pc ..,r.pc];rfl
  · change before.getReg .x18+0=_
    rw [saved,r.message];rfl
  · exact (saved .x20).trans r.cursor
  · change before.getReg .x22+before.getReg .x7=_
    rw [saved,saved,r.salt,r.bias]
  · exact (saved .x23).trans r.bigStride
  · rfl
  · rfl
  · rfl
  · change before.getReg .x24+before.getReg .x7=_
    rw [saved,saved,r.sentinel,r.bias]
  · exact (saved .x21).trans r.quartet
  · exact (saved .x24).trans r.sentinel
  · exact (saved .x8).trans r.output
  · exact (saved .x9).trans r.heap
  · exact (saved .x19).trans r.stride

theorem q_ready_regs (s : MachineState) (entry : CommitEntry s) {bits : Nat} (coins : BitVec bits) :
    StartLeafRegs (qReady s coins) := post_registers _ (seed_registers s entry) _

theorem q_ready_mem (s : MachineState) {bits : Nat} (coins : BitVec bits) :
    (qReady s coins).mem=(writeBits s (wordAddress (qSalt 0)) coins).mem := by
  exact CommitGolfCandidate.write_bits_memory_congr (prePrefix s 15) s _ coins rfl

end TwoPermutationPrototype.QuartetCommit
