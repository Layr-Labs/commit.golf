import CommitGolfCandidate.GroupedScan
import CommitGolfCandidate.TwoPermutationCommitSetup
namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt)
set_option maxRecDepth 32000
set_option maxHeartbeats 1800000
attribute [local irreducible] execute image writeBits
def setupOps : List Instr :=
  [.ADDI .x18 .x10 0,.LUI .x19 131072,
   .ADD .x21 .x12 .x19,.ADDI .x20 .x21 2056,
   .SLLI .x22 .x19 3,.ADD .x24 .x21 .x22,.ADDI .x20 .x20 2056,.ADDI .x23 .x20 3872,
   .ADDI .x25 .x20 3648,.ADDI .x5 .x0 2,.ADDI .x10 .x24 8,.ADDI .x11 .x0 24,.ECALL,
   .ADDI .x26 .x20 3424,.ADDI .x5 .x0 0,.ADDI .x11 .x0 200,
   .ADDI .x13 .x0 1,.JAL .x0 181032]
/-- Setup continued after the tile latch (words 45,275..45,295): the even A-leaf slot gaps, the two restore
registers (x1 = next leaf base - quartet block, x2 = x1 + 56), the chain link x3 = -2912, the odd-quartet slot and
A-slot gaps (x8, x9, x18, x19 = even - 1224; x21, x22, x4, x7 = those + 112) and the odd restores (x31, x6 = +1224). -/
def extraOps : List Instr :=
  [.ADDI .x10 .x18 56,.ADDI .x27 .x20 112,.ADDI .x28 .x23 112,.ADDI .x29 .x25 112,.ADDI .x30 .x26 112,
   .SUB .x1 .x0 .x20,.ADDI .x2 .x1 1096,.ADDI .x1 .x1 1040,.ADDI .x3 .x0 (-2048),.ADDI .x3 .x3 (-864),
   .ADDI .x8 .x20 (-1224),.ADDI .x9 .x23 (-1224),.ADDI .x18 .x25 (-1224),.ADDI .x19 .x26 (-1224),
   .ADDI .x21 .x8 112,.ADDI .x22 .x9 112,.ADDI .x4 .x18 112,.ADDI .x7 .x19 112,
   .ADDI .x31 .x1 1224,.ADDI .x6 .x2 1224,.JAL .x0 1916056]
private theorem setup_decoded : ∀ i : Fin 18, Manifest.decodeBase (codeWord (0+i.val)) =
    some ((setupOps[i.val]?).getD .EBREAK) := by decide +kernel
theorem fetch_setup (s : MachineState) (i : Fin 18) (pc : s.pc=wordPC (0+i.val)) :
    fetch image s=some (.base ((setupOps[i.val]?).getD .EBREAK)) :=
  fetch_decoded s _ (by have := i.isLt;omega) pc _ (setup_decoded i)
private theorem extra_decoded : ∀ i : Fin 21, Manifest.decodeBase (codeWord (45275+i.val)) =
    some ((extraOps[i.val]?).getD .EBREAK) := by decide +kernel
theorem fetch_extra (s : MachineState) (i : Fin 21) (pc : s.pc=wordPC (45275+i.val)) :
    fetch image s=some (.base ((extraOps[i.val]?).getD .EBREAK)) :=
  fetch_decoded s _ (by have := i.isLt;omega) pc _ (extra_decoded i)

def prePrefix (s : MachineState) (i : Nat) := (setupOps.take i).foldl execInstrBr s
theorem pre_run (s : MachineState) (pc : s.pc=wordPC 0) (fuel : Nat) :
    execute image (12+fuel) s true = (do
      let e ← execute image fuel (prePrefix s 12) true; return e.charge 12 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := prePrefix s)
  intro i hi
  refine ⟨.base ((setupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (prePrefix s i).pc=wordPC (0+i) := by
      interval_cases i <;> simp only [prePrefix,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    have cell := fetch_setup (prePrefix s i) ⟨0+i,by omega⟩ (by simpa only [Nat.zero_add,Nat.add_assoc] using here)
    interval_cases i <;> exact cell
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def postOps : List Instr := setupOps.drop 13 ++ extraOps
def postPC (i : Nat) : Nat := if i≤4 then 13+i else 45275+(i-5)
def postPrefix (s : MachineState) (i : Nat) := (postOps.take i).foldl execInstrBr s
theorem post_run (s : MachineState) (pc : s.pc=wordPC 13) (fuel : Nat) :
    execute image (26+fuel) s true = (do
      let e ← execute image fuel (postPrefix s 26) true; return e.charge 26 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := postPrefix s)
  intro i hi
  refine ⟨.base ((postOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (postPrefix s i).pc=wordPC (postPC i) := by
      interval_cases i <;> simp only [postPrefix,postOps,postPC,setupOps,extraOps,List.drop,List.take,List.foldl,
        List.append,List.cons_append,List.nil_append,execInstrBr,MachineState.setPC,pc] <;> rfl
    by_cases low : i≤4
    · have cell := fetch_setup (postPrefix s i) ⟨13+i,by omega⟩ (by simpa only [postPC,if_pos low,Nat.zero_add] using here)
      interval_cases i <;> exact cell
    · have cell := fetch_extra (postPrefix s i) ⟨i-5,by omega⟩ (by simpa only [postPC,if_neg low] using here)
      interval_cases i <;> first | omega | exact cell
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

structure SeedRegs (s : MachineState) : Prop where
  pc : s.pc=wordPC 12
  selector : s.getReg .x5=2
  target : s.getReg .x10=BitVec.ofNat 64 (8*qSalt 0+8)
  size : s.getReg .x11=24
  message : s.getReg .x18=4096
  stride : s.getReg .x19=536870912
  quartet : s.getReg .x21=wordAddress (qSource 0)
  sentinel : s.getReg .x24=wordAddress (qSource 4194304)
  slot0 : s.getReg .x20=wordAddress (slotGap 0)
  slot1 : s.getReg .x23=wordAddress (slotGap 1)
  slot2 : s.getReg .x25=wordAddress (slotGap 2)

private def seedChunk (block : Nat) (s : MachineState) :=
  ((setupOps.drop (4*block)).take 4).foldl execInstrBr s

private structure Seed1 (s : MachineState) : Prop where
  pc : s.pc=wordPC 4
  message : s.getReg .x18=4096
  stride : s.getReg .x19=536870912
  quartet : s.getReg .x21=wordAddress (qSource 0)
  slot0a : s.getReg .x20=4831840296

private theorem seedBlock1 (s : MachineState) (h : CommitEntry s) : Seed1 (seedChunk 0 s) := by
  constructor <;> dsimp [seedChunk,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [h.pc,show s.regs .x10=4096 from h.message,
    show s.regs .x11=4294971392 from h.commitment,
    show s.regs .x12=4294971424 from h.heap,
    show signExtend12 (2056#12) = (-2040 : Word) by decide]
  all_goals first | rfl | decide

private structure Seed2 (s : MachineState) : Prop where
  pc : s.pc=wordPC 8
  message : s.getReg .x18=4096
  stride : s.getReg .x19=536870912
  quartet : s.getReg .x21=wordAddress (qSource 0)
  sentinel : s.getReg .x24=wordAddress (qSource 4194304)
  slot0 : s.getReg .x20=wordAddress (slotGap 0)
  slot1 : s.getReg .x23=wordAddress (slotGap 1)

private theorem seedBlock2 (s : MachineState) (h : Seed1 s) : Seed2 (seedChunk 1 s) := by
  constructor <;> dsimp [seedChunk,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [h.pc,show s.regs .x18=4096 from h.message,
    show s.regs .x19=536870912 from h.stride,
    show s.regs .x21=wordAddress (qSource 0) from h.quartet,
    show s.regs .x20=4831840296 from h.slot0a,
    show signExtend12 (2056#12) = (-2040 : Word) by decide]
  all_goals first | rfl | decide

private theorem seedBlock3 (s : MachineState) (h : Seed2 s) : SeedRegs (seedChunk 2 s) := by
  constructor <;> dsimp [seedChunk,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals simp only [h.pc,show s.regs .x18=4096 from h.message,
    show s.regs .x19=536870912 from h.stride,
    show s.regs .x21=wordAddress (qSource 0) from h.quartet,
    show s.regs .x24=wordAddress (qSource 4194304) from h.sentinel,
    show s.regs .x20=wordAddress (slotGap 0) from h.slot0,
    show s.regs .x23=wordAddress (slotGap 1) from h.slot1,
    show signExtend12 (3648#12) = (-448 : Word) by decide]
  all_goals first | rfl | decide

theorem seed_registers (s : MachineState) (entry : CommitEntry s) : SeedRegs (prePrefix s 12) :=
  seedBlock3 _ (seedBlock2 _ (seedBlock1 s entry))


abbrev Key := BitVec 192

def readyState (s : MachineState) (key : Key) :=
  postPrefix (writeBits (prePrefix s 12) (wordAddress (qSalt 0)+8) key) 26

private theorem post_live_frame (w pre : MachineState) (r : SeedRegs pre)
    (pc : w.pc=wordPC 13) (keep : ∀ reg,w.getReg reg=pre.getReg reg) :
    Live (postPrefix w 26) 0 := by
  have k18 : w.regs .x18=4096 := (keep .x18).trans r.message
  have k20 : w.regs .x20=wordAddress (slotGap 0) := (keep .x20).trans r.slot0
  have k23 : w.regs .x23=wordAddress (slotGap 1) := (keep .x23).trans r.slot1
  have k25 : w.regs .x25=wordAddress (slotGap 2) := (keep .x25).trans r.slot2
  have k24 : w.regs .x24=wordAddress (qSource 4194304) := (keep .x24).trans r.sentinel
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
  all_goals dsimp only [postPrefix,postOps,setupOps,extraOps,List.drop,List.take,List.foldl,List.append,
    List.cons_append,List.nil_append,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,startPC]
  all_goals simp (config := {decide := true}) only [k18,k20,k23,k25,k24,pc,↓reduceIte]
  all_goals decide

theorem ready_live (s : MachineState) (e : CommitEntry s) (k : Key) : Live (readyState s k) 0 := by
  let pre := prePrefix s 12
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
  have cell : fetch image pre=some (.base .ECALL) := fetch_setup pre ⟨12,by decide⟩ r.pc
  have raw : execute image (1+n) pre true = (do
      let k ← liftM ($ᵗ BitVec (8*(pre.getReg .x11).toNat) : ProbComp (BitVec (8*(pre.getReg .x11).toNat)))
      let z ← execute image n (writeBits pre (pre.getReg .x10) k) true
      return z.charge (1+((pre.getReg .x11).toNat+7)/8) 0) := by
    rw [Nat.add_comm 1 n,execute,cell]
    simp only [r.selector,valid];rfl
  rw [r.size,src] at raw;exact raw

attribute [local irreducible] prePrefix postPrefix

theorem setup_run (s : MachineState) (e : CommitEntry s) (fuel : Nat) :
    execute image (39+fuel) s true = (do
      let key ← liftM ($ᵗ Key : ProbComp Key)
      let z ← execute image fuel (readyState s key) true
      return z.charge 42 0) := by
  have r:=seed_registers s e
  rw [show 39+fuel=12+(1+(26+fuel)) by omega,pre_run s e.pc,draw_run _ r]
  simp only [bind_assoc];apply bind_congr;intro k
  rw [post_run _ (by rw [written_pc,r.pc];rfl)]
  simp only [readyState,bind_assoc,pure_bind,Execution.charge]
  apply bind_congr;intro z;cases z;simp [Nat.add_assoc] <;> omega


/-! ## The six words after the body (45,660..45,665; 45,656..45,659 are never executed)

They rebuild the three values the upper stage reads: `x8` = commitment (`a0 - 56`), `x21` = `Q` (`s8 - 2^32`)
and `x9` = trapdoor (`x21 - 2^29`). -/
def tailPostOps : List Instr :=
  [.ADDI .x8 .x10 (-56),.ADDI .x31 .x0 1,.SLLI .x31 .x31 32,.SUB .x21 .x24 .x31,.LUI .x31 131072,.SUB .x9 .x21 .x31]
private theorem tail_post_decoded : ∀ i : Fin 6, Manifest.decodeBase (codeWord (45660+i.val)) =
    some ((tailPostOps[i.val]?).getD .EBREAK) := by decide +kernel
theorem fetch_tail_post (s : MachineState) (i : Fin 6) (pc : s.pc=wordPC (45660+i.val)) :
    fetch image s=some (.base ((tailPostOps[i.val]?).getD .EBREAK)) :=
  fetch_decoded s _ (by have := i.isLt;omega) pc _ (tail_post_decoded i)

def tailPostPrefix (s : MachineState) (i : Nat) := (tailPostOps.take i).foldl execInstrBr s
theorem tail_post_run (s : MachineState) (pc : s.pc=wordPC 45660) (fuel : Nat) :
    execute image (6+fuel) s true = (do
      let e ← execute image fuel (tailPostPrefix s 6) true; return e.charge 6 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := tailPostPrefix s)
  intro i hi
  refine ⟨.base ((tailPostOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (tailPostPrefix s i).pc=wordPC (45660+i) := by
      interval_cases i <;> simp only [tailPostPrefix,tailPostOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    have cell := fetch_tail_post (tailPostPrefix s i) ⟨i,hi⟩ here
    interval_cases i <;> exact cell
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem tail_post_mem (s : MachineState) : memoryView (tailPostPrefix s 6)=memoryView s := rfl

/-- What the six words leave for the upper stage (`TailEntry`, with `tailStart = 45,666`). -/
theorem tail_post_regs (s : MachineState) (r : Live s N) :
    (tailPostPrefix s 6).pc=wordPC 45666 ∧ (tailPostPrefix s 6).getReg .x5=0 ∧
    (tailPostPrefix s 6).getReg .x8=4294971392 ∧ (tailPostPrefix s 6).getReg .x9=4294971424 ∧
    (tailPostPrefix s 6).getReg .x21=wordAddress 603980292 ∧ (tailPostPrefix s 6).getReg .x24=9126809632 := by
  have k10 : s.regs .x10=wordAddress (entryWord N) := r.msg
  have k24 : s.regs .x24=wordAddress (qSalt 0) := r.counter
  have k5 : s.regs .x5=0 := r.selector
  have pc : s.pc=wordPC 45660 := by rw [r.pc];unfold startPC;rw [if_pos rfl]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp only [tailPostPrefix,tailPostOps,List.take,List.foldl,execInstrBr,MachineState.setPC,
    MachineState.setReg,MachineState.getReg]
  all_goals simp (config := {decide := true}) only [k10,k24,k5,pc,↓reduceIte]
  all_goals decide

end TwoPermutationPrototype.Grouped
