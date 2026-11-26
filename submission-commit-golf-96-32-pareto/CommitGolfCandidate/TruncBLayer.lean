import CommitGolfCandidate.TruncBFinish
import CommitGolfCandidate.TruncBRowHash
import CommitGolfCandidate.TruncBRegion
import CommitGolfCandidate.TruncBProgress
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 250000
attribute [local irreducible] readBuffer storedAt

def sourceRow (p : Nat) := 16384+96*p
def outSlot (p : Nat) := 4608+32*p
def inSlot (p : Nat) := 10871707680+32*p
def leftId (p : Fin 128) : Fin 256 := ⟨2*p.val,by have :=p.isLt;omega⟩
def rightId (p : Fin 128) : Fin 256 := ⟨2*p.val+1,by have :=p.isLt;omega⟩
theorem leftCell (p : Fin 128) : cell (leftId p).val=sourceRow p.val := by
  unfold cell sourceRow;rw [show (leftId p).val=2*p.val by rfl,heap_offset_even]
theorem rightCell (p : Fin 128) : cell (rightId p).val=sourceRow p.val+32 := by
  unfold cell sourceRow;rw [show (rightId p).val=2*p.val+1 by rfl,heap_offset_odd];omega

structure PairInvariant (H : Compression) (input : CheckInput) (k : Nat) (s : MachineState) : Prop where
  bound : k≤128
  pc : s.pc=if k=128 then 5592 else 5416
  slots : s.getReg .x19=BitVec.ofNat 64 (inSlot k)
  marks : s.getReg .x22=BitVec.ofNat 64 (flag (2*k))
  source : s.getReg .x23=BitVec.ofNat 64 (sourceRow k)
  dest : s.getReg .x24=BitVec.ofNat 64 (outSlot k)
  root : s.getReg .x26=4294971392
  remaining : s.getReg .x27=BitVec.ofNat 64 (128-k)
  rootDigest : digestAt s 4294971392=input.commitment
  left : ∀ p : Fin 128,k≤p.val → storedAt s (leftId p)=(childrenAt H input p.val).left
  right : ∀ p : Fin 128,k≤p.val → storedAt s (rightId p)=(childrenAt H input p.val).right
  gap : ∀ p : Fin 128,k≤p.val → digestAt s (sourceRow p.val+64)=0
  ins : ∀ p : Fin 128,k≤p.val → digestAt s (inSlot p.val)=supplied input p.val
  outs : ∀ p : Fin 128,p.val<k → digestAt s (outSlot p.val)=capTable H input p.val

private theorem initPairsInfo (s : MachineState) (pc : s.pc=5376) :
    let t:=initPairsState s
    t.pc=5416 ∧ t.getReg .x22=12288 ∧ t.getReg .x23=16384 ∧ t.getReg .x24=4608 ∧ t.getReg .x27=128 ∧
    t.getReg .x26=s.getReg .x26 ∧ t.getReg .x19=s.getReg .x19 ∧ t.mem=s.mem := by
  simp [initPairsState,initPairsOps,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,signExtend12,pc]

private theorem storedMem {s t : MachineState} (m : s.mem=t.mem) (u : Fin 256) : storedAt s u=storedAt t u := by
  have b:= byteMem m (flag u.val)
  unfold byteAt at b
  unfold storedAt;rw [b,read_buffer_memory_congr _ _ m]

attribute [local irreducible] initPairsState
theorem pairStart (o : Oracle) (input : CheckInput) (s : MachineState)
    (inv : RecordInvariant o.compression input 128 s) :
    Runs o s (initPairsState s) 10 0 ∧ PairInvariant o.compression input 0 (initPairsState s) := by
  have pc : s.pc=5376 := by simpa using inv.pc
  have run := pureBlockRuns (o:=o) (fun fuel => initPairsRun s pc fuel false)
  obtain ⟨p0,f,c,d,n,rt,sl,mem⟩ := initPairsInfo s pc
  have rootEq := (readHigh s _ inv.inputWords 4294971392 (by decide) (by decide) (by decide)).trans (check_input_commitment input)
  refine ⟨run,⟨by decide,p0,sl.trans inv.slots,f,c,d,rt.trans inv.root,n,?_,?_,?_,?_,?_,?_⟩⟩
  · exact (read_buffer_memory_congr _ _ mem _ _).trans rootEq
  · intro p _;exact (storedMem mem _).trans (inv.table (leftId p))
  · intro p _;exact (storedMem mem _).trans (inv.table (rightId p))
  · intro p _;exact (read_buffer_memory_congr _ _ mem _ _).trans (inv.gap p)
  · intro p _
    have bp:=p.isLt
    exact (read_buffer_memory_congr _ _ mem _ _).trans
      (readHigh s _ inv.inputWords (inSlot p.val) (by unfold inSlot;omega)
        (by unfold inSlot;omega) (by unfold inSlot;omega))
  · intro p impossible;omega

theorem completedCap (o : Oracle) (input : CheckInput) (s : MachineState)
    (inv : PairInvariant o.compression input 128 s) : CompleteCap o.compression input s := by
  exact ⟨by simpa using inv.pc,inv.root,inv.rootDigest,fun p hp => inv.outs ⟨p,hp⟩ hp⟩

end CommitGolfCandidate.Trunc.Batch
