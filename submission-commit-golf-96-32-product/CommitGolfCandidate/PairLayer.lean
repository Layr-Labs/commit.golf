import CommitGolfCandidate.PairFinish
import CommitGolfCandidate.PairRowHash
import CommitGolfCandidate.PairRegion
import CommitGolfCandidate.PairProgress
import CommitGolfCandidate.CKB2Steps
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 250000
attribute [local irreducible] readBuffer storedAt

def sourceRow (p : Nat) := 16384+96*p
def outSlot (p : Nat) := 4608+32*p
/-- (A96) pair slot `p`: 30 bytes at proof offset 65280+30p. -/
def inSlot (p : Nat) := 12079664928+30*p
def leftId (p : Fin 128) : Fin 256 := ⟨2*p.val,by have :=p.isLt;omega⟩
def rightId (p : Fin 128) : Fin 256 := ⟨2*p.val+1,by have :=p.isLt;omega⟩
theorem leftCell (p : Fin 128) : cell (leftId p).val=sourceRow p.val := by
  unfold cell sourceRow;rw [show (leftId p).val=2*p.val by rfl,heap_offset_even]
theorem rightCell (p : Fin 128) : cell (rightId p).val=sourceRow p.val+32 := by
  unfold cell sourceRow;rw [show (rightId p).val=2*p.val+1 by rfl,heap_offset_odd];omega

structure PairInvariant (H : Compression) (input : CheckInput) (k : Nat) (s : MachineState) : Prop where
  bound : k≤128
  pc : s.pc=if k=128 then 7348 else 6892
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
  ins : ∀ p : Fin 128,k≤p.val → widen (readBuffer s (inSlot p.val) 30)=supplied input p.val
  outs : ∀ p : Fin 128,p.val<k → digestAt s (outSlot p.val)=capTable H input p.val

private theorem initPairsInfo (s : MachineState) (pc : s.pc=5276) :
    let t:=initPairsState s
    t.pc=5316 ∧ t.getReg .x22=12288 ∧ t.getReg .x23=16384 ∧ t.getReg .x24=4608 ∧ t.getReg .x27=128 ∧
    t.getReg .x26=s.getReg .x26 ∧ t.getReg .x19=s.getReg .x19 ∧ t.mem=s.mem := by
  simp [initPairsState,initPairsOps,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,signExtend12,pc]

private theorem storedMem {s t : MachineState} (m : s.mem=t.mem) (u : Fin 256) : storedAt s u=storedAt t u := by
  have b:= byteMem m (flag u.val)
  unfold byteAt at b
  unfold storedAt;rw [b,read_buffer_memory_congr _ _ m]

attribute [local irreducible] initPairsState
/-- (A96) `initPairs` (words 295..304) and the jump at 305 into the pairs loop at 699. -/
theorem pairStart (o : Oracle) (input : CheckInput) (s : MachineState)
    (inv : RecordInvariant o.compression input 128 s) :
    Runs o s ((initPairsState s).setPC 6892) 11 0 ∧
      PairInvariant o.compression input 0 ((initPairsState s).setPC 6892) := by
  have pc : s.pc=5276 := by simpa using inv.pc
  have run := pureBlockRuns (o:=o) (fun fuel => initPairsRun s pc fuel false)
  obtain ⟨p0,f,c,d,n,rt,sl,mem⟩ := initPairsInfo s pc
  have jump := ckb2j305 o (initPairsState s) p0
  have mem' : ((initPairsState s).setPC 6892).mem=s.mem := mem
  have rootEq := (readHigh s _ inv.inputWords 4294971392 (by decide) (by decide) (by decide)).trans (Late.Check.loaded_root input)
  refine ⟨runs_trans run jump,⟨by decide,rfl,sl.trans inv.slots,f,c,d,rt.trans inv.root,n,?_,?_,?_,?_,?_,?_⟩⟩
  · exact (read_buffer_memory_congr _ _ mem' _ _).trans rootEq
  · intro p _;exact (storedMem mem' _).trans (inv.table (leftId p))
  · intro p _;exact (storedMem mem' _).trans (inv.table (rightId p))
  · intro p _;exact (read_buffer_memory_congr _ _ mem' _ _).trans (inv.gap p)
  · intro p _
    have bp:=p.isLt
    rw [read_buffer_memory_congr _ _ mem',
      readHighA s _ inv.inputWords (inSlot p.val) 30 (by unfold inSlot;omega) (by unfold inSlot MEMORY_BYTES;omega)]
    exact supplyRead input p.val
  · intro p impossible;omega

/-- (A96) After the last pair the loop exits through `jal x0 ->349` (word 813). -/
theorem completedCap (o : Oracle) (input : CheckInput) (s : MachineState)
    (inv : PairInvariant o.compression input 128 s) :
    Runs o s (s.setPC 5492) 1 0 ∧ CompleteCap o.compression input (s.setPC 5492) := by
  have pc : s.pc=7348 := by simpa using inv.pc
  have m (a : Nat) : readBuffer (s.setPC 5492) a 32 = digestAt s a := read_buffer_memory_congr (s.setPC 5492) s rfl a 32
  exact ⟨ckb2j813 o s pc,rfl,inv.root,(m _).trans inv.rootDigest,fun p hp => (m _).trans (inv.outs ⟨p,hp⟩ hp)⟩

end CommitGolfCandidate.PairCap.Batch
