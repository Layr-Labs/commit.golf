import CommitGolfCandidate.PairBatchSteps
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 300000

def flag (u : Nat) := 12288+u
def cell (u : Nat) := 16384+heapOffset u

private theorem cellNat : ∀ u : Fin 256,
    16384 + (((BitVec.ofNat 64 u.val >>> 1) + BitVec.ofNat 64 u.val) <<< 5) = BitVec.ofNat 64 (cell u.val) := by decide

private theorem flagOK : ∀ u : Fin 256, accessValid (BitVec.ofNat 64 (flag u.val)) 1 := by decide
private theorem cellOK : ∀ u : Fin 256, ∀ j : Fin 4,
    accessValid (BitVec.ofNat 64 (cell u.val) + BitVec.ofNat 64 (8*j.val)) 8 := by decide

theorem bucketAccess (s : MachineState) (u : Fin 256) (idx : s.getReg .x20=BitVec.ofNat 64 u.val) :
    safeSteps bucketOps s := by
  intro ⟨j,b⟩
  change j < 12 at b
  interval_cases j
  · rfl
  · rfl
  · rfl
  · rfl
  · have ptr : (stepPrefix bucketOps s 4).getReg .x22 = BitVec.ofNat 64 (flag u.val) := by
      simp [stepPrefix,bucketOps,execInstrBr,MachineState.getReg,MachineState.setReg,
        MachineState.setPC,signExtend12,flag,BitVec.ofNat_add] at idx ⊢
      rw [idx]
    change accessValid ((stepPrefix bucketOps s 4).getReg .x22 + 0#64) 1 = true
    rw [ptr,BitVec.add_zero]; exact flagOK u
  all_goals rfl

theorem bucketInfo (s : MachineState) (pc : s.pc=5120) (u : Fin 256) (idx : s.getReg .x20=BitVec.ofNat 64 u.val) :
    let b := bucketState s
    b.pc=5168 ∧ b.getReg .x22=BitVec.ofNat 64 (flag u.val) ∧ b.getReg .x23=BitVec.ofNat 64 (cell u.val) ∧
    b.getReg .x7=(s.getByte (BitVec.ofNat 64 (flag u.val))).zeroExtend 64 ∧ b.mem=s.mem := by
  have mark : (12288#64 + s.getReg .x20) = BitVec.ofNat 64 (flag u.val) := by
    rw [idx];exact (BitVec.ofNat_add 12288 u.val).symm
  simp only [bucketState,bucketOps,List.foldl,execInstrBr,signExtend12,MachineState.setPC,
    MachineState.setReg,MachineState.getReg,MachineState.getByte,MachineState.getMem] at *
  simp_all [flag,Nat.add_comm,BitVec.ofNat_add]
  exact (show ∀ w : Fin 256, 16384#64 + ((BitVec.ofNat 64 w.val <<< 5) +
    ((BitVec.ofNat 64 w.val >>> 1) <<< 5)) = BitVec.ofNat 64 (cell w.val) by decide) u

def copyAt (s : MachineState) (src dst : Word) :=
  openingCopyState ((s.setReg .x23 src).setReg .x25 dst)

private theorem copyAtGet (s : MachineState) (src dst : Word) (a : Word)
    (away : ∀ j : Fin 4, a ≠ dst + BitVec.ofNat 64 (8*j.val)) :
    (copyAt s src dst).getMem a = s.getMem a :=
  opening_copy_memory_outside _ _ away

theorem copyAtDigest (s : MachineState) (src dst : Nat) (a1 : src%8=0) (a2 : dst%8=0)
    (lim1 : src+32≤2^64) (lim2 : dst+32≤2^64) (disj : src+32≤dst ∨ dst+32≤src) :
    readBuffer (copyAt s (BitVec.ofNat 64 src) (BitVec.ofNat 64 dst)) dst 32 = readBuffer s src 32 :=
  opening_copy_digest _ _ _ rfl rfl a1 a2 lim1 lim2 disj

theorem storeMemory (s : MachineState) :
    (storeState s).mem = (copyAt (s.setByte (s.getReg .x22) 1) (s.getReg .x21) (s.getReg .x23)).mem := by
  simp [storeState,storeOps,copyAt,opening_copy_expansion,execInstrBr,MachineState.setReg,
    MachineState.getReg,MachineState.setPC,MachineState.getMem,MachineState.setMem,MachineState.setByte,signExtend12]

attribute [local irreducible] readBuffer copyAt storeState
private theorem markAway : ∀ v : Fin 256, ∀ w : Fin 4, alignToDword (BitVec.ofNat 64 (flag v.val)) ≠ BitVec.ofNat 64 (256+8*w.val) := by decide

theorem storedNode (s : MachineState) (u : Fin 256) (sf : s.getReg .x22 = BitVec.ofNat 64 (flag u.val))
    (sn : s.getReg .x23 = BitVec.ofNat 64 (cell u.val)) (scratch : s.getReg .x21=256) :
    readBuffer (storeState s) (cell u.val) 32 = readBuffer s 256 32 := by
  rw [read_buffer_memory_congr _ _ (storeMemory s),sf,sn,scratch]
  have domain : ∀ i : Fin 256, cell i.val % 8 = 0 ∧ cell i.val+32 ≤ 2^64 ∧ 288 ≤ cell i.val := by decide
  obtain ⟨align,bound,above⟩ := domain u
  let marked := s.setByte (BitVec.ofNat 64 (flag u.val)) 1
  apply (copyAtDigest marked 256 (cell u.val) (by decide) align (by decide) bound (Or.inl above)).trans
  apply read_digest_congr _ _ _ (by decide)
  intro i hi
  change ((s.setByte _ _).getMem _) = _
  unfold MachineState.setByte
  exact MachineState.getMem_setMem_ne (Ne.symm (markAway u ⟨i,hi⟩))

end CommitGolfCandidate.PairCap.Batch
