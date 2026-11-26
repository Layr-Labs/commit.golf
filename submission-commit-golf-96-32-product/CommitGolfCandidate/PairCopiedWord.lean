import CommitGolfCandidate.PairRowMap
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 2500
set_option maxHeartbeats 50000

private theorem memGet (s t : MachineState) (e : s.mem=t.mem) (w : Word) : s.getMem w=t.getMem w :=
  congrFun e w
private theorem copyGet (s : MachineState) (src dst w : Word)
    (h : ∀ j : Fin 4,w≠dst+BitVec.ofNat 64 (8*j.val)) :
    (copyAt s src dst).getMem w = s.getMem w := by
  unfold copyAt
  exact opening_copy_memory_outside ((s.setReg .x23 src).setReg .x25 dst) w h
private theorem byteGet (s : MachineState) (dst w : Word) (h : w≠alignToDword dst) :
    (s.setByte dst 1).getMem w=s.getMem w := MachineState.getMem_setMem_ne h
private theorem copiedDef (s : MachineState) : copied s = nextEdge (storeState (tested s)) := rfl
attribute [local irreducible] MachineState.getMem storedAt nextEdge storeState copyAt tested copied

theorem copiedWord (s : MachineState) (pc : s.pc=5120) (u : Fin 256) (idx : s.getReg .x20=BitVec.ofNat 64 u.val)
    (w : Word) (flagAway : w ≠ alignToDword (BitVec.ofNat 64 (flag u.val)))
    (cellAway : ∀ j : Fin 4, w ≠ BitVec.ofNat 64 (cell u.val+8*j.val)) :
    (copied s).getMem w=s.getMem w := by
  let t := tested s
  have info := testInfo s pc u idx
  have hf : t.getReg .x22=BitVec.ofNat 64 (flag u.val) := info.1
  have hc : t.getReg .x23=BitVec.ofNat 64 (cell u.val) := info.2.1
  let m:=t.setByte (t.getReg .x22) 1
  have fneq : w ≠ alignToDword (t.getReg .x22) := hf ▸ flagAway
  have cneq (j : Fin 4) : w ≠ t.getReg .x23+BitVec.ofNat 64 (8*j.val) := by
    rw [hc,← BitVec.ofNat_add];exact cellAway j
  rw [copiedDef]
  exact (memGet _ _ (nextMem (storeState t)) w).trans
    ((memGet _ _ (storeMemory t) w).trans ((copyGet m (t.getReg .x21) (t.getReg .x23) w cneq).trans
      ((byteGet t (t.getReg .x22) w fneq).trans (memGet t s info.2.2.2 w))))
end CommitGolfCandidate.PairCap.Batch
