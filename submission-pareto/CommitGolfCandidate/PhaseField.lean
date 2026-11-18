import CommitGolfCandidate.PhaseCopy

namespace TwoPermutationPrototype.PhaseOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open ProjectedHalfword
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000
attribute [local irreducible] execute

def moveList (ws : List Nat) (s : MachineState) (src dst : Nat) : MachineState :=
  match ws with
  | [] => s
  | w::rest => moveList rest (moveState s w src dst) (src+w) (dst+w)

theorem PairRun.next {im : Image} {a b c : MachineState} {n m : Nat}
    (first : PairRun im a b n) (second : PairRun im b c m) : PairRun im a c (n+m) := by
  intro fuel coins
  rw [Nat.add_assoc,first,second]
  simp only [bind_assoc,pure_bind]
  apply bind_congr
  intro z
  cases z
  simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem split_halves (m n : Nat) (s : MachineState) (src dst : Nat) :
    copyLoopMemory false (m+n) s (addr src) (addr dst) =
      copyLoopMemory false n (copyLoopMemory false m s (addr src) (addr dst))
        (addr (src+2*m)) (addr (dst+2*m)) := by
  have step (x : Nat) : advance false (addr x)=addr (x+2) := by unfold addr;rw [BitVec.ofNat_add];rfl
  induction m generalizing s src dst with
  | zero => simp [copyLoopMemory]
  | succ m ih =>
    rw [Nat.succ_add,copyLoopMemory,copyLoopMemory,step,step,ih]
    simp only [Nat.mul_succ]; congr 2 <;> omega

def ValidMoves : List Nat → Nat → Nat → Prop
  | [], _, _ => True
  | w::ws,src,dst => (w=2 ∨ w=4 ∨ w=8) ∧ src%w=0 ∧ dst%w=0 ∧
                    ValidMoves ws (src+w) (dst+w)

theorem moveList_memory (ws : List Nat) (s : MachineState) (src dst : Nat)
    (valid : ValidMoves ws src dst) (apart : src+ws.sum≤dst) (fits : dst+ws.sum≤2^64) :
    (moveList ws s src dst).mem =
      (copyLoopMemory false (ws.sum/2) s (addr src) (addr dst)).mem := by
  have even (ls : List Nat) (a b : Nat) (v : ValidMoves ls a b) : ls.sum%2=0 := by
    induction ls generalizing a b with
    | nil => rfl
    | cons w ls ih =>
      have rest := ih _ _ v.2.2.2
      rcases v.1 with rfl|rfl|rfl <;> simp only [List.sum_cons] <;> omega
  induction ws generalizing s src dst with
  | nil => rfl
  | cons w ws ih =>
    have head := valid.1
    have rest := valid.2.2.2
    have half : 2*(w/2)=w := by rcases head with rfl|rfl|rfl <;> decide
    have cost : (w+ws.sum)/2=w/2+ws.sum/2 := by have :=even _ _ _ rest;omega
    simp only [List.sum_cons] at apart fits ⊢
    rw [moveList,ih _ _ _ rest (by omega) (by omega),cost,split_halves,half]
    apply copyLoopMemory_congr
    exact move_memory s w src dst head valid.2.1 valid.2.2.1 (by omega) (by omega)

theorem moveList_register (ws : List Nat) (s : MachineState) (src dst : Nat) (r : Reg) (safe : r≠.x31) :
    (moveList ws s src dst).getReg r=s.getReg r := by
  induction ws generalizing s src dst with
  | nil => rfl
  | cons w ws ih => exact (ih _ _ _).trans (move_register _ _ _ _ _ safe)

theorem moveList_pc (ws : List Nat) (s : MachineState) (src dst : Nat) :
    (moveList ws s src dst).pc = s.pc+addr (8*ws.length) := by
  induction ws generalizing s src dst with
  | nil => simp [moveList,addr]
  | cons w ws ih =>
    rw [moveList,ih,move_pc,List.length_cons,Nat.mul_succ]
    unfold addr
    rw [BitVec.ofNat_add]
    change s.pc+BitVec.ofNat 64 8+BitVec.ofNat 64 (8*ws.length)=s.pc+(BitVec.ofNat 64 (8*ws.length)+BitVec.ofNat 64 8)
    ac_rfl

theorem moveList_run (im : Image) (f : Fin 18) (s : MachineState) (ws : List Nat)
    (src dst sourceOffset destOffset : Nat) (vs : ValidMoves ws src dst)
    (bound : src+ws.sum≤MEMORY_BYTES ∧ dst+ws.sum≤MEMORY_BYTES)
    (off : sourceOffset+ws.sum≤128 ∧ destOffset+ws.sum≤128)
    (srcAddr : s.getReg (srcReg f)+addr sourceOffset=addr src)
    (dstAddr : s.getReg .x21+addr destOffset=addr dst)
    (code : ∀ j (inside : j<ws.length) (u : MachineState),
      let skip := (ws.take j).sum
      (u.pc=s.pc+addr (8*j) → fetch im u=some (.base (loadWidth ws[j] f (sourceOffset+skip)))) ∧
      (u.pc=s.pc+addr (8*j+4) → fetch im u=some (.base (saveWidth ws[j] (destOffset+skip))))) :
    PairRun im s (moveList ws s src dst) (2*ws.length) := by
  induction ws generalizing s src dst sourceOffset destOffset with
  | nil =>
    intro fuel coins
    simp [moveList,Execution.charge]
  | cons w ws ih =>
    simp only [List.sum_cons] at bound off
    have ww : 0<w := by rcases vs.1 with rfl|rfl|rfl <;> decide
    have slot := code 0 (by simp)
    have head := move_run im s f w sourceOffset destOffset src dst vs.1 srcAddr dstAddr
      (by omega) (by omega) (by omega) (by omega) vs.2.1 vs.2.2.1
      (by simpa [addr] using (slot s).1 (by simp [addr]))
      (fun t pc => by simpa [addr] using (slot t).2 (by simpa [addr] using pc))
    have add_addr (a b : Nat) : addr (a+b)=addr a+addr b := BitVec.ofNat_add ..
    have nextSource : (moveState s w src dst).getReg (srcReg f)+addr (sourceOffset+w)=addr (src+w) := by
      have safe : srcReg f≠.x31 := by unfold srcReg;split <;> decide
      rw [move_register _ _ _ _ _ safe,add_addr,←BitVec.add_assoc,srcAddr,add_addr]
    have nextDest : (moveState s w src dst).getReg .x21+addr (destOffset+w)=addr (dst+w) := by
      rw [move_register _ _ _ _ _ (by decide),add_addr,←BitVec.add_assoc,dstAddr,add_addr]
    have tail := ih (moveState s w src dst) (src+w) (dst+w) (sourceOffset+w) (destOffset+w)
      vs.2.2.2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ nextSource nextDest
    have pcNext : ∀ j, (moveState s w src dst).pc+addr (8*j) = s.pc+addr (8*(j+1)) := by
      intro j
      rw [move_pc,Nat.mul_succ,add_addr]
      change s.pc+addr 8+addr (8*j)=s.pc+(addr (8*j)+addr 8)
      ac_rfl
    apply (show 2*List.length (w::ws)=2+2*ws.length by simp [Nat.mul_succ];omega) ▸ head.next ?_
    apply tail
    intro j inside u
    have found := code (j+1) (by simpa using inside) u
    simp only [List.take_succ_cons,List.sum_cons,List.getElem_cons_succ] at found
    constructor
    · intro atPC
      simpa only [Nat.add_assoc] using found.1 (atPC.trans (pcNext j))
    · intro atPC
      have step4 : (moveState s w src dst).pc+addr (8*j+4)=s.pc+addr (8*(j+1)+4) := by
        rw [add_addr,←BitVec.add_assoc,pcNext,add_addr,BitVec.add_assoc]
      simpa only [Nat.add_assoc] using found.2 (atPC.trans step4)

#print axioms moveList_run
#print axioms moveList_memory
end TwoPermutationPrototype.PhaseOpening
