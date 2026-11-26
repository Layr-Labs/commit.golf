import CommitGolfCandidate.S5LeafStep
import CommitGolfCandidate.S5Initial
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late (PairCoins)
set_option maxRecDepth 16000

structure Saved (s : MachineState) : Prop where
  msg : s.getReg .x8=4096
  root : s.getReg .x9=4294971392
  td : s.getReg .x18=4294975488
  rows : s.getReg .x19=5502935040
  scratch : s.getReg .x24=7113547776

private theorem header_saved (s : MachineState) (m : s.getReg .x10=4096) (r : s.getReg .x11=4294971392)
    (t : s.getReg .x12=4294975488) : Saved (initializeOps.foldl execInstrBr s) := by
  have m' : s.regs .x10=4096:=m;have r' : s.regs .x11=4294971392:=r;have t' : s.regs .x12=4294975488:=t
  constructor <;> simp [initializeOps,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,
    signExtend12,m',r',t'] <;> rfl

private theorem coin_keeps (p : Nat) (s : MachineState) (w : PairCoins) (r : Reg) (a : Reg.x10≠r) (b : Reg.x20≠r) :
    (nextPair p s w).getReg r=s.getReg r := by
  have same:=(random_registers s w).2.2 r a.symm
  unfold nextPair;split
  · simpa only [latchState,decrement,MachineState.getReg_setPC,execInstrBr,MachineState.getReg_setReg_ne _ _ _ _ b] using same
  · exact same

private theorem tape_keeps (ws : List PairCoins) (p : Nat) (s : MachineState) (r : Reg) (a : Reg.x10≠r) (b : Reg.x20≠r) :
    (applyPairs p s ws).getReg r=s.getReg r := by
  induction ws generalizing p s with
  | nil=>rfl
  | cons w ws ih=>exact (ih (p+1) (nextPair p s w)).trans (coin_keeps p s w r a b)

theorem sampled_saved (m : Message) (ws : List PairCoins) : Saved (sampled m ws) := by
  have saved:=header_saved (start m) rfl rfl rfl
  constructor
  · exact (tape_keeps ws 0 _ _ (by decide) (by decide)).trans saved.msg
  · exact (tape_keeps ws 0 _ _ (by decide) (by decide)).trans saved.root
  · exact (tape_keeps ws 0 _ _ (by decide) (by decide)).trans saved.td
  · exact (tape_keeps ws 0 _ _ (by decide) (by decide)).trans saved.rows
  · exact (tape_keeps ws 0 _ _ (by decide) (by decide)).trans saved.scratch

def leafOps : List Instr :=
  [.ADDI .x5 .x0 0,.ADDI .x11 .x0 96,.ADDI .x13 .x0 0,.LUI .x6 1,.ADDI .x6 .x6 2048,
   .ADD .x21 .x8 .x6,.ADD .x22 .x19 .x6,.ADD .x23 .x18 .x6,.LUI .x25 1,.LUI .x26 1,.ADDI .x26 .x26 4032,
   .ADDI .x27 .x0 384,.LUI .x20 16]
def prepareLeaves (s : MachineState) := leafOps.foldl execInstrBr s
private theorem leaf_header : ∀ i : Fin 13,
    decodeInstruction (atWord .commit ⟨4111+i.val,by change 4111+i.val<18492;omega⟩)=
    some (.base (leafOps.get ⟨i.val,i.isLt⟩)) := by decide +kernel

theorem leaf_entry_run (s : MachineState) (pc : s.pc=pcAt 4111) (fuel : Nat) :
    execute commitImage (fuel+13) s true=
      (do let r←execute commitImage fuel (prepareLeaves s) true;return r.charge 13 0) := by
  apply execute_linear .commit true leafOps 4111 s fuel pc
  · intro op member
    simp only [leafOps,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> intro s <;> exact ⟨rfl,rfl,rfl⟩
  · intro i hi
    change i<13 at hi
    apply site (by change 4111+i<18492;omega)
    exact leaf_header ⟨i,hi⟩

private theorem leaf_prepared (s : MachineState) (pc : s.pc=pcAt 4111) (v : Saved s) : AtLeaf (prepareLeaves s) 0 := by
  have m : s.regs .x8=4096:=v.msg;have r : s.regs .x9=4294971392:=v.root;have t : s.regs .x18=4294975488:=v.td
  have rows : s.regs .x19=5502935040:=v.rows;have scratch : s.regs .x24=7113547776:=v.scratch
  constructor <;> simp [prepareLeaves,leafOps,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,
    signExtend12,m,r,t,rows,scratch,pc,pcAt,tileSite,slotIndex,LENGTH,LOG_LENGTH,msgPos,rowPos,nodePos,rowBase] <;> rfl

theorem sampled_pc (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) : (sampled m ws).pc=pcAt 4111 := by
  have v:=apply_pairs_invariant ws 0 (prepared m) (ready m) (by rw [len];omega)
  rw [Nat.zero_add,len] at v
  exact v.pc.trans (by rw [if_neg (Nat.lt_irrefl _)])
theorem leaf_initial (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    AtLeaf (prepareLeaves (sampled m ws)) 0 := leaf_prepared _ (sampled_pc m ws len) (sampled_saved m ws)
end CommitGolfCandidate.S5Machine
