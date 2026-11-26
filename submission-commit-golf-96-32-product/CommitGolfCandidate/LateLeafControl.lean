import CommitGolfCandidate.LateLatchRegs

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def slotIndex (k : Nat) : Fin 32 := ⟨k%32, Nat.mod_lt _ (by decide)⟩
def leafBranch (s : MachineState) := execInstrBr s (.BNE .x20 .x0 6624)

structure AtLeaf (s : MachineState) (k : Nat) : Prop where
  pc : s.pc = pcAt (if k < LENGTH then leafPC (slotIndex k) 0 else 932)
  message : s.getReg .x8 = BitVec.ofNat 64 (msgAddr (8*(k/8)))
  rows : s.getReg .x18 = BitVec.ofNat 64 (rowAddr (16*(k/16)))
  nodes : s.getReg .x23 = BitVec.ofNat 64 (nodeAddress 0 (32*(k/32)))
  counter : s.getReg .x20 = BitVec.ofNat 64 (524288-k/32)
  stride : s.getReg .x29 = 2048
  base : s.getReg .x9 = 4294971424
  root : s.getReg .x26 = 4294971392
  selector : s.getReg .x5 = 0
  len : s.getReg .x11 = 96
  kind : s.getReg .x13 = 0

theorem toRegs {s : MachineState} {k : Nat} (a : AtLeaf s k) : LeafRegs s (k/32) (slotIndex k) := by
  refine ⟨?_,?_,a.nodes,a.selector,a.len,a.kind⟩
  · rw [a.message]; congr 2; change _ = 32*(k/32)+8*(k%32/8); omega
  · rw [a.rows]; congr 2; change _ = 32*(k/32)+16*(k%32/16); omega

def afterLeaf (h : Compression) (s : MachineState) (k : Nat) :=
  let i := slotIndex k
  let t := updatesState (finalLeafState h s (k/32) i) i
  if i.val = 31 then leafBranch t else t

def tailCount (k : Nat) := (updates (slotIndex k)).length + (if k%32=31 then 1 else 0)

private theorem end_word (i : Fin 32) :
    i.val = 31 → latchStart i + (updates i).length = 931 := by intro eq; have same : i = (31 : Fin 32) := Fin.ext eq; subst i; decide

private theorem fixed_updates (o : Oracle) (s : MachineState) (i : Fin 32) (fuel : Nat)
    (pc : s.pc = pcAt (latchStart i)) :
    o.run (execute commitImage (fuel+(updates i).length) s true) =
      (do let (out,n) ← o.run (execute commitImage fuel (updatesState s i) true)
          return (out.charge (updates i).length 0,n)) := by
  rw [execute_updates s i fuel pc,oracle_run_bind]
  simp only [oracle_run_pure, pure_bind, Nat.add_zero]

theorem fixed_iteration (o : Oracle) (s : MachineState) (k : Nat) (inside : k < LENGTH)
    (a : AtLeaf s k) (fuel : Nat) :
    o.run (execute commitImage (fuel+(12+tailCount k)) s true) =
      (do let (out,n) ← o.run (execute commitImage fuel (afterLeaf o.compression s k) true)
          return (out.charge (40+tailCount k) 4,4+n)) := by
  let i := slotIndex k
  let f := finalLeafState o.compression s (k/32) i
  let t := updatesState f i
  have pc : s.pc = pcAt (leafPC i 0) := by simpa only [if_pos inside] using a.pc
  have hi : 32*(k/32)+i.val < LENGTH := by change 32*(k/32)+k%32 < LENGTH; omega
  have post : f.pc = pcAt (latchStart i) := exit_pc _ _ _ _ pc
  by_cases e : i.val=31
  · have word := end_word i e
    have tpc : t.pc = pcAt 931 := by
      rw [(update_regs f i).pc,post]; unfold pcAt; rw [←BitVec.ofNat_add]
      apply congrArg (BitVec.ofNat 64); omega
    have dyn : tailCount k = (updates i).length + 1 := by
      unfold tailCount; rw [if_pos (show k%32=31 from e)]
    rw [show fuel+(12+tailCount k) = ((fuel+1)+(updates i).length)+12 by omega,
      fixed_leaf o s _ i (toRegs a) pc hi, fixed_updates o f i (fuel+1) post,
      last_branch t fuel tpc, oracle_run_bind]
    simp only [bind_assoc,oracle_run_pure,pure_bind, Nat.add_zero]
    simp only [afterLeaf, e, ← Nat.add_assoc, Execution.charge, dyn, if_true, Nat.zero_add]
    rw [if_pos (show (slotIndex k).val=31 from e)]
    rfl
  · have dyn : tailCount k = (updates i).length := by
      unfold tailCount; rw [if_neg (show ¬k%32=31 from e), Nat.add_zero]
    rw [show fuel+(12+tailCount k) = (fuel+(updates i).length)+12 by omega,
      fixed_leaf o s _ i (toRegs a) pc hi, fixed_updates o f i fuel post]
    simp only [afterLeaf,e,if_false, Execution.charge, dyn, bind_assoc,pure_bind,
      Nat.zero_add, Nat.add_zero, Nat.add_assoc]
    rw [if_neg (show (slotIndex k).val≠31 from e)]

end CommitGolfCandidate.Late
