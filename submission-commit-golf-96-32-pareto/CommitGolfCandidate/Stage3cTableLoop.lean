import CommitGolfCandidate.Stage3cOpenTable
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def tableFold (s : MachineState) : Nat → MachineState
  | 0=>s
  | n+1=>putTable (tableFold s n) n

structure TableBuilt (batch : Bool) (s t : MachineState) (n : Nat) : Prop where
  run : Runs s t (tableIndex n) (tableIndex n)
  pc : t.pc=pcAt (tablePC batch n)
  regs : ∀ r,r≠.x6→t.getReg r=s.getReg r
  stored : ∀ j<n,wordAt t (tableSlot j)=W (tdBase+levelOffset j)
  frame : ∀ a : Word,(∀ j<n,a≠W (tableSlot j))→t.getMem a=s.getMem a

theorem table_loop (s : MachineState) (batch : Bool) (atPC : s.pc=pcAt (tablePC batch 0))
    (base : s.getReg .x8=W tdBase) (gp : s.getReg .x3=W 2048) (n : Nat) (bound : n≤25) :
    TableBuilt batch s (tableFold s n) n := by
  induction n with
  | zero=>exact ⟨Runs.refl _,atPC,fun _ _=>rfl,fun _ h=>by omega,fun _ _=>rfl⟩
  | succ n ih=>
    let l : Fin 25:=⟨n,by omega⟩
    let t:=tableFold s n
    obtain ⟨first,pc,regs,stored,frame⟩:=ih (by omega)
    obtain ⟨one,next,keeps,write⟩:=put_table t l batch pc ((regs _ (by decide)).trans base) ((regs _ (by decide)).trans gp)
    constructor
    · simpa only [tableIndex,tableFold,t,l,Nat.add_assoc] using first.trans one
    · exact next
    · exact fun r ne=>(keeps r ne).trans (regs r ne)
    · intro j hj
      change (putTable t n).getMem (W (tableSlot j))=_
      rw [write]
      by_cases last : j=n
      · subst j;simp [l]
      · have ne : W (tableSlot j)≠W (tableSlot n) := by
          intro e
          have a:=congrArg BitVec.toNat e
          simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show tableSlot j<2^64 by unfold tableSlot;omega),
            Nat.mod_eq_of_lt (show tableSlot n<2^64 by unfold tableSlot;omega)] at a
          unfold tableSlot at a;omega
        rw [if_neg (fun h=>ne (beq_iff_eq.mp h))]
        exact stored j (by omega)
    · intro a away
      rw [show (tableFold s (n+1)).getMem a=_ from write a,if_neg (fun h=>away n (by omega) (beq_iff_eq.mp h))]
      exact frame a (fun j hj=>away j (by omega))

theorem table_complete (s : MachineState) (batch : Bool) (pc : s.pc=pcAt (if batch then 44 else 378))
    (base : s.getReg .x8=W tdBase) (gp : s.getReg .x3=W 2048) :
    let t:=tableFold s 25
    Runs s t 82 82 ∧ t.pc=pcAt (if batch then 126 else 460) ∧ (∀ j<25,wordAt t (tableSlot j)=W (tdBase+levelOffset j)) ∧
    (∀ r,r≠.x6→t.getReg r=s.getReg r) ∧ Outside s t 2048 200 := by
  have start : tablePC batch 0=(if batch then 44 else 378) := by cases batch <;> rfl
  obtain ⟨run,last,regs,stored,frame⟩:=table_loop s batch (start ▸ pc) base gp 25 le_rfl
  rw [show tableIndex 25=82 by decide +kernel] at run
  have stop : tablePC batch 25=(if batch then 126 else 460) := by cases batch <;> decide +kernel
  refine ⟨run,last.trans (congrArg pcAt stop),stored,regs,?_⟩
  intro a bound al apart
  apply frame
  intro j hj eq
  have e:=congrArg BitVec.toNat eq
  have small : a<2^64 := by change a<2^36 at bound;omega
  simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt (show tableSlot j<2^64 by unfold tableSlot;omega)] at e
  unfold tableSlot at e;omega
end CommitGolfCandidate.Chained.BinaryMachine.Open
