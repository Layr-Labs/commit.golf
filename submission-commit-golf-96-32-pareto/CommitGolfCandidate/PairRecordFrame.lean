import CommitGolfCandidate.PairTailChoice
import CommitGolfCandidate.PairRowSemantic
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 35000
attribute [local irreducible] readBuffer rowHash storedAt prefixNode lowerHash

theorem mapCongr (s t : MachineState) (eqn : s.mem=t.mem) (u : Fin 256) :
    storedAt s u=storedAt t u := by
  have byte : s.getByte (BitVec.ofNat 64 (flag u.val))=t.getByte (BitVec.ofNat 64 (flag u.val)) := by
    simp only [MachineState.getByte,MachineState.getMem,eqn]
  simp only [storedAt,byte,read_buffer_memory_congr s t eqn]

private theorem chooseProperty {α : Type} (b : Bool) (l r : α) (P : α→Prop)
    (left : b=true → P l) (right : b=false → P r) : P (if b then l else r) := by
  cases b
  · exact right rfl
  · exact left rfl

theorem rowProperty (m : MachineState) (b : Bool) (P : MachineState→Prop)
    (write : b=true → P (copied m)) (compare : b=false → P (compared m)) : P (finishRow b m) :=
  chooseProperty b (copied m) (compared m) P write compare

theorem wordAfter {s t : MachineState} (m : t.mem=s.mem) (w : Word) : t.getMem w=s.getMem w := congrFun m w

theorem priorAgrees {α : Type} {v : Option α} {d current : α} (b : Bool)
    (prior : v=if b then none else some current) (hit : v=some d) : d=current := by
  cases b
  · exact Option.some.inj (hit.symm.trans prior)
  · have bad : none=some d := prior.symm.trans hit
    cases bad
theorem whenFresh {α : Type} {v : Option α} {current : α} {b : Bool}
    (prior : v=if b then none else some current) (yes : b=true) : v=none := by simpa only [yes,ite_true] using prior
theorem whenSeen {α : Type} {v : Option α} {current : α} {b : Bool}
    (prior : v=if b then none else some current) (no : b=false) : v=some current := by
  simpa only [no,Bool.false_eq_true,ite_false] using prior

theorem recordFrom (H : Compression) (input : CheckInput) (n : Nat) (bound : n≤128) (s : MachineState)
    (reg : NextRegs n s) (tab : ∀ u,storedAt s u=prefixNode H input n u)
    (agree : ∀ r<n,∀ u : Fin 256, openingIndex input.positions r/65536=u.val → prefixNode H input n u=some (lowerHash H input r))
    (high : ∀ w : Word,32768≤w.toNat → s.getMem w=(submission.initialState .check input).getMem w)
    (gap : ∀ p : Fin 128,readBuffer s (16384+96*p.val+64) 32=0) : RecordInvariant H input n s :=
  ⟨bound,reg.ip,reg.vp,reg.pp,reg.remaining,reg.scratch,reg.depth,reg.slots,reg.root,reg.pc,tab,agree,high,gap⟩
end CommitGolfCandidate.PairCap.Batch
