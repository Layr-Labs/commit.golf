import CommitGolfCandidate.TwoPermutationPackedOperands
import CommitGolfCandidate.TwoPermutationPackedLowerControl

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def mergeEnd (leaf even : Bool) : Nat :=
  if even then (siblingSite leaf even).start+31 else childSite leaf even+8

/-- Odd nodes copy the sibling first; the leaf level clears byte 31 of its digest before the child copy. -/
def merge (s : MachineState) (leaf even : Bool) : MachineState :=
  if even then siblingState (childCopied (truncState s leaf) (childSite leaf even)) leaf even
  else childCopied (truncState (siblingState s leaf even) leaf) (childSite leaf even)

theorem OperandFacts.read_outside {s t : MachineState} {steps next dest : Nat} {v : BitVec 256}
    (op : OperandFacts s t steps next dest v) (base count : Nat) (bound : base+count≤2^64)
    (away : base+count≤8*dest ∨ 8*(dest+4)≤base) : readBuffer t base count=readBuffer s base count := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat _)
  apply Finset.sum_congr rfl
  intro i hi
  have hb := Finset.mem_range.mp hi
  rw [byte_eq_of_word_frame s t (base+i) (op.frame _ (by omega) (by omega))]

theorem OperandFacts.wire_outside {s t : MachineState} {steps next dest : Nat} {v : BitVec 256}
    (op : OperandFacts s t steps next dest v) (proof : Nat) (leaf : Bool) (bound : proof+30≤2^64)
    (away : proof+30≤8*dest ∨ 8*(dest+4)≤proof) : wire t proof leaf=wire s proof leaf := by
  unfold wire
  rw [op.read_outside proof 30 bound away]

structure MergeFacts (s t : MachineState) (leaf even : Bool) (proof : Nat) : Prop where
  run : GroupHop s t (8+siblingCost leaf+truncCost leaf)
  pc : t.pc=BitVec.ofNat 64 (4096+4*mergeEnd leaf even)
  register : ∀ r, r≠.x31 → t.getReg r=s.getReg r
  child : readBuffer t (8*slotWord (!even)) 32=own s leaf
  sibling : readBuffer t (8*slotWord even) 32=wire s proof leaf
  frame : ∀ w<2^61, (w<1536 ∨ 1540≤w) → (w<1568 ∨ 1576≤w) → memoryView t w=memoryView s w

attribute [local irreducible] readBuffer childCopied siblingState execute truncState

theorem merge_facts (s : MachineState) (leaf even : Bool) (proof : Nat)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*dispatchStart leaf even))
    (src : s.getReg .x21=BitVec.ofNat 64 proof) (child : s.getReg .x23=12288)
    (dst : s.getReg .x24=12544) (above : 32768≤proof) (aligned : proof%2=0)
    (room : proof+30≤MEMORY_BYTES) :
    MergeFacts s (merge s leaf even) leaf even proof := by
  have lim : MEMORY_BYTES<2^64 := by decide
  cases even with
  | true =>
    have z := trunc_operand s leaf (dispatchStart leaf true) (by cases leaf <;> exact pc)
      (by intro h; subst h; rfl) (by cases leaf <;> decide) child
    let u := truncState s leaf
    have c := child_operand u leaf true (by rw [z.pc]; cases leaf <;> rfl)
      ((z.register _ (by decide)).trans child) ((z.register _ (by decide)).trans dst)
    let t := childCopied u (childSite leaf true)
    have q := sibling_operand t leaf true proof (by cases leaf <;> exact c.pc)
      ((c.register _ (by decide)).trans ((z.register _ (by decide)).trans src))
      ((c.register _ (by decide)).trans ((z.register _ (by decide)).trans dst)) above aligned room
    refine ⟨?_,?_,fun r h => (q.register r h).trans ((c.register r h).trans (z.register r h)),
      ?_,?_,?_⟩
    · have hop := GroupHop.thenDo (GroupHop.thenDo z.execute c.execute) q.execute
      rwa [show truncCost leaf+8+siblingCost leaf=8+siblingCost leaf+truncCost leaf by omega] at hop
    · exact q.pc
    · exact (q.read_outside 12544 32 (by decide) (Or.inl (by decide))).trans (c.digest.trans z.digest)
    · refine q.digest.trans ?_
      refine (c.wire_outside proof leaf (by omega) (Or.inr (by change 12576≤proof;omega))).trans ?_
      exact z.wire_outside proof leaf (by omega) (Or.inr (by change 12320≤proof;omega))
    · intro w hw h h'
      exact (q.frame w hw (by change w<1572 ∨ 1572+4≤w; omega)).trans
        ((c.frame w hw (by change w<1568 ∨ 1568+4≤w; omega)).trans (z.frame w hw (by omega)))
  | false =>
    have q := sibling_operand s leaf false proof (by cases leaf <;> exact pc) src dst above aligned room
    let t := siblingState s leaf false
    have z := trunc_operand t leaf ((siblingSite leaf false).start+siblingCost leaf) q.pc
      (by intro h; subst h; rfl) (by cases leaf <;> decide) ((q.register _ (by decide)).trans child)
    let u := truncState t leaf
    have c := child_operand u leaf false (by rw [z.pc]; cases leaf <;> rfl)
      ((z.register _ (by decide)).trans ((q.register _ (by decide)).trans child))
      ((z.register _ (by decide)).trans ((q.register _ (by decide)).trans dst))
    refine ⟨?_,c.pc,fun r h => (c.register r h).trans ((z.register r h).trans (q.register r h)),?_,?_,?_⟩
    · have hop := GroupHop.thenDo (GroupHop.thenDo q.execute z.execute) c.execute
      rwa [show siblingCost leaf+truncCost leaf+8=8+siblingCost leaf+truncCost leaf by omega] at hop
    · refine c.digest.trans (z.digest.trans ?_)
      unfold own
      rw [q.read_outside 12288 32 (by decide) (Or.inl (by decide))]
    · exact (c.read_outside 12544 32 (by decide) (Or.inl (by decide))).trans
        ((z.read_outside 12544 32 (by decide) (Or.inr (by decide))).trans q.digest)
    · intro w hw h h'
      exact (c.frame w hw (by change w<1572 ∨ 1572+4≤w; omega)).trans
        ((z.frame w hw (by omega)).trans (q.frame w hw (by change w<1568 ∨ 1568+4≤w; omega)))

def routeCost (leaf even : Bool) : Nat := if leaf&&even then 0 else 1
def route (s : MachineState) (leaf even : Bool) := if leaf&&even then s else s.setPC 5024

theorem route_pc (s : MachineState) (leaf even : Bool) (pc : s.pc=BitVec.ofNat 64 (4096+4*mergeEnd leaf even)) :
    (route s leaf even).pc=5024 := by cases leaf <;> cases even <;> first | rfl | exact pc

theorem route_run (s : MachineState) (leaf even : Bool) (pc : s.pc=BitVec.ofNat 64 (4096+4*mergeEnd leaf even)) :
    GroupHop s (route s leaf even) (routeCost leaf even) := by
  have jump (ord imm : Nat) (here : s.pc=BitVec.ofNat 64 (4096+4*ord)) (ordBound : ord<367)
      (fetched : (packedImage.code[ord]?).bind decodeInstruction=some (.base (.JAL .x0 (BitVec.ofNat 21 imm))))
      (landing : s.pc+signExtend21 (BitVec.ofNat 21 imm)=5024) :
      GroupHop s (s.setPC 5024) 1 := by
    intro fuel
    have ran : ordinaryStep s (.base (.JAL .x0 (BitVec.ofNat 21 imm)))=some (s.setPC 5024) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,MachineState.setReg,landing]
    rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ (fetch_at s ord _ ordBound here fetched) ran]
    rfl
  cases leaf <;> cases even
  · exact jump 107 500 pc (by decide) rfl (by rw [pc];rfl)
  · exact jump 147 340 pc (by decide) rfl (by rw [pc];rfl)
  · exact jump 191 164 pc (by decide) rfl (by rw [pc];rfl)
  · intro fuel
    simp [routeCost,route,Execution.charge]

end TwoPermutationPrototype.Packed.Checker
