import CommitGolfCandidate.QuadLeafToNode
import CommitGolfCandidate.QuadNodeSemantic
import CommitGolfCandidate.QuadRecordLeafMeaning

namespace TwoPermutationPrototype.Quad.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling TwoPermutationPrototype.Quad.Checker
open TwoPermutationPrototype.Checker (honestIndex)
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
attribute [local irreducible] quadWorkspace quadPrefix quadRotation writeBits quadReturn rawLeaf leafToQuad

def nodeEntry (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) : MachineState :=
  leafToQuad (rawLeaf oracle ordinal index s).1

structure NodeEntryFacts (ordinal : Nat) (index : Index) (s : MachineState) : Prop where
  ready : QuadNodeReady s ⟨index.val%4,Nat.mod_lt _ (by decide)⟩ (checkProofByte ordinal+16)
  pc : s.pc=4336
  node : s.getReg .x6=BitVec.ofNat 64 (LENGTH+index.val)
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1

theorem node_entry_facts (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal< input.positions.card) (s : MachineState) (fits : ProofWithin input)
    (cursor : RecordCursor input ordinal s) (framed : RecordInputFrame input ordinal s) :
    NodeEntryFacts ordinal (honestIndex input.positions ordinal present).val
      (nodeEntry oracle ordinal (honestIndex input.positions ordinal present).val s) := by
  let index := (honestIndex input.positions ordinal present).val
  let raw := (rawLeaf oracle ordinal index s).1
  let mid := leafToQuad raw
  obtain ⟨pc,position,kept,frame⟩ := raw_view oracle input ordinal present s fits cursor framed
  have rawPC : raw.pc=4328 := pc
  have post := leaf_to_quad_post raw rawPC
  have keep (r : Reg) (a : r≠.x6) (b : r≠.x28) (c : r≠.x10) (d : r≠.x11)
      (e : r≠.x13) (f : r≠.x12) (g : r≠.x31) : raw.getReg r=s.getReg r := kept r a b c d e f g
  have keepMid (r : Reg) (a : r≠.x6) (b : r≠.x21) (c : r≠.x28) (d : r≠.x10)
      (e : r≠.x11) (f : r≠.x13) (g : r≠.x12) (h : r≠.x31) : mid.getReg r=s.getReg r :=
    (leaf_to_quad_saved raw r b a).trans (keep r a c d e f g h)
  have src : mid.getReg .x21=BitVec.ofNat 64 (checkProofByte ordinal+16) := by
    change (leafToQuad raw).getReg .x21=_
    rw [post.2.1,keep .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),cursor.proof]
    exact (BitVec.ofNat_add _ _).symm
  have node : mid.getReg .x6=BitVec.ofNat 64 (LENGTH+index.val) := by
    change (leafToQuad raw).getReg .x6=_
    rw [post.2.2.1,show raw.getReg .x6=BitVec.ofNat 64 index.val from position,
      keep .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),cursor.challengeLength,
      ←BitVec.ofNat_add,Nat.add_comm index.val]
  have pair : mid.getReg .x24=12544 := (keepMid .x24 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans cursor.pair
  have digest : mid.getReg .x23=12288 := (keepMid .x23 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans cursor.digest
  have selector : mid.getReg .x5=0 := (keepMid .x5 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans cursor.selector
  have readyLeaf := leaf_ready input ordinal present s fits cursor framed
  have rawSize : raw.getReg .x11=200 ∧ raw.getReg .x13=1 := by
    dsimp only [raw]
    unfold rawLeaf
    rw [checker_leaf_rows]
    exact ⟨(checker_leaf_preserved_register _ _ _ _ .x11 (by decide) (by decide) (by decide)).trans readyLeaf.size,
      (checker_leaf_preserved_register _ _ _ _ .x13 (by decide) (by decide) (by decide)).trans readyLeaf.primitive⟩
  have bounds := quad_record_geometry input ordinal present fits
  refine ⟨⟨pair,digest,?_,src,?_,?_,?_⟩,post.1,node,selector,?_,?_⟩
  · change mid.getReg .x6 &&& 3#64=BitVec.ofNat 64 (index.val%4)
    rw [node,quad_opened_slot]
  · have room := bounds.2.2.2.1
    omega
  · have align := bounds.1
    omega
  · have above := bounds.2.2.1
    omega
  · exact (leaf_to_quad_saved raw .x11 (by decide) (by decide)).trans rawSize.1
  · exact (leaf_to_quad_saved raw .x13 (by decide) (by decide)).trans rawSize.2

end TwoPermutationPrototype.Quad.RecordLeaf
