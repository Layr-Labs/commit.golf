import CommitGolfCandidate.TwoPermutationPackedCapAdvance
import CommitGolfCandidate.TwoPermutationCheckerCapHash
import CommitGolfCandidate.K3C4CapMask
import CommitGolfCandidate.CapCompressionStep

/-! # The cap parent call (T238)

`srli x6,x6,1; slli x10,x6,6; add x10,x25,x10; slli x12,x6,5; add x12,x25,x12; ecall` (334..339), then
`jal <700>` (340), the 238-bit mask `lhu x31,28(x12); slli x31,x31,50; srli x31,x31,50; sw x31,28(x12)`
(700..703), `jal <341>` (704) and `jal <330>` (341). The parent slot holds `pad238` of the reply. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

open TwoPermutationPrototype.Checker (capRootAt)
open CommitGolfCandidate (capCompressionAnswer)
open ShortTree

private theorem cap_node_shift (node : Nat) (bounded : node < 2^64) :
    BitVec.ofNat 64 node >>> 1 = BitVec.ofNat 64 (node/2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bounded, Nat.mod_eq_of_lt (by omega : node/2 < 2^64), Nat.shiftRight_eq_div_pow]

private theorem cap_address (node : Nat) :
    16384#64 + (BitVec.ofNat 64 node <<< 5) = wordAddress (2048+4*node) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 16384 + BitVec.ofNat 64 node * BitVec.ofNat 64 32 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, wordAddress]
  congr 1
  omega

structure CapHashReady (state : MachineState) (node : Nat) where
  pc : state.pc = 0x1538
  nodeReg : state.getReg .x6 = BitVec.ofNat 64 node
  roots : state.getReg .x25 = 16384#64
  selector : state.getReg .x5 = 0
  size : state.getReg .x11 = 64
  primitive : state.getReg .x13 = 0
  bound : node < 512

/-- The state after the parent call: reply written, top doubleword masked, back at word 330. -/
def capHashReply (state : MachineState) (_parent : Nat) (answer : BitVec 256) : MachineState :=
  (maskAfter ((capCompressionAnswer (capParent state) answer).setPC 0x1af0) .x12 28).setPC 0x1528

def capHashQuery (state : MachineState) (parent : Nat) : OracleComp World MachineState := do
  let answer ← World.query (.inr (.inl (capRootAt state (2*parent+1) ++ capRootAt state (2*parent))))
  return capHashReply state parent answer

theorem cap_answer_pc (s : MachineState) (answer : BitVec 256) :
    (capCompressionAnswer s answer).pc = s.pc + 4 := rfl

set_option maxRecDepth 4096
attribute [local irreducible] execute readBuffer writeBits maskAfter

private theorem parent_registers {state : MachineState} {node : Nat} (ready : CapHashReady state node) :
    (capParent state).pc = 0x154c ∧
    (capParent state).getReg .x10 = wordAddress (2048+8*(node/2)) ∧
    (capParent state).getReg .x12 = wordAddress (2048+4*(node/2)) := by
  obtain ⟨pc, parent, source, dest, mem⟩ := cap_parent_post state ready.pc
  have room := ready.bound
  have shifted : state.getReg .x6 >>> 1 = BitVec.ofNat 64 (node/2) := by
    rw [ready.nodeReg, cap_node_shift _ (by omega)]
  refine ⟨pc, ?_, ?_⟩
  · rw [source, ready.roots, shifted, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 16384 + BitVec.ofNat 64 (node/2) * BitVec.ofNat 64 64 = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, wordAddress]
    congr 1
    omega
  · rw [dest, ready.roots, shifted, cap_address]

private theorem answer_address {state : MachineState} {node : Nat} (ready : CapHashReady state node)
    (answer : BitVec 256) :
    ((capCompressionAnswer (capParent state) answer).setPC 0x1af0).getReg .x12 + signExtend12 28 =
      BitVec.ofNat 64 (8*(2048+4*(node/2))+24+4) := by
  rw [MachineState.getReg_setPC, cap_compression_register, (parent_registers ready).2.2, wordAddress,
    show signExtend12 28 = BitVec.ofNat 64 28 from rfl, ← BitVec.ofNat_add]

/-- The seven ordinary steps after the reply: two jumps, the mask, two jumps. -/
private theorem cap_hash_tail {state : MachineState} {node : Nat} (ready : CapHashReady state node)
    (answer : BitVec 256) :
    GroupHop (capCompressionAnswer (capParent state) answer) (capHashReply state (node/2) answer) 7 := by
  let s1 := capCompressionAnswer (capParent state) answer
  have p1 : s1.pc = BitVec.ofNat 64 (4096+4*340) := by
    rw [cap_answer_pc, (parent_registers ready).1]
    rfl
  have h1 := cap_jal_hop s1 340 700 1440 (by decide) p1 rfl rfl
  let s2 := s1.setPC (BitVec.ofNat 64 (4096+4*700))
  have bound := ready.bound
  have h2 := execute_mask s2 700 .x12 28 (8*(2048+4*(node/2))+24) (by decide) rfl rfl rfl rfl rfl
    (answer_address ready answer) (by omega) (by unfold MEMORY_BYTES; omega) (by decide)
  let s3 := maskAfter s2 .x12 28
  have p3 : s3.pc = BitVec.ofNat 64 (4096+4*704) := by
    rw [(mask_post s2 .x12 28 _ (answer_address ready answer) (by omega) (by decide)).pc]
    rfl
  have h3 := cap_jal_hop s3 704 341 2095700 (by decide) p3 rfl rfl
  have h4 := cap_jal_hop (s3.setPC (BitVec.ofNat 64 (4096+4*341))) 341 330 2097108 (by decide) rfl rfl rfl
  exact ((h1.thenDo h2).thenDo h3).thenDo h4

theorem execute_cap_hash {state : MachineState} {node : Nat} (ready : CapHashReady state node) (fuel : Nat) :
    execute packedImage (13+fuel) state false =
      (do let next ← capHashQuery state (node/2)
          let result ← execute packedImage fuel next false
          return result.charge 20 1) := by
  obtain ⟨pc, parent, source, dest, mem⟩ := cap_parent_post state ready.pc
  obtain ⟨_, src, dst⟩ := parent_registers ready
  have room := ready.bound
  have control (r : Reg) (n : r ≠ .x6) (a : r ≠ .x10) (b : r ≠ .x12) :
      (capParent state).getReg r = state.getReg r := cap_parent_register state r n a b
  have select : (capParent state).getReg .x5=0 ∧ (capParent state).getReg .x11=64 ∧
      (capParent state).getReg .x13=0 :=
    ⟨(control _ (by decide) (by decide) (by decide)).trans ready.selector,
      (control _ (by decide) (by decide) (by decide)).trans ready.size,
      (control _ (by decide) (by decide) (by decide)).trans ready.primitive⟩
  have lim : MEMORY_BYTES < 2^64 := by decide
  have memLimit : 32768 ≤ MEMORY_BYTES := by decide
  let input := 8*(2048+8*(node/2))
  have srcV : rangeValid ((capParent state).getReg .x10) 64 = true := by
    simp only [src, wordAddress, rangeValid, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8*(2048+8*(node/2)) < 2^64), decide_eq_true_eq]
    omega
  have dstV : rangeValid ((capParent state).getReg .x12) 32 = true := by
    simp only [dst, wordAddress, rangeValid, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8*(2048+4*(node/2)) < 2^64), decide_eq_true_eq]
    omega
  have asrc : ((capParent state).getReg .x10).toNat % 8 = 0 := by
    simp only [src, wordAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8*(2048+8*(node/2)) < 2^64)]
    omega
  have adst : ((capParent state).getReg .x12).toNat % 8 = 0 := by
    simp only [dst, wordAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8*(2048+4*(node/2)) < 2^64)]
    omega
  have fetched : fetch packedImage (capParent state) = some (.base .ECALL) :=
    cap_fetch _ 339 _ (by decide) (by rw [pc]; rfl) rfl
  have call := cap_compression_execute packedImage (capParent state) fetched select srcV dstV asrc adst (7+fuel) false
  have inner : readBuffer (capParent state) ((capParent state).getReg .x10).toNat 64 =
      capRootAt state (2*(node/2)+1) ++ capRootAt state (2*(node/2)) := by
    rw [src, wordAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8*(2048+8*(node/2)) < 2^64),
      read_compression_halves _ _ (by omega)]
    unfold capRootAt
    have offset : 8*(2048+8*(node/2))+32 = 8*(2048+4*(2*(node/2)+1)) := by omega
    have base : 8*(2048+8*(node/2)) = 8*(2048+4*(2*(node/2))) := by omega
    rw [offset, base]
    congr 1 <;> apply read_digest_congr _ _ _ (by omega) <;>
      intro i _ <;> exact congrFun mem _
  rw [show 13+fuel = 5+(1+(7+fuel)) by omega, execute_cap_parent_setup _ ready.pc, call]
  unfold capCompressionInput
  erw [inner]
  simp only [capHashQuery, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  rw [cap_hash_tail ready answer fuel]
  simp only [Execution.charge, bind_assoc, pure_bind, ← Nat.add_assoc, Nat.reduceAdd, Nat.add_zero]

theorem cap_hash_digest {state : MachineState} {node : Nat} (ready : CapHashReady state node)
    (answer : BitVec 256) :
    capRootAt (capHashReply state (node/2) answer) (node/2) = pad238 answer := by
  have bound := ready.bound
  let s2 := (capCompressionAnswer (capParent state) answer).setPC 0x1af0
  have words : ∀ k < 4, s2.getMem (BitVec.ofNat 64 (8*(2048+4*(node/2))+8*k)) = answer.extractLsb' (64*k) 64 := by
    intro k small
    rw [MachineState.getMem_setPC]
    unfold capCompressionAnswer
    rw [(parent_registers ready).2.2]
    exact written_dword _ _ k answer (by omega) small
  have masked := masked_slot_digest s2 .x12 (8*(2048+4*(node/2))) answer (by omega) (by omega)
    (answer_address ready answer) (by decide) words
  unfold capRootAt capHashReply
  rw [← masked]
  exact read_digest_congr _ _ _ (by omega) (fun _ _ => MachineState.getMem_setPC)

theorem cap_hash_rows (oracle : Oracle) (state : MachineState) (parent : Nat) :
    let pair := capRootAt state (2*parent+1) ++ capRootAt state (2*parent)
    let reply := oracle.compression pair
    checkEvaluation oracle (recordRows (capHashQuery state parent)) =
      ((capHashReply state parent reply, [.compression pair reply]), 1) := by
  simp only [capHashQuery, record_rows_query, check_evaluation_public_bind, check_evaluation_map,
    record_rows_pure, check_evaluation_pure]
  rfl

end TwoPermutationPrototype.Packed.Checker
