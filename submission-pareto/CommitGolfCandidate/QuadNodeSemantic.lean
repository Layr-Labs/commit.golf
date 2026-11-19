import CommitGolfCandidate.QuadNodeWorkspace

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] quadWorkspace quadPrefix quadRotation writeBits quadReturn
  checkEvaluation recordRows quadNode quadFinish packBuffer readBuffer

private theorem call_prepared_pc (s : MachineState) : (quadCallPrepared s).pc=s.pc+4 := rfl
private theorem call_prepared_memory (s : MachineState) : (quadCallPrepared s).mem=s.mem := rfl
private theorem call_prepared_register (s : MachineState) (reg : Reg) (kept : reg≠.x12) :
    (quadCallPrepared s).getReg reg=s.getReg reg := by
  simp [quadCallPrepared,execInstrBr,MachineState.getReg_setPC,Opening.getReg_setReg,Ne.symm kept]
private theorem node_write_pc (s : MachineState) (address : Word) (answer : Block) :
    (writeBits s address answer).pc=s.pc+4 := by unfold writeBits; rfl

/-- Concrete reply state of the actual quad call and its binary-loop return. -/
def quadReply (s : MachineState) (answer : Block) : MachineState :=
  quadReturn (writeBits (quadCallPrepared (quadWorkspace s)) (wordAddress 1536) answer) 3

structure QuadNodeReady (s : MachineState) (slot : Fin 4) (proof : Nat) : Prop where
  pair : s.getReg .x24=12544
  digest : s.getReg .x23=12288
  opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val
  source : s.getReg .x21=BitVec.ofNat 64 proof
  room : proof+96≤MEMORY_BYTES
  even : proof%2=0
  above : 32768≤proof

theorem quad_node_observation (oracle : Oracle) (s : MachineState) (slot : Fin 4) (proof : Nat)
    (ready : QuadNodeReady s slot proof) :
    let input := quadInput (workspaceChildren (quadWorkspace s))
    let answer := oracle.permutation input
    checkEvaluation oracle (recordRows (quadNode s))=
      ((quadReply s answer,[.permutation input answer]),1) := by
  have nodeEq : quadNode s=quadFinish (quadWorkspace s) := by
    unfold quadNode quadWorkspace
    rfl
  rw [nodeEq,quad_finish_rows]
  have inp : (packBuffer (window (memoryView (quadWorkspace s)) 1600) : Block)=
      quadInput (workspaceChildren (quadWorkspace s)) := (quad_workspace_input s slot proof ready.pair ready.digest ready.opened ready.source
    ready.room ready.even ready.above).1
  exact congrArg (fun input : Block =>
    ((quadReply s (oracle.permutation input),[PublicRow.permutation input (oracle.permutation input)]),1)) inp

theorem quad_reply_digest (s : MachineState) (answer : Block) :
    readBuffer (quadReply s answer) 12288 32=answer.extractLsb' 0 256 :=
  quad_finish_digest (quadWorkspace s) answer

theorem quad_reply_saved (s : MachineState) (slot : Fin 4) (proof : Nat)
    (ready : QuadNodeReady s slot proof) (answer : Block) (reg : Reg)
    (a : reg≠.x6) (b : reg≠.x10) (d : reg≠.x12)
    (f : reg≠.x21) (g : reg≠.x28) (h : reg≠.x29) (i : reg≠.x30) (j : reg≠.x31) :
    (quadReply s answer).getReg reg=s.getReg reg := by
  unfold quadReply
  rw [quad_return_register _ reg a h,writeBits_register]
  exact (call_prepared_register (quadWorkspace s) reg d).trans (quad_workspace_register s slot proof ready.pair ready.opened ready.source ready.room ready.even
    reg b f g h i j)

theorem quad_reply_post (s : MachineState) (slot : Fin 4) (proof : Nat)
    (ready : QuadNodeReady s slot proof) (answer : Block) (n : Nat)
    (node : s.getReg .x6=BitVec.ofNat 64 n) (bound : n<2^64) :
    (quadReply s answer).pc=(if n/4/2^21=0 then 5824 else 5564) ∧
    (quadReply s answer).getReg .x6=BitVec.ofNat 64 (n/4) ∧
    (quadReply s answer).getReg .x21=BitVec.ofNat 64 (proof+96) ∧
    (quadReply s answer).getReg .x29=BitVec.ofNat 64 (n/4/2^21) := by
  have post := quad_workspace_post s slot proof ready.pair ready.opened ready.source ready.room ready.even
  have pc : (writeBits (quadCallPrepared (quadWorkspace s)) (wordAddress 1536) answer).pc=5812 := by
    rw [node_write_pc,call_prepared_pc,post.1]
    rfl
  have nodeW : (writeBits (quadCallPrepared (quadWorkspace s)) (wordAddress 1536) answer).getReg .x6=
      BitVec.ofNat 64 n := by
    rw [writeBits_register]
    rw [call_prepared_register _ .x6 (by decide)]
    exact (quad_workspace_register s slot proof ready.pair ready.opened ready.source ready.room ready.even
      .x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans node
  have returned := quad_return_post _ pc n nodeW bound
  have src : (quadReply s answer).getReg .x21=BitVec.ofNat 64 (proof+96) := by
    unfold quadReply
    rw [quad_return_register _ .x21 (by decide) (by decide),writeBits_register]
    exact (call_prepared_register _ .x21 (by decide)).trans post.2.2
  exact ⟨returned.1,returned.2.1,src,returned.2.2.1⟩

/-- Workspace writes and the permutation's complete 200-byte reply are framed. -/
theorem quad_reply_frame (s : MachineState) (slot : Fin 4) (proof : Nat)
    (ready : QuadNodeReady s slot proof) (answer : Block) (word : Nat) (bounded : word<2^33)
    (replyOutside : word<1536 ∨ 1561≤word) (workspaceOutside : word<1600 ∨ 1625≤word) :
    memoryView (quadReply s answer) word=memoryView s word := by
  change BitVec 1600 at answer
  unfold quadReply
  change (quadReturn (writeBits (quadCallPrepared (quadWorkspace s)) (wordAddress 1536) answer) 3).getMem (wordAddress word)=_
  rw [MachineState.getMem,quad_return_memory]
  change memoryView (writeBits (quadCallPrepared (quadWorkspace s)) (wordAddress 1536) answer) word=_
  rw [permutation_write_memory _ 1536 word answer (by decide) bounded,writeWindow,
    dite_eq_right (by omega : ¬(1536≤word ∧ word<1536+25))]
  exact (congrFun (call_prepared_memory (quadWorkspace s)) (wordAddress word)).trans
    (quad_workspace_frame s slot proof ready.pair ready.digest ready.opened ready.source
      ready.room ready.even ready.above word bounded workspaceOutside)

end TwoPermutationPrototype.Quad.Checker
