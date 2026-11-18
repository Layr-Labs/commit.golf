import CommitGolfCandidate.QuadRecordNodeEntry
import CommitGolfCandidate.QuadRecordComposition
import CommitGolfCandidate.QuadNodeHonest

namespace TwoPermutationPrototype.Quad.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling TwoPermutationPrototype.Quad.Checker
open TwoPermutationPrototype.Checker (honestIndex)
open TwoPermutationPrototype.Packed.Checker (RecordBlock)
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
attribute [local irreducible] quadWorkspace quadPrefix quadRotation writeBits quadReturn rawLeaf leafToQuad readBuffer

def block (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) : RecordBlock :=
  let raw := rawLeaf oracle ordinal index s
  let mid := leafToQuad raw.1
  let children := workspaceChildren (quadWorkspace mid)
  let input := quadInput children
  let answer := oracle.permutation input
  ⟨quadReply mid answer,182,203,raw.2++[.permutation input answer]⟩

theorem raw_digest_rows (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) :
    let message := window (memoryView (staged s)) (checkSourceWord ordinal+5)
    let nonce := checkerNonce (staged s)
    let a := pinnedFirstRow oracle.permutation message
    let b := pinnedSecondRow oracle.permutation index nonce a.2 message
    (rawLeaf oracle ordinal index s).2=[.permutation a.1 a.2,.permutation b.1 b.2] ∧
      readBuffer (rawLeaf oracle ordinal index s).1 12288 32=outputDigest b.2 := by
  unfold rawLeaf
  rw [checker_leaf_rows]
  exact ⟨rfl,checker_leaf_digest _ _ _ _⟩

/-- The two transition words preserve all proof fields. The pinned leaf writes
only its current entry and the separated scratch region. -/
theorem node_entry_proof (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (s : MachineState) (fits : ProofWithin input)
    (cursor : RecordCursor input ordinal s) (framed : RecordInputFrame input ordinal s)
    (offset count : Nat) (inside : offset+count≤ 534) :
    readBuffer (nodeEntry oracle ordinal (honestIndex input.positions ordinal present).val s)
      (checkProofByte ordinal+offset) count=readBuffer s (checkProofByte ordinal+offset) count := by
  let index := (honestIndex input.positions ordinal present).val
  let raw := (rawLeaf oracle ordinal index s).1
  have view := raw_view oracle input ordinal present s fits cursor framed
  have memory := (leaf_to_quad_post raw view.1).2.2.2
  have initial := (read_buffer_memory_congr _ _ memory (checkProofByte ordinal+offset) count)
  apply initial.trans
  apply buffer_byte_frame
  intro j hj
  have card := checker_positions_bound input
  have geometry := quad_record_geometry input ordinal present fits
  apply view.2.2.2 _ (by unfold checkProofByte; unfold MEMORY_BYTES at geometry; omega)
  · right
    unfold checkProofByte checkSourceWord
    omega
  · right
    unfold checkProofByte
    omega

theorem block_trace (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (s : MachineState) (fits : ProofWithin input)
    (cursor : RecordCursor input ordinal s) (framed : RecordInputFrame input ordinal s) :
    let item := honestIndex input.positions ordinal present
    Nonempty (QuadLeafTrace oracle item.val (input.values item)
      (readBuffer (block oracle ordinal item.val s).state 12288 32) (block oracle ordinal item.val s).rows) := by
  let item := honestIndex input.positions ordinal present
  let raw := rawLeaf oracle ordinal item.val s
  let mid := leafToQuad raw.1
  let children := workspaceChildren (quadWorkspace mid)
  let inputBlock := quadInput children
  let answer := oracle.permutation inputBlock
  have ready := (node_entry_facts oracle input ordinal present s fits cursor framed).ready
  have meaning := raw_digest_rows oracle ordinal item.val s
  have values := staged_entry_words input ordinal present s fits cursor framed
  dsimp only at meaning
  rw [values] at meaning
  have memory := (leaf_to_quad_post raw.1 (raw_view oracle input ordinal present s fits cursor framed).1).2.2.2
  have digest : readBuffer mid 12288 32=outputDigest
      (pinnedSecondRow oracle.permutation item.val (checkerNonce (staged s))
        (pinnedFirstRow oracle.permutation (entryWords (input.values item))).2 (entryWords (input.values item))).2 :=
    (read_buffer_memory_congr _ _ memory _ _).trans meaning.2
  have opened := (quad_workspace_input mid ⟨item.val.val%4,Nat.mod_lt _ (by decide)⟩ (checkProofByte ordinal+16)
    ready.pair ready.digest ready.opened ready.source ready.room ready.even ready.above).2
  refine ⟨⟨checkerNonce (staged s),?_,?_,children,opened.trans digest,answer,?_,?_⟩⟩
  · change PublicRow.permutation _ _ ∈ raw.2++[.permutation inputBlock answer]
    apply List.mem_append_left
    rw [show raw.2=_ from meaning.1]
    exact List.mem_cons_self
  · change PublicRow.permutation _ _ ∈ raw.2++[.permutation inputBlock answer]
    apply List.mem_append_left
    rw [show raw.2=_ from meaning.1]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · change PublicRow.permutation inputBlock answer ∈ raw.2++[.permutation inputBlock answer]
    exact List.mem_append_right _ List.mem_cons_self
  · exact (quad_reply_digest mid answer).symm

theorem block_honest (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (s : MachineState) (fits : ProofWithin input)
    (cursor : RecordCursor input ordinal s) (framed : RecordInputFrame input ordinal s)
    (message : Message) (salts : CompleteSaltTape)
    (canonical : input=honestCheckInput oracle message input.positions salts) :
    let item := honestIndex input.positions ordinal present
    readBuffer (block oracle ordinal item.val s).state 12288 32=
      Honest.honestHeap oracle message salts (lowerNode item.val 0) := by
  let item := honestIndex input.positions ordinal present
  let raw := rawLeaf oracle ordinal item.val s
  let mid := leafToQuad raw.1
  let leaves := Honest.honestLeaves oracle message salts
  have ready := (node_entry_facts oracle input ordinal present s fits cursor framed).ready
  have memory := (leaf_to_quad_post raw.1 (raw_view oracle input ordinal present s fits cursor framed).1).2.2.2
  have digest := (raw_digest_rows oracle ordinal item.val s).2
  rw [staged_entry_words input ordinal present s fits cursor framed,
    staged_honest_nonce_words oracle input ordinal present s fits cursor framed message salts canonical,
    canonical_entry_value oracle input message salts item canonical] at digest
  have leafDigest : readBuffer mid 12288 32=leaves item.val := by
    apply (read_buffer_memory_congr _ _ memory _ _).trans
    exact digest.trans (honest_row_digest oracle message salts item.val)
  have loaded : RecordInputFrame (honestCheckInput oracle message input.positions salts) ordinal s :=
    Eq.mp (congrArg (fun data => RecordInputFrame data ordinal s) canonical) framed
  have siblings (j : Nat) (which : j < 3) :
      readBuffer mid (checkProofByte ordinal+16+32*j) 32=quadLeaf leaves item.val (quadRotSlot item.val j) := by
    have frame := node_entry_proof oracle input ordinal present s fits cursor framed (16+32*j) 32 (by omega)
    have data := quad_record_child oracle message input.positions salts ordinal j present which s loaded
    rw [←Nat.add_assoc] at frame
    exact frame.trans data
  have children := quad_workspace_honest mid item.val (checkProofByte ordinal+16) ready leaves leafDigest siblings
  change readBuffer (quadReply mid (oracle.permutation (quadInput (workspaceChildren (quadWorkspace mid))))) 12288 32=_
  rw [quad_reply_digest,children]
  exact quad_honest_start oracle leaves item.val

end TwoPermutationPrototype.Quad.RecordLeaf
