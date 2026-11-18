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

/-- First pass (quad node) reply, at the start of the second pass. -/
def secondEntry (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) : MachineState :=
  let mid := leafToQuad (rawLeaf oracle ordinal index s).1
  quadReply mid (oracle.permutation (quadInput (workspaceChildren (quadWorkspace mid))))

def block (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) : RecordBlock :=
  let raw := rawLeaf oracle ordinal index s
  let mid := leafToQuad raw.1
  let input := quadInput (workspaceChildren (quadWorkspace mid))
  let answer := oracle.permutation input
  let mid2 := quadReply mid answer
  let input2 := quadInput (workspaceChildren (quadWorkspace mid2))
  let answer2 := oracle.permutation input2
  ⟨quadExit (quadReply mid2 answer2) 4,325,353,raw.2++[.permutation input answer,.permutation input2 answer2]⟩

theorem quad2_opened_slot (index : Index) :
    BitVec.ofNat 64 ((LENGTH+index.val)/4) &&& 3#64=BitVec.ofNat 64 ((index.val/4)%4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,BitVec.toNat_ofNat,BitVec.toNat_ofNat]
  change (((16777216+index.val)/4)%2^64) &&& (2^2-1)=((index.val/4)%4)%2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have := index.isLt
  change index.val<16777216 at this
  omega

/-- Second-pass entry: the first quad reply loops back to the block start with
the shifted node index and the cursor at the three quad neighbours. -/
structure SecondEntryFacts (ordinal : Nat) (index : Index) (s : MachineState) : Prop where
  ready : QuadNodeReady s ⟨(index.val/4)%4,Nat.mod_lt _ (by decide)⟩ (checkProofByte ordinal+112)
  pc : s.pc=5564
  node : s.getReg .x6=BitVec.ofNat 64 ((LENGTH+index.val)/4)
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1

theorem second_entry_facts (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal< input.positions.card) (s : MachineState) (fits : ProofWithin input)
    (cursor : RecordCursor input ordinal s) (framed : RecordInputFrame input ordinal s) :
    SecondEntryFacts ordinal (honestIndex input.positions ordinal present).val
      (secondEntry oracle ordinal (honestIndex input.positions ordinal present).val s) := by
  let index := (honestIndex input.positions ordinal present).val
  let mid := nodeEntry oracle ordinal index s
  let answer := oracle.permutation (quadInput (workspaceChildren (quadWorkspace mid)))
  have entry := node_entry_facts oracle input ordinal present s fits cursor framed
  have indexBound : index.val<16777216 := index.isLt
  have post := quad_reply_post mid _ _ entry.ready answer (LENGTH+index.val) entry.node
    (by change 16777216+index.val<2^64; omega)
  have keep (r : Reg) (a : r≠.x6) (b : r≠.x10) (d : r≠.x12)
      (f : r≠.x21) (g : r≠.x28) (h : r≠.x29) (i : r≠.x30) (j : r≠.x31) :
      (quadReply mid answer).getReg r=mid.getReg r :=
    quad_reply_saved mid _ _ entry.ready answer r a b d f g h i j
  have bounds := quad_record_geometry input ordinal present fits
  have loops : ¬ (LENGTH+index.val)/4/2^21=0 := by
    change ¬ (16777216+index.val)/4/2097152=0
    omega
  change SecondEntryFacts ordinal index (quadReply mid answer)
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,post.2.1,?_,?_,?_⟩
  · exact (keep .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans entry.ready.pair
  · exact (keep .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans entry.ready.digest
  · rw [post.2.1]
    exact quad2_opened_slot index
  · exact post.2.2.1.trans (by rw [Nat.add_assoc])
  · have room := bounds.2.2.2.1
    omega
  · have align := bounds.1
    omega
  · have above := bounds.2.2.1
    omega
  · rw [post.1,if_neg loops]
  · exact (keep .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans entry.selector
  · exact (keep .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans entry.size
  · exact (keep .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans entry.primitive

/-- Proof bytes of the record are untouched by the first quad pass. -/
theorem second_entry_proof (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (s : MachineState) (fits : ProofWithin input)
    (cursor : RecordCursor input ordinal s) (framed : RecordInputFrame input ordinal s)
    (offset count : Nat) (inside : offset+count≤570) :
    readBuffer (secondEntry oracle ordinal (honestIndex input.positions ordinal present).val s)
      (checkProofByte ordinal+offset) count=
      readBuffer (nodeEntry oracle ordinal (honestIndex input.positions ordinal present).val s)
        (checkProofByte ordinal+offset) count := by
  let index := (honestIndex input.positions ordinal present).val
  let mid := nodeEntry oracle ordinal index s
  have entry := node_entry_facts oracle input ordinal present s fits cursor framed
  have geometry := quad_record_geometry input ordinal present fits
  apply buffer_byte_frame
  intro j hj
  apply quad_reply_frame mid _ _ entry.ready _ _ (by unfold checkProofByte at geometry ⊢; unfold MEMORY_BYTES at geometry; omega)
  · right; unfold checkProofByte; omega
  · right; unfold checkProofByte; omega

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
    (offset count : Nat) (inside : offset+count≤ 570) :
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
  let mid2 := quadReply mid answer
  let children2 := workspaceChildren (quadWorkspace mid2)
  let inputBlock2 := quadInput children2
  let answer2 := oracle.permutation inputBlock2
  have ready := (node_entry_facts oracle input ordinal present s fits cursor framed).ready
  have ready2 := (second_entry_facts oracle input ordinal present s fits cursor framed).ready
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
  have opened2 := (quad_workspace_input mid2 ⟨(item.val.val/4)%4,Nat.mod_lt _ (by decide)⟩ (checkProofByte ordinal+112)
    ready2.pair ready2.digest ready2.opened ready2.source ready2.room ready2.even ready2.above).2
  have rows : (block oracle ordinal item.val s).rows=raw.2++[.permutation inputBlock answer,.permutation inputBlock2 answer2] := rfl
  refine ⟨⟨checkerNonce (staged s),?_,?_,children,opened.trans digest,answer,?_,
    children2,opened2.trans (quad_reply_digest mid answer),answer2,?_,?_⟩⟩
  · rw [rows]
    apply List.mem_append_left
    rw [show raw.2=_ from meaning.1]
    exact List.mem_cons_self
  · rw [rows]
    apply List.mem_append_left
    rw [show raw.2=_ from meaning.1]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · rw [rows]
    exact List.mem_append_right _ List.mem_cons_self
  · rw [rows]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · change answer2.extractLsb' 0 256=readBuffer (quadExit (quadReply mid2 answer2) 4) 12288 32
    rw [read_buffer_memory_congr _ _ (quad_exit_memory _) _ _]
    exact (quad_reply_digest mid2 answer2).symm

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
  let quad := Honest.honestQuad oracle
  have ready := (node_entry_facts oracle input ordinal present s fits cursor framed).ready
  have ready2 := (second_entry_facts oracle input ordinal present s fits cursor framed).ready
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
  let answer := oracle.permutation (quadInput (workspaceChildren (quadWorkspace mid)))
  let mid2 := quadReply mid answer
  have firstValue : readBuffer mid2 12288 32=quad (quadLeaf leaves item.val) := by
    change readBuffer (quadReply mid answer) 12288 32=_
    rw [quad_reply_digest]
    change (oracle.permutation (quadInput (workspaceChildren (quadWorkspace mid)))).extractLsb' 0 256=_
    rw [children]
    rfl
  have siblings2 (j : Nat) (which : j < 3) :
      readBuffer mid2 (checkProofByte ordinal+112+32*j) 32=
        quad2Group quad leaves (item.val.val/16) ⟨((item.val.val/4)%4+j+1)%4,Nat.mod_lt _ (by decide)⟩ := by
    have frame2 := second_entry_proof oracle input ordinal present s fits cursor framed (112+32*j) 32 (by omega)
    have frame := node_entry_proof oracle input ordinal present s fits cursor framed (112+32*j) 32 (by omega)
    have data := quad_record_quad_child oracle message input.positions salts ordinal j present which s loaded
    rw [←Nat.add_assoc] at frame frame2
    exact frame2.trans (frame.trans (data.trans (quad2_neighbour_child quad leaves item.val j)))
  have children2 := quad_workspace_children mid2 _ (checkProofByte ordinal+112) ready2
    (quad2Group quad leaves (item.val.val/16)) (firstValue.trans (quad2_opened_child quad leaves item.val).symm) siblings2
  let answer2 := oracle.permutation (quadInput (workspaceChildren (quadWorkspace mid2)))
  change readBuffer (quadExit (quadReply mid2 answer2) 4) 12288 32=_
  rw [read_buffer_memory_congr _ _ (quad_exit_memory _) _ _,quad_reply_digest]
  change (oracle.permutation (quadInput (workspaceChildren (quadWorkspace mid2)))).extractLsb' 0 256=_
  rw [children2]
  exact quad2_honest_start oracle leaves item.val

end TwoPermutationPrototype.Quad.RecordLeaf
