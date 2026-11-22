import CommitGolfCandidate.GroupOpenRecordsAPI
import CommitGolfCandidate.GroupOpenRecordTail
import CommitGolfCandidate.GroupOpenSetup
import CommitGolfCandidate.TwoPermutationOpeningRecordGroups

namespace TwoPermutationPrototype.GroupedOpening
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (sortedIndex markBase
  RecordMarks groupsBefore machineMarks nat_address_injective)

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC

@[local simp] private theorem reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

private theorem tail_register (state : MachineState) (reg : Reg)
    (temp : reg ≠ .x7) (index : reg ≠ .x8) :
    (recordTailPrefix state 4).getReg reg = state.getReg reg := by
  by_cases done : state.getReg .x8 + 8#64 = state.getReg .x17 <;>
    simp [recordTailPrefix, recordTailInstructions, Opening.recordTailInstructions, execInstrBr,
      signExtend12, done, Ne.symm temp, Ne.symm index]

attribute [local irreducible] execute recordData

private theorem after_latch_memory (marked : MachineState) (final : Bool) :
    (afterLatch marked final).mem = marked.mem := by cases final <;> rfl

private theorem after_latch_register (marked : MachineState) (final : Bool) (r : Reg) :
    (afterLatch marked final).getReg r = marked.getReg r := by cases final <;> rfl

private def latchCost (final : Bool) : Nat := if final then 6 else 5

private def branchOff (c : Nat) :=
  BitVec.ofNat 13 (8192+4*(Whole.row (Whole.nextClass c) 0-3)-4*(Whole.row c 22+4))
private def exitOff (c : Nat) :=
  BitVec.ofNat 21 (2^21+4*1097-4*(Whole.row c 22+5))
private def markRows : List Instr := Opening.recordTailInstructions.take 4

private theorem latch_table (c : Fin 4) :
    Whole.Slice (Whole.row c 22) markRows ∧
    (openingImage.code[Whole.row c 22+4]?).bind Opening.decodeBase=some (.BNE .x8 .x17 (branchOff c)) ∧
    (openingImage.code[Whole.row c 22+5]?).bind Opening.decodeBase=some (.JAL .x0 (exitOff c)) ∧
    Whole.pcAt (Whole.row c 22+4)+signExtend13 (branchOff c)=Whole.pcAt (Whole.row (Whole.nextClass c) 0-3) ∧
    Whole.pcAt (Whole.row c 22+5)+signExtend21 (exitOff c)=Whole.pcAt 1097 ∧
    Whole.row c 22+5<7872 := by revert c;decide +kernel

@[local simp] private theorem mem_pc_latch (s : MachineState) (v : Word) : (s.setPC v).mem=s.mem := rfl
@[local simp] private theorem mem_reg_latch (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem=s.mem := by cases r <;> rfl

private theorem mark_post (s : MachineState) :
    let m:=recordTailPrefix s 4
    m.mem=(s.setMem (Opening.recordMarkAddress s) (s.getReg .x23)).mem ∧
    m.getReg .x8=s.getReg .x8+8#64 ∧ m.pc=s.pc+16 := by
  refine ⟨?_,rfl,?_⟩
  · simp [recordTailPrefix,recordTailInstructions,Opening.recordTailInstructions,execInstrBr,Opening.recordMarkAddress,MachineState.setMem,signExtend12]
  · change s.pc+4+4+4+4=s.pc+16
    simp only [BitVec.add_assoc];rfl

private theorem run_latch (s : MachineState) (o : Nat) (last : Prop) [Decidable last]
    (pc : s.pc=Whole.pcAt (Whole.row (Whole.pageClass o) 22))
    (safe : accessValid (Opening.recordMarkAddress s) 8=true)
    (stop : s.getReg .x8+8#64=s.getReg .x17 ↔ last)
    (dp : s.getReg .x21=BitVec.ofNat 64 (recordBase (o+1))) (bound : o<LENGTH) :
    let m:=recordTailPrefix s 4
    RunsOpeningBlock s (afterLatch m (decide last)) (latchCost (decide last)) ∧
    (afterLatch m (decide last)).pc=(if last then Whole.pcAt 1097 else Whole.setupPC (o+1)) := by
  let c : Fin 4:=⟨Whole.pageClass o,Whole.class_lt o⟩
  let m:=recordTailPrefix s 4
  obtain ⟨rows,br,jump,bTarget,jTarget,fit⟩:=latch_table c
  have start : RunsOpeningBlock s m 4 := Shifted30.code_run markRows _ s
    (by change _+4≤_;omega) (Whole.codeOfSlice rows) ⟨rfl,rfl,by simpa [memoryArgumentsValid,memAccess,execInstrBr,Opening.recordMarkAddress,signExtend12] using safe,rfl,trivial⟩ pc (by decide)
    (by intro u i member
        change i ∈ [.SLLI .x7 .x6 3,.ADD .x7 .x26 .x7,.SD .x7 .x23 0,.ADDI .x8 .x8 8] at member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl|rfl|rfl <;> rfl)
  have post:=mark_post s
  have atBranch : m.pc=Whole.pcAt (Whole.row c 22+4) := by rw [show m.pc=_ from post.2.2,pc];exact ofNat_step _ 4
  have runB:=run_step m _ _ (by omega) atBranch br rfl rfl
  have endTest : m.getReg .x8=m.getReg .x17 ↔ last := by
    rw [show m.getReg .x8=_ from post.2.1,show m.getReg .x17=_ from tail_register s .x17 (by decide) (by decide)];exact stop
  have next : Whole.pageClass (o+1)=Whole.nextClass c := Whole.class_succ o
  have toNat : (m.getReg .x21).toNat=recordBase (o+1) := by
    have fit:=all_record_ends_fit o bound
    rw [show m.getReg .x21=_ from tail_register s .x21 (by decide) (by decide),dp,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_of_le_of_lt fit (by decide : MEMORY_BYTES<2^64))]
  by_cases lastH : last
  · have cmp : m.getReg .x8=m.getReg .x17 := endTest.mpr lastH
    have e : execInstrBr m (.BNE .x8 .x17 (branchOff c))=m.setPC (Whole.pcAt (Whole.row c 22+5)) := by
      have bn : (m.getReg .x8 != m.getReg .x17)=false := by simp [cmp]
      simp only [execInstrBr,bn,Bool.false_eq_true,if_false,atBranch]
      exact congrArg m.setPC (ofNat_four _)
    rw [e] at runB
    let t:=m.setPC (Whole.pcAt (Whole.row c 22+5))
    have runJ:=run_step t _ _ fit (show t.pc=_ from rfl) jump rfl rfl
    have ex : execInstrBr t (.JAL .x0 (exitOff c))=m.setPC (Whole.pcAt 1097) := by
      change m.setPC (Whole.pcAt (Whole.row c 22+5)+signExtend21 (exitOff c))=_;rw [jTarget]
    rw [ex] at runJ
    simp only [decide_eq_true lastH,if_pos lastH,afterLatch,latchCost,if_true]
    exact ⟨(start.next runB).next runJ,rfl⟩
  · have cmp : m.getReg .x8≠m.getReg .x17 := fun e => lastH (endTest.mp e)
    have e : execInstrBr m (.BNE .x8 .x17 (branchOff c))=m.setPC (Whole.pcAt (Whole.row (Whole.nextClass c) 0-3)) := by
      simp [execInstrBr,cmp,atBranch,bTarget]
    rw [e] at runB
    have cls : (m.getReg .x21).toNat%8/2=Whole.nextClass c := by rw [toNat];exact next
    change RunsOpeningBlock s (afterLatch m _) _ ∧ (afterLatch m _).pc=_
    simp only [decide_eq_false lastH,if_neg lastH,afterLatch,latchCost,Bool.false_eq_true,if_false,cls,
      Whole.setupPC,if_neg (show o+1≠0 by omega),next]
    exact ⟨start.next runB,rfl⟩

private theorem complete_record_cost (ordinal : Nat) (final : Bool) :
    127+recordExtra ordinal+latchCost final = recordCost ordinal final := by
  cases final <;> simp [recordCost, latchCost] <;> omega

private theorem execute_record_with_data (s : Submission)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state prepared : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (boundary : RecordBoundary s trapdoor positions state ordinal)
    (data : RecordData state prepared (sortedIndex positions ordinal present) ordinal) :
    OneRecord s trapdoor positions state
      (afterLatch (recordTailPrefix prepared 4) (decide (ordinal+1=positions.card))) ordinal present := by
  let index := sortedIndex positions ordinal present
  let marked := recordTailPrefix prepared 4
  let done := afterLatch marked (decide (ordinal+1=positions.card))
  have sameBase : Opening.trapdoorBase = trapdoorBase := rfl
  let group := Sampling.capGroup index
  let markAddr := markBase+8*group
  have card : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have pc : prepared.pc=Whole.pcAt (Whole.row (Whole.pageClass ordinal) 22) := data.cursor.pc
  have groupBound : group < 512 := (Opening.lower_cap_range index).2
  have markFit : markAddr < trapdoorBase := by
    have room := Opening.marks_before_trapdoor
    unfold markAddr
    omega
  have address : Opening.recordMarkAddress prepared = BitVec.ofNat 64 markAddr :=
    Opening.record_mark_address prepared group
      ((data.register .x26 (by decide)).trans boundary.marks)
      data.cursor.node
  have safe : accessValid (Opening.recordMarkAddress prepared) 8 = true := by
    rw [address]
    apply Opening.aligned_access
    · have aligned : markBase % 8 = 0 := by decide
      unfold markAddr
      omega
    · have room : trapdoorBase+8 ≤ MEMORY_BYTES := by decide
      omega
  have post := mark_post prepared
  have pointer : prepared.getReg .x8 = BitVec.ofNat 64 (indicesBase+8*ordinal) :=
    (data.register .x8 (by decide)).trans boundary.index
  have finish : prepared.getReg .x17 = BitVec.ofNat 64 (indicesBase+8*positions.card) :=
    (data.register .x17 (by decide)).trans boundary.endIndex
  have bumped : prepared.getReg .x8 + 8#64 = BitVec.ofNat 64 (indicesBase+8*(ordinal+1)) := by
    rw [pointer, ← BitVec.ofNat_add]
    congr 1
  have nowEnd : prepared.getReg .x8 + 8#64 = prepared.getReg .x17 ↔ ordinal+1=positions.card := by
    have base : indicesBase = 9395245088 := rfl
    have length : LENGTH = 16777216 := rfl
    rw [bumped, finish]
    constructor
    · intro z
      have eq := nat_address_injective (by omega) (by omega) z
      omega
    · intro z
      rw [z]
  have endDest : prepared.getReg .x21=BitVec.ofNat 64 (recordBase (ordinal+1)) := by
    exact data.cursor.dest.trans (congrArg (BitVec.ofNat 64) (record_end ordinal))
  obtain ⟨tail,nextPC⟩:=run_latch prepared ordinal (ordinal+1=positions.card) pc safe nowEnd endDest (by omega)
  have doneMem : done.mem = marked.mem := after_latch_memory marked _
  have doneReg (r : Reg) : done.getReg r = marked.getReg r := after_latch_register marked _ r
  have saved (r : Reg) (free : r ∉ recordScratch) (b : r ≠ .x7) (e : r ≠ .x8) : done.getReg r=state.getReg r :=
    (doneReg r).trans ((tail_register prepared r b e).trans (data.register r free))
  have one : prepared.getReg .x23 = 1#64 :=
    (data.register .x23 (by decide)).trans boundary.one
  have store : done.mem = (prepared.setMem (BitVec.ofNat 64 markAddr) 1#64).mem :=
    doneMem.trans (by rw [show marked.mem=_ from post.1,address,one])
  have stableWord (query : Word) (neq : query ≠ BitVec.ofNat 64 markAddr) :
      done.getMem query = prepared.getMem query := by
    have same := congrFun store query
    exact same.trans (MachineState.getMem_setMem_ne neq)
  have fit64 : MEMORY_BYTES+8 ≤ 2^64 := by decide
  have stableByte (query : Nat) (fit : query < MEMORY_BYTES) (above : trapdoorBase ≤ query) :
      done.getByte (BitVec.ofNat 64 query) = prepared.getByte (BitVec.ofNat 64 query) := by
    have different : alignToDword (BitVec.ofNat 64 query) ≠ BitVec.ofNat 64 markAddr := by
      intro same
      have aligned := aligned_dword_above trapdoorBase query (by decide) above (by omega)
      rw [same, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : markAddr < 2^64)] at aligned
      omega
    simp only [MachineState.getByte, stableWord _ different]
  refine ⟨?_, ⟨nextPC,
    (saved .x9 (by decide) (by decide) (by decide)).trans boundary.heap,
    ?_, (saved .x22 (by decide) (by decide) (by decide)).trans boundary.nonce,
    ?_, (saved .x19 (by decide) (by decide) (by decide)).trans boundary.leaves,
    (saved .x24 (by decide) (by decide) (by decide)).trans boundary.slots, ?_,
    (saved .x17 (by decide) (by decide) (by decide)).trans boundary.endIndex,
    (saved .x26 (by decide) (by decide) (by decide)).trans boundary.marks,
    (saved .x23 (by decide) (by decide) (by decide)).trans boundary.one,
    (saved .x25 (by decide) (by decide) (by decide)).trans boundary.capHeap,
    (saved .x27 (by decide) (by decide) (by decide)).trans boundary.capLeaves,
    (saved .x20 (by decide) (by decide) (by decide)).trans boundary.proofBegin, boundary.pointer⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · have whole := data.run.next tail
    change RunsOpeningBlock state done (recordCost ordinal (decide (ordinal+1=positions.card)))
    rw [← complete_record_cost]
    exact whole
  · have pointer := (data.register .x8 (by decide)).trans boundary.index
    have bump := congrArg (fun a : Word => a+8#64) pointer
    apply (doneReg .x8).trans (post.2.1.trans (bump.trans _))
    rw [← BitVec.ofNat_add]
    congr 1
  · have nextDest := data.cursor.dest.trans (congrArg (BitVec.ofNat 64) (record_end ordinal))
    exact (doneReg .x21).trans ((tail_register prepared .x21 (by decide) (by decide)).trans nextDest)
  · intro query above below aligned
    have limit : proofBase < 2^64 := by decide
    have neq : BitVec.ofNat 64 query ≠ BitVec.ofNat 64 markAddr := by
      intro same
      have eq := nat_address_injective (by omega) (by omega) same
      omega
    exact (stableWord _ neq).trans ((data.input _ below).trans (boundary.input _ above below aligned))
  · intro node bounded
    change machineMarks done node = if node=group then 1 else machineMarks state node
    by_cases same : node = group
    · subst node
      rw [ite_eq_left rfl]
      exact (congrFun store (BitVec.ofNat 64 markAddr)).trans MachineState.getMem_setMem_eq
    · have fit := Opening.marks_before_trapdoor
      have heapFit : trapdoorBase < 2^64 := by decide
      have different : BitVec.ofNat 64 (markBase+8*node) ≠ BitVec.ofNat 64 markAddr := by
        intro sameAddr
        have eq := nat_address_injective (by omega) (by omega) sameAddr
        unfold markAddr at eq
        apply same
        omega
      have valid : markBase+8*node < proofBase := by
        have afterHeap : trapdoorBase ≤ proofBase := by decide
        omega
      rw [ite_eq_right same]
      exact (stableWord _ different).trans (data.input _ valid)
  · intro query fit above outside
    exact (stableByte query fit above).trans (data.frame query (by omega) outside)
  · intro b inside
    have fits := all_record_ends_fit ordinal (by omega)
    have mem : MEMORY_BYTES+8 ≤ 2^64 := by decide
    have low : trapdoorBase ≤ proofBase := by decide
    have targetFit : recordBase ordinal+b < MEMORY_BYTES := by unfold recordBase recordBytes at *; omega
    exact (stableByte _ (by omega) (by unfold recordBase; omega)).trans (data.nonce b inside)
  · intro l hl b inside
    have fits := (all_sibling_copies_fit index ordinal l (by omega) hl).2.2.2
    have narrow := plain_width_le l
    have mem : MEMORY_BYTES+8 ≤ 2^64 := by decide
    have low : trapdoorBase ≤ proofBase := by decide
    exact (stableByte _ (by omega) (by unfold siblingDestination recordBase; omega)).trans (data.sibling l hl b inside)
  · intro k hk b hb
    have fits := (all_sibling_copies_fit index ordinal (6+k) (by omega) (by omega)).2.2.2
    have width : siblingWidth (6+k) = 30 := by unfold siblingWidth; rw [if_neg (by omega), if_pos (by omega)]
    have mem : MEMORY_BYTES+8 ≤ 2^64 := by decide
    have low : trapdoorBase ≤ proofBase := by decide
    exact (stableByte _ (by omega) (by unfold siblingDestination recordBase; omega)).trans (data.fold k hk b hb)

theorem execute_record (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (boundary : RecordBoundary s trapdoor positions state ordinal) :
    OneRecord s trapdoor positions state (runRecord state (decide (ordinal+1=positions.card))) ordinal present :=
  execute_record_with_data s trapdoor positions state (recordData state) ordinal present boundary
    (execute_record_data s layout trapdoor positions state ordinal present (boundary.start present))

end TwoPermutationPrototype.GroupedOpening
