import CommitGolfCandidate.TwoPermutationOverlapReader
import CommitGolfCandidate.OverlapWindowRows
import CommitGolfCandidate.TwoPermutationCheckerReplay

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp OracleSpec
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 16384

private theorem add_word (a b : Nat) :
    wordAddress a + BitVec.ofNat 64 (8*b) = wordAddress (a+b) :=
  (wordAddress_add a b).symm

theorem checker_nonce_words (state : MachineState) (nonce : Nat)
    (source : state.getReg .x21 = wordAddress nonce) :
    checkerNonce state = window (memoryView state) nonce := by
  funext i
  fin_cases i <;> simp [checkerNonce, source, window, memoryView, wordAddress_add] <;> rfl

structure LeafReady (state : MachineState) (src nonce : Nat) (index : Index) where
  pc : state.pc = 0x10e4
  source : state.getReg .x10 = wordAddress src
  proofPointer : state.getReg .x21 = wordAddress nonce
  destination : state.getReg .x23 = wordAddress 1536
  tag : state.getReg .x28 = firstTag index.val
  selector : state.getReg .x5 = 0
  size : state.getReg .x11 = 200
  primitive : state.getReg .x13 = 1
  separated : src + 37 ≤ nonce
  endBound : nonce + 2 ≤ 2^33

  aboveScratch : 1561 ≤ src

theorem aligned_access (word : Nat) (bounded : word < 2 ^ 33) :
    accessValid (wordAddress word) 8 = true := by
  have width := word_address_value (word := word) (by omega)
  simp [accessValid, rangeValid, width, MEMORY_BYTES]
  omega

private theorem view_mem (s t : MachineState) (h : s.mem=t.mem) (q : Nat) :
    memoryView s q=memoryView t q := congrFun h _

theorem first_header_view {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (word : Nat) (bounded : word < 2^33) :
    memoryView (firstPrefix state 4) word = writeWord (memoryView state) (src+4) 0 word := by
  rw [view_mem _ _ (first_prefix_mem state), ready.source, offset_word src 4 32 rfl]
  exact memory_at_store (by have := ready.separated; have := ready.endBound; omega) (by omega)

theorem checker_first_input {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) :
    window (memoryView (firstPrefix state 4)) (src+4) =
      Overlap.firstInput (window (memoryView state) (src+5)) := by
  funext j
  have b := ready.endBound
  have s := ready.separated
  have h := j.isLt
  change memoryView (firstPrefix state 4) (src+4+j.val) = _
  rw [first_header_view ready _ (by omega)]
  unfold Overlap.firstInput window writeWord
  by_cases zero : j.val = 0
  · simp [zero]
  · rw [if_neg (show src+4+j.val ≠ src+4 by omega), dif_neg zero]
    exact congrArg (memoryView state) (show src+4+j.val = src+5+(j.val-1) by omega)

def firstReplyState (s : MachineState) (_src : Nat) (a : Block) : MachineState :=
  writeBits (firstPrefix s 4) (wordAddress 1536) a

def secondReplyState (s : MachineState) (src : Nat) (a b : Block) : MachineState :=
  writeBits (secondPrefix (firstReplyState s src a) 16) (wordAddress 1536) b

theorem after_first_register (s : MachineState) (src : Nat) (a : Block) (reg : Reg)
    (h10 : reg ≠ .x10) (h12 : reg ≠ .x12) :
    (firstReplyState s src a).getReg reg = s.getReg reg := by
  rw [firstReplyState,writeBits_register,first_prefix_register _ _ h10 h12]

private theorem after_first_input {s : MachineState} {src no : Nat} {idx : Index}
    (r : LeafReady s src no idx) (a : Block) : (firstReplyState s src a).getReg .x10 = wordAddress (src+4) := by
  rw [firstReplyState,writeBits_register,first_prefix_input,r.source,offset_word src 4 32 rfl]

private theorem after_first_output (s : MachineState) (src : Nat) (a : Block) :
    (firstReplyState s src a).getReg .x12 = s.getReg .x23 := by
  rw [firstReplyState,writeBits_register,first_prefix_output]

theorem after_first_pc {s : MachineState} {src no : Nat} {idx : Index} (r : LeafReady s src no idx) (a : Block) :
    (firstReplyState s src a).pc=4996 := by
  change (firstPrefix s 4).pc+4=_
  rw [first_prefix_pc s r.pc]
  rfl

private theorem reply_view {s : MachineState} {src no : Nat} {idx : Index}
    (r : LeafReady s src no idx) (a : Block) (q : Nat) (hq : q<2^33) :
    memoryView (firstReplyState s src a) q =
      if h : 1536 ≤ q ∧ q < 1561 then replyWords a ⟨q-1536,by omega⟩ else
        writeWord (memoryView s) (src+4) 0 q := by
  change BitVec 1600 at a
  change memoryView (writeBits (firstPrefix s 4) (wordAddress 1536) a) q = _
  rw [permutation_write_memory _ 1536 q a (by decide) hq]
  unfold writeWindow
  split <;> simp_all [first_header_view r]

private theorem wrapper_view {s : MachineState} {src no : Nat} {idx : Index}
    (r : LeafReady s src no idx) (a : Block) (q : Nat) (hq : q<2^33) :
    let prev := firstReplyState s src a
    memoryView (secondPrefix prev 16) q =
      if src+12≤q ∧ q<src+19 then headerCell (memoryView prev) 1536 no (secondTag idx.val) (q-(src+12))
      else memoryView prev q := by
  dsimp only
  let prev := firstReplyState s src a
  have keep (reg : Reg) (h10 : reg ≠ .x10 := by decide) (h12 : reg ≠ .x12 := by decide) :
      prev.getReg reg = s.getReg reg := after_first_register s src a reg h10 h12
  have tag : prev.getReg .x28+96#64 = secondTag idx.val := by rw [keep .x28,r.tag]; rfl
  change memoryView (secondPrefix prev 16) q = _
  rw [view_mem _ _ (second_prefix_mem prev),show prev.getReg .x10 = wordAddress (src+4) from after_first_input r a,
    keep .x23,r.destination,keep .x21,r.proofPointer,tag,
    copy_header_view _ (src+4) 1536 no _ (by have := r.aboveScratch; omega)
      (by have := r.separated; omega) r.endBound 6 (by decide) q hq]

theorem checker_second_input {s : MachineState} {src no : Nat} {idx : Index} (r : LeafReady s src no idx)
    (a : Block) :
    window (memoryView (secondPrefix (firstReplyState s src a) 16)) (src+12) =
      Overlap.secondInput idx.val (checkerNonce s) (replyWords a) (window (memoryView s) (src+5)) := by
  change BitVec 1600 at a
  funext i
  have hi := i.isLt
  have limit := r.endBound
  have gap := r.separated
  have lo := r.aboveScratch
  change memoryView (secondPrefix (firstReplyState s src a) 16) (src+12+i.val) = _
  rw [wrapper_view r a _ (by omega)]
  simp only [Overlap.secondInput,checker_nonce_words s no r.proofPointer,window,headerCell]
  by_cases z : i.val=0
  · simp [z]
  · by_cases link : i.val<5
    · simp only [if_pos (show src+12≤src+12+i.val ∧ src+12+i.val<src+19 by omega),
        Nat.add_sub_cancel_left,if_neg z,if_pos link,dif_neg z,dif_pos link,Fin.val_mk]
      rw [reply_view r a _ (by omega), dif_pos (by omega)]
      apply congrArg (replyWords a)
      apply Fin.ext
      change 1536+20+i.val-1536 = i.val+20
      omega
    · by_cases salt : i.val<7
      · simp only [if_pos (show src+12≤src+12+i.val ∧ src+12+i.val<src+19 by omega),
          Nat.add_sub_cancel_left,if_neg z,if_neg link,if_pos salt,dif_neg z,dif_neg link,dif_pos salt,Fin.val_mk]
        rw [reply_view r a _ (by omega),dif_neg (by omega),writeWord,if_neg (by omega)]
      · simp only [if_neg (show ¬(src+12≤src+12+i.val ∧ src+12+i.val<src+19) by omega),
          if_neg z,if_neg link,if_neg salt,dif_neg z,dif_neg link,dif_neg salt,Fin.val_mk]
        rw [reply_view r a _ (by omega),dif_neg (by omega),writeWord,if_neg (by omega)]
        exact congrArg (memoryView s) (show src+12+i.val = src+5+(i.val+7) by omega)

attribute [local irreducible] execute readBuffer writeBits packBuffer

private theorem first_call_run {s : MachineState} {src no : Nat} {idx : Index}
    (r : LeafReady s src no idx) (fuel : Nat) :
    execute checkerImage (5+fuel) s false =
      (do let a ← World.query (.inr (.inr (.inl (packBuffer
              (Overlap.firstInput (window (memoryView s) (src+5)))))))
          let rest ← execute checkerImage fuel (firstReplyState s src a) false
          return rest.charge 12 1) := by
  have gap := r.separated
  have bound := r.endBound
  have input : (firstPrefix s 4).getReg .x10 = wordAddress (src+4) := by
    rw [first_prefix_input, r.source, offset_word src 4 32 rfl]
  have call := execute_permutation_call checkerImage fuel (firstPrefix s 4) false (src+4) 1536
    (by omega) (by decide) input ((first_prefix_output s).trans r.destination)
    ((first_prefix_register s .x5 (by decide) (by decide)).trans r.selector)
    ((first_prefix_register s .x11 (by decide) (by decide)).trans r.size)
    ((first_prefix_register s .x13 (by decide) (by decide)).trans r.primitive)
    (checker_first_ecall _ (first_prefix_pc s r.pc))
  rw [checker_first_input r] at call
  have valid : accessValid (s.getReg .x10 + 32#64) 8 = true := by
    rw [r.source,offset_word src 4 32 rfl]
    exact aligned_access _ (by omega)
  rw [show 5+fuel=4+(fuel+1) by omega,execute_first_prefix s r.pc _ valid,call]
  simp [firstReplyState,Execution.charge,bind_assoc,← Nat.add_assoc] <;> rfl

private theorem second_call_run {s : MachineState} {src no : Nat} {idx : Index}
    (r : LeafReady s src no idx) (a : Block) (fuel : Nat) :
    execute checkerImage (17+fuel) (firstReplyState s src a) false =
      (do let b ← World.query (.inr (.inr (.inl (packBuffer (Overlap.secondInput idx.val
              (checkerNonce s) (replyWords a) (window (memoryView s) (src+5)))))))
          let rest ← execute checkerImage fuel (secondReplyState s src a b) false
          return rest.charge 24 1) := by
  let prev := firstReplyState s src a
  have eq (reg : Reg) (h : reg ≠ .x10 := by decide) (j : reg ≠ .x12 := by decide) :
      prev.getReg reg = s.getReg reg := after_first_register s src a reg h j
  have x : prev.getReg .x10 = wordAddress (src+4) := after_first_input r a
  have input : (secondPrefix prev 16).getReg .x10=wordAddress (src+12) := by
    rw [second_prefix_input,x,offset_word (src+4) 8 64 rfl]
  have output : (secondPrefix prev 16).getReg .x12=wordAddress 1536 :=
    (second_prefix_register prev .x12 (by decide) (by decide)).trans
      ((after_first_output s src a).trans r.destination)
  have gap := r.separated
  have bound := r.endBound
  have call := execute_permutation_call checkerImage fuel (secondPrefix prev 16) false (src+12) 1536
    (by omega) (by decide) input output
    ((second_prefix_register prev .x5 (by decide) (by decide)).trans ((eq .x5).trans r.selector))
    ((second_prefix_register prev .x11 (by decide) (by decide)).trans ((eq .x11).trans r.size))
    ((second_prefix_register prev .x13 (by decide) (by decide)).trans ((eq .x13).trans r.primitive))
    (checker_second_ecall _ (second_prefix_pc prev (after_first_pc r a)))
  rw [show prev = firstReplyState s src a from rfl,checker_second_input r] at call
  have dst (j : Fin 7) : accessValid (prev.getReg .x10+BitVec.ofNat 64 (64+8*j.val)) 8=true := by
    rw [x,offset_word (src+4) (8+j.val) _ (by omega)]
    exact aligned_access _ (by have := j.isLt; omega)
  have sc (j : Fin 4) : accessValid (prev.getReg .x23+BitVec.ofNat 64 (168+8*j.val)) 8=true := by
    rw [eq .x23,r.destination,offset_word 1536 (21+j.val) _ (by omega)]
    exact aligned_access _ (by have := j.isLt; omega)
  have nonce (j : Fin 2) : accessValid (prev.getReg .x21+BitVec.ofNat 64 (8*j.val)) 8=true := by
    rw [eq .x21,r.proofPointer,add_word]
    exact aligned_access _ (by have := j.isLt; omega)
  rw [show 17+fuel=16+(fuel+1) by omega,execute_second_prefix prev (after_first_pc r a) _ dst sc nonce,call]
  simp [secondReplyState,Execution.charge,bind_assoc,← Nat.add_assoc] <;> rfl

def leafQueries (s : MachineState) (src : Nat) (idx : Index) : OracleComp World MachineState := do
  let m := window (memoryView s) (src+5)
  let a ← World.query (.inr (.inr (.inl (packBuffer (Overlap.firstInput m)))))
  let b ← World.query (.inr (.inr (.inl (packBuffer (Overlap.secondInput idx.val (checkerNonce s) (replyWords a) m)))))
  return secondReplyState s src a b

theorem execute_checker_leaf {s : MachineState} {src no : Nat} {idx : Index}
    (r : LeafReady s src no idx) (fuel : Nat) :
    execute checkerImage (22+fuel) s false =
      (do let intermediate ← leafQueries s src idx
          let result ← execute checkerImage fuel intermediate false
          return result.charge 36 2) := by
  rw [show 22+fuel=5+(17+fuel) by omega,first_call_run r]
  simp only [leafQueries,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a _
  change Block at a
  rw [second_call_run r a fuel]
  simp [Execution.charge,bind_assoc,← Nat.add_assoc] <;> rfl

theorem checker_leaf_rows (oracle : Oracle) (s : MachineState) (src : Nat) (idx : Index) :
    let m := window (memoryView s) (src+5)
    let a := Overlap.firstRow oracle.permutation m
    let b := Overlap.secondRow oracle.permutation idx (checkerNonce s) m a.2
    checkEvaluation oracle (recordRows (leafQueries s src idx)) =
      ((secondReplyState s src a.2 b.2,[.permutation a.1 a.2,.permutation b.1 b.2]),2) := by
  simp only [leafQueries,Overlap.firstRow,Overlap.secondRow,record_rows_query,check_evaluation_public_bind,
    check_evaluation_map,record_rows_pure,check_evaluation_pure]
  rfl

theorem checker_leaf_digest (s : MachineState) (src : Nat) (a b : Block) :
    readBuffer (secondReplyState s src a b) 12288 32 = outputDigest b := by
  unfold secondReplyState
  simpa only [wordAddress,Nat.add_zero,Nat.mul_zero,outputDigest] using
    write_bits_digest (secondPrefix (firstReplyState s src a) 16) 12288 0 b (by decide) (by decide)

theorem checker_leaf_finished_pc {s : MachineState} {src no : Nat} {idx : Index}
    (r : LeafReady s src no idx) (a b : Block) : (secondReplyState s src a b).pc=0x111c := by
  unfold secondReplyState writeBits
  change (secondPrefix (firstReplyState s src a) 16).pc+4=_
  rw [second_prefix_pc _ (after_first_pc r a)]
  rfl

theorem checker_leaf_preserved_register (s : MachineState) (src : Nat) (a b : Block)
    (reg : Reg) (h10 : reg ≠ .x10) (h12 : reg ≠ .x12) (h31 : reg ≠ .x31) :
    (secondReplyState s src a b).getReg reg=s.getReg reg := by
  rw [secondReplyState,writeBits_register,second_prefix_register _ _ h10 h31,
    after_first_register _ _ _ _ h10 h12]

theorem checker_leaf_frame {s : MachineState} {src no : Nat} {idx : Index}
    (r : LeafReady s src no idx) (a b : Block) (q : Nat)
    (bound : q<2^33) (outside : q<src ∨ src+25≤q) (scratch : q<1536 ∨ 1561≤q) :
    memoryView (secondReplyState s src a b) q = memoryView s q := by
  change BitVec 1600 at a b
  change memoryView (writeBits (secondPrefix (firstReplyState s src a) 16) (wordAddress 1536) b) q = _
  rw [permutation_write_memory _ 1536 q b (by decide) bound,writeWindow,dif_neg (by omega),
    wrapper_view r a q bound, if_neg (by omega),reply_view r a q bound,dif_neg (by omega),
    writeWord,if_neg (by omega)]

end TwoPermutationPrototype.Checker
