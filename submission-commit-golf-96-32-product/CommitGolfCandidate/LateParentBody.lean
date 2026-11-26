import CommitGolfCandidate.LateParentRun
import CommitGolfCandidate.LateLinear
import CommitGolfCandidate.LateMemoryStep

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def parentResult (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat) :=
  parentReply s d p (h (readBuffer s (nodeAddress d (2*p)) 96))

theorem parent_result_mem (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat)
    (regs : ParentRegs s d p) (inside : p < levelCount (d.val+1)) :
    (parentResult h s d p).mem = (compressAt h s (nodeAddress d (2*p)) (nodeAddress (d.val+1) p)).mem := by
  let w := h (readBuffer s (nodeAddress d (2*p)) 96)
  have same := (call_addresses s .x21 .x22 (BitVec.ofNat 12 (parentSourceOffset d (p%32)))
      (BitVec.ofNat 12 (gapOffset (p%32))) (by decide)).2
  exact (call_memory s .x21 .x22 _ _ w (by decide)).trans
    (congrArg (fun a => (writeBits s a w).mem) (same.symm.trans (parent_addresses regs inside).2))

theorem cut_op_exec (q : MachineState) (j : Nat) (hj : j < 32) :
    execInstrBr q (cutOp j) =
      (q.setHalfword (q.getReg .x22 + BitVec.ofNat 64 (gapOffset j + 30)) 0).setPC (q.pc + 4) := by
  have off : signExtend12 (BitVec.ofNat 12 (gapOffset j + 30)) = BitVec.ofNat 64 (gapOffset j + 30) :=
    cm_half_offset _ (by unfold gapOffset; omega)
  simp only [cutOp, execInstrBr, off]
  have z : (q.getReg .x0) = 0 := by rfl
  rw [z]; rfl

/-- The state after a parent site given the compression answer `w`: the call, then the
truncating store in the cut passes. -/
def storeAfter (s : MachineState) (d : Fin 24) (p : Nat) (w : Digest) :=
  let r := parentReply s d p w
  if cutPass d then execInstrBr r (cutOp (p%32)) else r

def parentStore (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat) :=
  storeAfter s d p (h (readBuffer s (nodeAddress d (2*p)) 96))

theorem reply_reg (s : MachineState) (d p : Nat) (w : Digest) (r : Reg) (a : Reg.x10 ≠ r) (b : Reg.x12 ≠ r) :
    (parentReply s d p w).getReg r = s.getReg r := call_register _ _ _ _ _ _ _ a b

theorem store_after_reg (s : MachineState) (d : Fin 24) (p : Nat) (w : Digest) (r : Reg)
    (a : Reg.x10 ≠ r) (b : Reg.x12 ≠ r) : (storeAfter s d p w).getReg r = s.getReg r := by
  unfold storeAfter
  split
  · rw [cut_op_exec _ _ (Nat.mod_lt _ (by decide)), MachineState.getReg_setPC, cm_set_halfword_reg]
    exact reply_reg s d p w r a b
  · exact reply_reg s d p w r a b

theorem store_after_pc (s : MachineState) (d : Fin 24) (p : Nat) (w : Digest) :
    (storeAfter s d p w).pc = s.pc + BitVec.ofNat 64 (4*siteWidth d) := by
  have rp : (parentReply s d p w).pc = s.pc+12 := call_pc _ _ _ _ _ _
  unfold storeAfter siteWidth
  by_cases c : cutPass d = true
  · rw [if_pos c, if_pos c, cut_op_exec _ _ (Nat.mod_lt _ (by decide))]
    change (parentReply s d p w).pc + 4 = _
    rw [rp, BitVec.add_assoc]; rfl
  · rw [if_neg c, if_neg c]; exact rp

theorem cut_address (s : MachineState) {d : Fin 24} {p : Nat} (regs : ParentRegs s d p) (w : Digest) :
    (parentReply s d p w).getReg .x22 + BitVec.ofNat 64 (gapOffset (p%32) + 30) =
      BitVec.ofNat 64 (nodeAddress (d.val+1) p + 30) := by
  rw [reply_reg s d p w .x22 (by decide) (by decide), regs.target, ←BitVec.ofNat_add]
  apply congrArg (BitVec.ofNat 64); unfold nodeAddress gapOffset; omega

theorem store_after_mem_cut (s : MachineState) {d : Fin 24} {p : Nat} (regs : ParentRegs s d p) (w : Digest)
    (c : cutPass d = true) :
    (storeAfter s d p w).mem = ((parentReply s d p w).setHalfword (BitVec.ofNat 64 (nodeAddress (d.val+1) p + 30)) 0).mem := by
  unfold storeAfter
  rw [if_pos c, cut_op_exec _ _ (Nat.mod_lt _ (by decide)), cut_address s regs w]
  rfl

theorem store_after_mem_plain (s : MachineState) (d : Fin 24) (p : Nat) (w : Digest) (c : ¬ cutPass d = true) :
    (storeAfter s d p w).mem = (parentReply s d p w).mem := by
  unfold storeAfter; rw [if_neg c]

theorem parent_store_mem (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat)
    (regs : ParentRegs s d p) (inside : p < levelCount (d.val+1)) :
    (parentStore h s d p).mem = (writeParent h s d p).mem := by
  have base := parent_result_mem h s d p regs inside
  by_cases c : cutPass d = true
  · have ch : CutHeight (d.val+1) := by simpa only [cutPass, decide_eq_true_eq] using c
    refine (store_after_mem_cut s regs (h (readBuffer s (nodeAddress d (2*p)) 96)) c).trans ?_
    unfold writeParent
    rw [if_pos ch]
    exact cm_set_halfword_mem_congr _ _ base _ _
  · have ch : ¬ CutHeight (d.val+1) := by simpa only [cutPass, decide_eq_true_eq] using c
    refine (store_after_mem_plain s d p (h (readBuffer s (nodeAddress d (2*p)) 96)) c).trans ?_
    unfold writeParent
    rw [if_neg ch]
    exact base

def parentUpdates : List Instr :=
  [.ADD .x21 .x21 .x29,.ADDI .x22 .x22 1536,.ADDI .x20 .x20 4095]

def latchOffset (d : Nat) : BitVec 13 := if cutPass d then 7668 else 7796
def latchPC (d : Nat) := parentBodyPC d + 32*siteWidth d

def advance (s : MachineState) := parentUpdates.foldl execInstrBr s
def parentBranch (d : Nat) (s : MachineState) := execInstrBr s (.BNE .x20 .x0 (latchOffset d))
def parentTick (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat) :=
  let t := parentStore h s d p
  if p%32 = 31 then parentBranch d (advance t) else t

private theorem latch_enc : ∀ d : Fin 24, 32 ≤ levelCount (d.val+1) →
    ∀ j : Fin 4, packedWord (latchPC d+j) =
      ([0x01da8ab3,0x600b0b13,0xfffa0a13,if cutPass d then 0xde0a1ae3 else 0xe60a1ae3] :
        List (BitVec 32))[j.val]?.getD 0 := by decide

private theorem latches (d : Fin 24) (large : 32 ≤ levelCount (d.val+1)) :
    (∀ j : Fin 3, AtWord (latchPC d+j) (parentUpdates[j.val]'(by exact j.isLt))) ∧
    AtWord (latchPC d+3) (.BNE .x20 .x0 (latchOffset d)) := by
  have small : ∀ x : Fin 24, 32 ≤ levelCount (x.val+1) → latchPC x+3 < 3796 := by decide
  have endSmall := small d large
  constructor
  · intro j
    apply decoded_word _ (by have := j.isLt; omega)
    have e := latch_enc d large ⟨j.val,by omega⟩
    rw [e]
    rcases j with ⟨n,hn⟩
    interval_cases n
    · exact (show decodeInstruction 0x01da8ab3 = some (.base (.ADD .x21 .x21 .x29)) by rfl)
    · exact (show decodeInstruction 0x600b0b13 = some (.base (.ADDI .x22 .x22 1536)) by rfl)
    · exact (show decodeInstruction 0xfffa0a13 = some (.base (.ADDI .x20 .x20 4095)) by rfl)
  · apply decoded_word _ endSmall
    have e := latch_enc d large 3
    change packedWord (latchPC d+3) = (if cutPass d then 0xde0a1ae3 else 0xe60a1ae3) at e
    rw [e]; unfold latchOffset
    cases cutPass d.val
    · exact (show decodeInstruction 0xe60a1ae3 = some (.base (.BNE .x20 .x0 7796)) by rfl)
    · exact (show decodeInstruction 0xde0a1ae3 = some (.base (.BNE .x20 .x0 7668)) by rfl)

theorem run_parent_latch (d : Fin 24) (large : 32 ≤ levelCount (d.val+1)) (s : MachineState)
    (pc : s.pc=pcAt (latchPC d)) (fuel : Nat) :
    execute commitImage (fuel+4) s true =
      (do let r ← execute commitImage fuel (parentBranch d (advance s)) true
          return r.charge 4 0) := by
  obtain ⟨updateCode,branchCode⟩ := latches d large
  have line := execute_linear parentUpdates (latchPC d) s (fuel+1) pc (by
    intro op member; simp only [parentUpdates,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h <;> subst op <;> intro q <;> exact ⟨rfl,rfl,rfl⟩)
    (fun i hi => updateCode ⟨i,hi⟩)
  have atbr : (advance s).pc=pcAt (latchPC d+3) := by
    change s.pc+4+4+4 = _; rw [pc]
    simp only [BitVec.add_assoc]
    change pcAt (latchPC d) + BitVec.ofNat 64 12 = _
    unfold pcAt; rw [←BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
  change execute commitImage (fuel+4) s true =
    (do let r ← execute commitImage (fuel+1) (advance s) true; pure (r.charge 3 0)) at line
  rw [line,execute_ordinary_step _ _ _ (parentBranch d (advance s)) _ _ (branchCode _ atbr) rfl]
  simp [Execution.charge, ←Nat.add_assoc, instructionCycles, parentUpdates]

/-- A parent site (three instructions, plus the truncating store in the cut passes). -/
theorem site_store_run {s : MachineState} {d : Fin 24} {p : Nat} (regs : ParentRegs s d p)
    (inside : p < levelCount (d.val+1))
    (pc : s.pc = pcAt (parentPC d (p%32))) (fuel : Nat) :
    execute commitImage (fuel+siteWidth d) s true =
      (do let w ← hash (readBuffer s (nodeAddress d (2*p)) 96)
          let out ← execute commitImage fuel (storeAfter s d p w) true
          return out.charge (7+siteWidth d) 1) := by
  by_cases c : cutPass d = true
  · have wd : siteWidth d = 4 := by simp only [siteWidth, c, if_true]
    rw [wd, show fuel+4 = (fuel+1)+3 by omega, parent_site_run regs inside pc]
    apply bind_congr; intro w
    let j : Fin 32 := ⟨p%32,by omega⟩
    have htile : j.val < tileWidth d := by unfold tileWidth; dsimp [j]; omega
    have f3 := (parent_sites d j htile).2.2.2 c
    let r := parentReply s d p w
    have rpc : r.pc = pcAt (parentPC d j+3) := by
      rw [show r.pc = s.pc+12 from call_pc _ _ _ _ _ _, pc]
      change pcAt _ + BitVec.ofNat 64 12 = _
      unfold pcAt; rw [←BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); dsimp [j]; omega
    have outEnd := parent_below_salts (d.val+1) p inside
    have hsign : signExtend12 (BitVec.ofNat 12 (gapOffset j + 30)) = BitVec.ofNat 64 (gapOffset j + 30) := by
      have hj := j.isLt
      generalize j.val = n at hj ⊢
      interval_cases n <;> rfl
    have valid : memoryArgumentsValid r (cutOp j) = true := by
      change accessValid (r.getReg .x22 + signExtend12 (BitVec.ofNat 12 (gapOffset j + 30))) 2 = true
      rw [hsign]
      change accessValid (r.getReg .x22 + BitVec.ofNat 64 (gapOffset (p%32) + 30)) 2 = true
      rw [cut_address s regs w]
      unfold rowBase at outEnd
      have al := node_aligned (d.val+1) p
      simp only [accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_ofNat]
      unfold MEMORY_BYTES
      constructor <;> omega
    have stepped : ordinaryStep r (.base (cutOp j)) = some (storeAfter s d p w) := by
      simp only [ordinaryStep, cutOp] at valid ⊢
      rw [if_pos valid]
      simp only [storeAfter, c, if_true]
      rfl
    rw [execute_ordinary_step _ _ _ _ _ _ (f3 r rpc) stepped]
    simp only [bind_assoc, pure_bind, Execution.charge, instructionCycles, cutOp]
    apply bind_congr; intro out
    rw [show 10 + (1 + out.cycles) = 7+4+out.cycles by omega, Nat.zero_add]
  · have wd : siteWidth d = 3 := by simp only [siteWidth, c]; rfl
    rw [wd, parent_site_run regs inside pc]
    apply bind_congr; intro w
    simp only [storeAfter, c]
    rfl

theorem parent_tick_run (o : Oracle) {s : MachineState} {d : Fin 24} {p : Nat} (regs : ParentRegs s d p)
    (inside : p < levelCount (d.val+1)) (pc : s.pc=pcAt (parentPC d (p%32))) (fuel : Nat) :
    o.run (execute commitImage (fuel+(siteWidth d+if p%32=31 then 4 else 0)) s true) =
      (do let (out,n) ← o.run (execute commitImage fuel (parentTick o.compression s d p) true)
          return (out.charge (7+siteWidth d+if p%32=31 then 4 else 0) 1,1+n)) := by
  let r := parentStore o.compression s d p
  by_cases last : p%32=31
  · have large : 32 ≤ levelCount (d.val+1) := by omega
    have ip : r.pc=pcAt (latchPC d) := by
      change (storeAfter _ _ _ _).pc = _
      erw [store_after_pc]
      rw [pc, last]
      unfold pcAt latchPC parentPC; rw [←BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
    simp only [if_pos last, parentTick]
    rw [show fuel+(siteWidth d+4)=(fuel+4)+siteWidth d by omega,site_store_run regs inside pc]
    unfold hash
    erw [oracle_run_public_bind o (.inl _)]
    change (do let (v,n) ← o.run (do let v ← execute commitImage (fuel+4) r true; pure (v.charge (7+siteWidth d) 1))
               pure (v,1+n)) = _
    rw [run_parent_latch d large r ip]
    simp only [bind_assoc,pure_bind,oracle_run_bind,oracle_run_pure,Nat.add_zero,
      Execution.charge,← Nat.add_assoc,Nat.zero_add]
    rfl
  · simp only [if_neg last,parentTick,Nat.add_zero]
    rw [site_store_run regs inside pc]; unfold hash
    erw [oracle_run_public_bind o (.inl _)]
    simp only [oracle_run_bind,oracle_run_pure,pure_bind,bind_assoc,Nat.add_zero]
    rfl

end CommitGolfCandidate.Late
