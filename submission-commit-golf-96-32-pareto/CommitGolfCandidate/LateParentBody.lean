import CommitGolfCandidate.LateParentRun
import CommitGolfCandidate.LateMaskedSite
import CommitGolfCandidate.LateLinear
import CommitGolfCandidate.LateMemoryStep

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def parentResult (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat) :=
  laneReply s d p (h (readBuffer s (rowAddress d p) 96))

private theorem pcFrame (u : MachineState) (v : Word) : (u.setPC v).mem=u.mem := rfl
attribute [local irreducible] writeBits callState
private theorem savedReply (s : MachineState) (d : Fin 24) (p : Nat) (w : Digest) (regs : ParentRegs s d p) :
    (laneReply s d p w).mem=(store s (nodeAddress (d.val+1) p) (retain (23-d.val) w)).mem := by
  let a:=BitVec.ofNat 12 (96*(p%16))
  let b:=BitVec.ofNat 12 (gapOffset (p%16))
  let z:=retain (23-d.val) w
  have ptr:= (call_addresses s .x21 .x22 a b (by decide)).2
  have target : s.getReg .x22+signExtend12 b=BitVec.ofNat 64 (nodeAddress (d.val+1) p) :=
    ptr.symm.trans (parent_addresses regs).2
  unfold laneReply;rw [pcFrame];unfold parentReply store
  exact (call_memory s .x21 .x22 a b z (by decide)).trans (congrArg (fun v=> (writeBits s v z).mem) target)

theorem parent_result_mem (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat)
    (regs : ParentRegs s d p) :
    (parentResult h s d p).mem = (writeParent (layerHash h d) s d p).mem :=
by
  have e:=savedReply s d p (h (readBuffer s (rowAddress d p) 96)) regs
  unfold retain at e
  rw [show 24-(23-d.val)=d.val+1 by have:=d.isLt;omega] at e
  exact e

def parentUpdates : List Instr :=
  [.ADDI .x21 .x21 1536,.ADDI .x22 .x22 768,.ADDI .x20 .x20 4095]

def advance (s : MachineState) := parentUpdates.foldl execInstrBr s
def parentBranch (d : Fin 24) (s : MachineState) := execInstrBr s (.BNE .x20 .x0 (backImm d))
def parentTick (h : Compression) (s : MachineState) (d : Fin 24) (p : Nat) :=
  let t := parentResult h s d p
  if p%16 = 15 then parentBranch d (advance t) else t

private theorem latch_enc : ∀ d : Fin 24, 16 ≤ levelCount (d.val+1) →
    ∀ j : Fin 4, packedWord (parentBodyPC d+laneWidth d*16+j) =
      ([0x600a8a93,0x300b0b13,0xfffa0a13,(if maskedPhase d then 0xee0a1ae3 else 0xf20a1ae3)] : List (BitVec 32))[j.val]?.getD 0 := by decide

private theorem latches (d : Fin 24) (large : 16 ≤ levelCount (d.val+1)) :
    (∀ j : Fin 3, AtWord (parentBodyPC d+laneWidth d*16+j) (parentUpdates[j.val]'(by exact j.isLt))) ∧
    AtWord (parentBodyPC d+laneWidth d*16+3) (.BNE .x20 .x0 (backImm d)) := by
  have small : ∀ x : Fin 24, 16 ≤ levelCount (x.val+1) → parentBodyPC x+laneWidth x*16+3 < 3262 := by decide
  have endSmall := small d large
  constructor
  · intro j
    apply decoded_word _ (by have := j.isLt; omega)
    have e := latch_enc d large ⟨j.val,by omega⟩
    rw [e]
    rcases j with ⟨n,hn⟩
    interval_cases n
    · exact (show decodeInstruction 0x600a8a93 = some (.base (.ADDI .x21 .x21 1536)) by rfl)
    · exact (show decodeInstruction 0x300b0b13 = some (.base (.ADDI .x22 .x22 768)) by rfl)
    · exact (show decodeInstruction 0xfffa0a13 = some (.base (.ADDI .x20 .x20 4095)) by rfl)
  · apply decoded_word _ endSmall
    have e := latch_enc d large 3
    change packedWord (parentBodyPC d+laneWidth d*16+3) = (if maskedPhase d then 0xee0a1ae3 else 0xf20a1ae3) at e
    rw [e];unfold backImm;split <;> rfl

theorem run_parent_latch (d : Fin 24) (large : 16 ≤ levelCount (d.val+1)) (s : MachineState)
    (pc : s.pc=pcAt (parentBodyPC d+laneWidth d*16)) (fuel : Nat) :
    execute commitImage (fuel+4) s true =
      (do let r ← execute commitImage fuel (parentBranch d (advance s)) true
          return r.charge 4 0) := by
  obtain ⟨updateCode,branchCode⟩ := latches d large
  have line := execute_linear parentUpdates (parentBodyPC d+laneWidth d*16) s (fuel+1) pc (by
    intro op member; simp only [parentUpdates,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h <;> subst op <;> intro q <;> exact ⟨rfl,rfl,rfl⟩)
    (fun i hi => updateCode ⟨i,hi⟩)
  have atbr : (advance s).pc=pcAt (parentBodyPC d+laneWidth d*16+3) := by
    change s.pc+4+4+4 = _; rw [pc]
    simp only [BitVec.add_assoc]
    change pcAt (parentBodyPC d+laneWidth d*16) + BitVec.ofNat 64 12 = _
    unfold pcAt; rw [←BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
  change execute commitImage (fuel+4) s true =
    (do let r ← execute commitImage (fuel+1) (advance s) true; pure (r.charge 3 0)) at line
  rw [line,execute_ordinary_step _ _ _ (parentBranch d (advance s)) _ _ (branchCode _ atbr) rfl]
  simp [Execution.charge, ←Nat.add_assoc, instructionCycles, parentUpdates]

theorem parent_tick_run (o : Oracle) {s : MachineState} {d : Fin 24} {p : Nat} (regs : ParentRegs s d p)
    (inside : p < levelCount (d.val+1)) (pc : s.pc=pcAt (lanePC d p)) (fuel : Nat) :
    o.run (execute commitImage (fuel+(laneWidth d+if p%16=15 then 4 else 0)) s true) =
      (do let (out,n) ← o.run (execute commitImage fuel (parentTick o.compression s d p) true)
          return (out.charge ((10+laneExtra d)+if p%16=15 then 4 else 0) 1,1+n)) := by
  let r := parentResult o.compression s d p
  by_cases last : p%16=15
  · have large : 16 ≤ levelCount (d.val+1) := by omega
    have nontail : tailBank d.val p=false := by unfold tailBank;apply decide_eq_false;omega
    have ip : r.pc=pcAt (parentBodyPC d+laneWidth d*16) := by
      rw [show r.pc=s.pc+BitVec.ofNat 64 (4*laneWidth d) from laneReply_pc ..,pc,lanePC,nontail,bankPC]
      simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
      rw [last,pcAt,←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);unfold parentPC;omega
    simp only [if_pos last, parentTick]
    rw [show fuel+(laneWidth d+4)=(fuel+4)+laneWidth d by omega,lane_site_run regs inside pc]
    unfold hash
    erw [oracle_run_public_bind o (.inl _)]
    change (do let (v,n) ← o.run (do let v ← execute commitImage (fuel+4) r true; pure (v.charge (10+laneExtra d) 1))
               pure (v,1+n)) = _
    rw [run_parent_latch d large r ip]
    simp only [bind_assoc,pure_bind,oracle_run_bind,oracle_run_pure,Nat.add_zero,
      Execution.charge,← Nat.add_assoc,Nat.zero_add]
    rfl
  · simp only [if_neg last,parentTick,Nat.add_zero]
    rw [lane_site_run regs inside pc]; unfold hash
    erw [oracle_run_public_bind o (.inl _)]
    simp only [oracle_run_bind,oracle_run_pure,pure_bind,bind_assoc,Nat.add_zero]
    rfl

end CommitGolfCandidate.Late
