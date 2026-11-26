import CommitGolfCandidate.ReconstructedCapPath
import CommitGolfCandidate.ReconstructedCapSlots

namespace CommitGolfCandidate.Reconstruction.CapScanWrite
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 HonestCapStages
open CapPath (Line listed follows final clear)
open HonestCapTables (addrSlot scratch w)
open CommitBlocks (addr)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] ArtifactEncoding.decode

def branch : Line := (1475,.BEQ .x14 .x15 8152)
def nextPair : List Line := [(1465,.ADDIW .x21 .x21 2),(1466,.ADDI .x16 .x16 2),
  (1467,.ADDI .x23 .x23 2),(1468,.ADDI .x24 .x24 1)]
def writePath : List Line := [(1476,.ADD .x14 .x21 .x14),(1477,.SLLI .x15 .x20 32),
  (1478,.ADDIW .x20 .x20 1),(1479,.SRLI .x15 .x15 30),(1480,.ADD .x15 .x9 .x15),
  (1481,.SW .x15 .x14 0),(1482,.JAL .x0 2097084)]
def tail (different : Bool) := if different then writePath++nextPair else nextPair

private theorem table (b : Bool) : listed (branch::tail b) := by
  cases b <;> simp only [tail,Bool.false_eq_true,ite_false,ite_true,writePath,nextPair,branch,List.cons_append,List.nil_append,listed]
  all_goals repeat' apply And.intro
  all_goals first | rfl | exact True.intro | decide

private theorem noCuts (b : Bool) : clear (tail b) := by
  cases b <;> simp only [tail,Bool.false_eq_true,ite_false,ite_true,writePath,nextPair,List.cons_append,List.nil_append,clear]
  all_goals decide +kernel

private theorem pc_set (s : MachineState) (p : Word) : (s.setPC p).pc=p := rfl

private theorem equal_pc (s : MachineState) (pc : s.pc=addr 1475) (same : s.getReg .x14=s.getReg .x15) :
    follows s (branch::tail false) 1469 := by
  simp only [tail,Bool.false_eq_true,ite_false,branch,nextPair,follows,execInstrBr,same,beq_self_eq_true,ite_true]
  simp only [pc_set,pc]
  decide

private theorem different_pc (s : MachineState) (pc : s.pc=addr 1475) (different : s.getReg .x14≠s.getReg .x15) :
    follows s (branch::tail true) 1469 := by
  simp only [tail,ite_true,branch,writePath,nextPair,List.cons_append,List.nil_append,follows,execInstrBr,
    beq_eq_false_iff_ne.mpr different,Bool.false_eq_true,ite_false]
  simp only [pc_set,pc]
  decide

private theorem branch_mem (s : MachineState) (condition : Bool) (a b : Word) :
    (if condition then s.setPC a else s.setPC b).mem=s.mem := by cases condition <;> rfl

private theorem equal_mem (s : MachineState) :
    (final s (branch::tail false)).mem=s.mem := by
  change (execInstrBr s (.BEQ .x14 .x15 8152)).mem=s.mem
  change (if s.getReg .x14 == s.getReg .x15 then s.setPC (s.pc+signExtend13 8152) else s.setPC (s.pc+4)).mem=s.mem
  exact branch_mem s _ _ _

private theorem different_mem (s : MachineState) (different : s.getReg .x14≠s.getReg .x15) :
    (final s (branch::tail true)).mem =
      (s.setWord32 (s.getReg .x9+((s.getReg .x20 <<< (32:Nat)) >>> (30:Nat)))
        ((s.getReg .x21+s.getReg .x14).truncate 32)).mem := by
  simp only [tail,ite_true,branch,writePath,nextPair,List.cons_append,List.nil_append,final,execInstrBr,
    beq_eq_false_iff_ne.mpr different,Bool.false_eq_true,ite_false]
  change (s.setWord32 ((s.getReg .x9+((s.getReg .x20 <<< (32:Nat)) >>> (30:Nat)))+signExtend12 0)
    ((s.getReg .x21+s.getReg .x14).truncate 32)).mem=_
  rw [show signExtend12 0=0#64 from rfl,BitVec.add_zero]

private theorem index_address (p : Fin 257) : w scratch+((w p.val <<< (32:Nat)) >>> (30:Nat))=addrSlot p.val :=
  (by decide +kernel : ∀ j : Fin 257, w scratch+((w j.val <<< (32:Nat)) >>> (30:Nat))=addrSlot j.val) p

theorem effects (s t : MachineState) (coins : Bool) (pc : s.pc=addr 1475) (path : HonestCapState.Path coins s t)
    (p : Fin 257) (k : Nat) (l r : Bool) (lp : s.getReg .x14=w l.toNat) (rp : s.getReg .x15=w r.toNat)
    (idbase : s.getReg .x21=w k) (scratchPtr : s.getReg .x9=w scratch) (pending : s.getReg .x20=w p.val) :
    t.mem = if l=r then s.mem else (s.setWord32 (addrSlot p.val) (BitVec.ofNat 32 (k+l.toNat))).mem := by
  by_cases same : l=r
  · have equal : s.getReg .x14=s.getReg .x15 := lp.trans ((congrArg (fun v : Bool => w v.toNat) same).trans rp.symm)
    have done := CapPath.endpoint (table false) (noCuts false) (by decide : stops (addr 1469)=true) (equal_pc s pc equal) path
    rw [ite_eq_left same,done,equal_mem s]
  · have different : s.getReg .x14≠s.getReg .x15 := by
      rw [lp,rp]
      cases l <;> cases r <;> first | decide | contradiction
    have done := CapPath.endpoint (table true) (noCuts true) (by decide : stops (addr 1469)=true) (different_pc s pc different) path
    rw [ite_eq_right same,done,different_mem s different,idbase,lp,scratchPtr,pending,index_address,←BitVec.ofNat_add]
    have shrink (n : Nat) : (w n).truncate 32=BitVec.ofNat 32 n := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.truncate,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
      omega
    rw [shrink]

end CommitGolfCandidate.Reconstruction.CapScanWrite
