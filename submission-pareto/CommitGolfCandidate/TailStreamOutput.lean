import CommitGolfCandidate.TailStreamRun

namespace TwoPermutationPrototype.PackedOpening.TailStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
set_option maxRecDepth 8192
attribute [local simp] Opening.getReg_setReg set_byte_read

def emitPath (m : Nat) : List Nat := (List.range 8).map (fun i => 38+8*m+i)

def adjacentByte (a b : Byte) (m : Nat) : Byte :=
  BitVec.ofNat 8 (a.toNat%128/2^m+(b.toNat%128)*2^(7-m))

@[simp] theorem se12_127 : signExtend12 127#12=127#64 := by decide

variable {image : Image} [CodeImage image]

set_option maxHeartbeats 2400000 in
theorem emit_one (s : MachineState) (h d m : Nat) (hm : m<7)
    (pc : s.pc=pcOf (38+8*m))
    (x28 : s.getReg .x28=BitVec.ofNat 64 h) (x26 : s.getReg .x26=BitVec.ofNat 64 d)
    (hfit : h+8≤2^36) (dfit : d+7≤2^36) :
    Runs image s (run s (emitPath m)) 8 8 ∧
      (run s (emitPath m)).pc=pcOf (46+8*m) ∧
      (∀ a, (run s (emitPath m)).getByte a=
        if a=BitVec.ofNat 64 (d+m) then adjacentByte
          (s.getByte (BitVec.ofNat 64 (h+m)))
          (s.getByte (BitVec.ofNat 64 (h+(m+1)))) m else s.getByte a) := by
  have ok : PathOK s (emitPath m) := by
    interval_cases m <;>
      simp (disch := omega) [PathOK,emitPath,List.range_succ,execInstrBr,pc,x28,x26,
        ordinaryInstr,memoryArgumentsValid,memAccess,w_add]
    all_goals repeat' constructor
    all_goals apply accessValid_of <;> rw [toNat_w _ (by omega)] <;> omega
  refine ⟨(runs_path (image := image) _ s ok).cast ?_ ?_,?_,?_⟩
  · simp [emitPath]
  · interval_cases m <;> decide
  · interval_cases m <;> simp [run,emitPath,List.range_succ,execInstrBr,pc]
  · intro a
    have packed := packed_word
      ((s.getByte (BitVec.ofNat 64 (h+m))).toNat%128)
      ((s.getByte (BitVec.ofNat 64 (h+(m+1)))).toNat%128) m
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hm
    have value := congrArg
      (fun v : Byte => if a=BitVec.ofNat 64 (d+m) then v else s.getByte a) packed
    interval_cases m <;>
      simpa [run,emitPath,List.range_succ,execInstrBr,x28,x26,w_add,byte_and127,adjacentByte]
        using value

end TwoPermutationPrototype.PackedOpening.TailStream
