import CommitGolfCandidate.S5ParentBuffers
import CommitGolfCandidate.S5Root
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000

def rootOps : List Instr := [.LUI .x6 262144,.ADDI .x6 .x6 1088,.ADD .x7 .x18 .x6]
def rootPrepared (s : MachineState) :=rootOps.foldl execInstrBr s
def exited (s : MachineState) :=haltState (rootCopy (rootPrepared s))
private theorem root_table : ∀ i : Fin 3,decoded (18478+i.val)=some (.base (rootOps.get ⟨i.val,i.isLt⟩)) := by decide +kernel

theorem root_registers (s : MachineState) (base : s.getReg .x18=4294975488) (root : s.getReg .x9=4294971392) :
    (rootPrepared s).getReg .x7=BitVec.ofNat 64 rootSource ∧ (rootPrepared s).getReg .x9=BitVec.ofNat 64 rootDestination := by
  refine ⟨?_,root⟩
  change s.getReg .x18+(((262144 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64 + signExtend12 1088)=_
  rw [base];decide

theorem root_exit (s : MachineState) (pc : s.pc=pcAt 18478) (cm : Common s) (fuel : Nat) :
    execute commitImage (fuel+14) s true=pure ⟨.success,exited s,14,0⟩ := by
  have run:=execute_linear .commit true rootOps 18478 s (fuel+11) pc
    (fun op m=>header_straight op (List.all_eq_true.mp (by decide : rootOps.all setupOp) op m))
    (fun i hi=>decoded_site (by change i<3 at hi;omega) (root_table ⟨i,hi⟩))
  have ip : (rootPrepared s).pc=pcAt 18481 := by change s.pc+4+4+4=_;rw [pc];rfl
  obtain ⟨from_,to_⟩:=root_registers s cm.base cm.root
  rw [show fuel+14=(fuel+11)+rootOps.length by change fuel+14=fuel+11+3;omega,run]
  change (do let r ← execute commitImage (fuel+11) (rootPrepared s) true; pure (r.charge 3 0)) = _
  rw [commit_exit _ ip from_ to_,pure_bind];rfl

theorem exited_root (s : MachineState) (cm : Common s) :
    readBuffer (exited s) rootDestination 32=readBuffer s rootSource 32 := by
  obtain ⟨from_,to_⟩:=root_registers s cm.base cm.root
  exact (root_copy_contents _ from_ to_).trans (read_congr_mem (rootPrepared s) s _ _ rfl)

theorem exited_retains (s : MachineState) (cm : Common s) (a : Nat) (low : tdBase≤a)
    (small : a+32≤MEMORY_BYTES) (aligned : a%8=0) : readBuffer (exited s) a 32=readBuffer s a 32 := by
  obtain ⟨src,dst⟩:=root_registers s cm.base cm.root
  apply (read_digest_eq_iff _ _ _ _ aligned aligned).mpr
  intro j hj
  have bound : a+8*j<2^64 := by change _≤2^36 at small;omega
  exact (root_copy_away (rootPrepared s) src dst (BitVec.ofNat 64 (a+8*j))
    (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound];unfold rootDestination tdBase at *;omega)).trans
      (show (rootPrepared s).getMem (BitVec.ofNat 64 (a+8*j))=s.getMem _ from rfl)
end CommitGolfCandidate.S5Machine
