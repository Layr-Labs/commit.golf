import CommitGolfCandidate.S4Catalog
import CommitGolfCandidate.S4Stores
import CommitGolfCandidate.R4bBytes
set_option Elab.async false
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.S4
open S4.Machine (W Safe Runs Matches Code byte Wrote)
open Late (pcAt)

def clocks : List Instr → Nat
  | [] => 0
  | i::xs => instructionCycles (.base i)+clocks xs

inductive Straight : MachineState → List Instr → MachineState → Prop where
  | nil (s) : Straight s [] s
  | cons {s v t : MachineState} {i : Instr} {ops : List Instr}
      (step : ordinaryStep s (.base i)=some v) (pc : v.pc=s.pc+4)
      (tail : Straight v ops t) : Straight s (i::ops) t

theorem Straight.one {s t : MachineState} {i : Instr}
    (step : ordinaryStep s (.base i)=some t) (pc : t.pc=s.pc+4) : Straight s [i] t :=
  .cons step pc (.nil t)
theorem Straight.append {s u t : MachineState} {a b : List Instr}
    (h : Straight s a u) (e : Straight u b t) : Straight s (a++b) t := by
  induction h with
  | nil=>exact e
  | cons step pc _ ih=>exact .cons step pc (ih e)

theorem Straight.exec {s t : MachineState} {xs : List Instr} (run : Straight s xs t)
    (p : Nat) (pc : s.pc=pcAt p) (lim : p+xs.length≤Code.opening.count) (sites : Matches .opening p xs) :
    Runs .opening s t xs.length (clocks xs) ∧ t.pc=pcAt (p+xs.length) := by
  induction run generalizing p with
  | nil s=>exact ⟨Runs.refl .opening _,by simpa using pc⟩
  | @cons s v t i ops step inc _ ih=>
    have n:=Machine.one (c:=.opening) (by simp only [List.length_cons] at lim;omega : p<Code.opening.count) pc i (sites 0 (by simp)) step
    have ip : v.pc=pcAt (p+1):=inc.trans ((congrArg (·+4) pc).trans (Late.pc_succ p).symm)
    have suffix : Matches .opening (p+1) ops := by
      intro j h
      rw [show p+1+j=p+(j+1) by omega]
      have hh : j+1<(i::ops).length:=by simpa using h
      exact (sites (j+1) hh).trans (congrArg (fun x=>some (Instruction.base x)) (show (i::ops)[j+1]=ops[j] from rfl))
    obtain ⟨e,last⟩:=ih (p+1) ip (by simp only [List.length_cons] at lim;omega) suffix
    exact ⟨by simpa only [clocks,List.length_cons,show ops.length+1=1+ops.length by omega] using n.trans e,
      last.trans (congrArg pcAt (by simp only [List.length_cons];omega))⟩

abbrev imm12 (n : Nat) := BitVec.ofNat 12 n
abbrev imm6 (n : Nat) := BitVec.ofNat 6 n
set_option maxRecDepth 8000 in
theorem sextSmall : ∀ n : Fin 2048,signExtend12 (imm12 n.val)=W n.val := by decide +kernel
theorem smallAddr (s : MachineState) (r : Reg) (a k : Nat) (h : s.getReg r=W a) (small : k<2048) :
    s.getReg r+signExtend12 (imm12 k)=W (a+k) := by
  rw [h,sextSmall ⟨k,small⟩];exact (BitVec.ofNat_add ..).symm

theorem justLoad (s : MachineState) (d r : Reg) (k a : Nat)
    (addr : s.getReg r+signExtend12 (imm12 k)=W a) (safe : Safe a 8) :
    Straight s [.LD d r (imm12 k)] ((s.setReg d (s.getMem (W a))).setPC (s.pc+4)) := by
  apply Straight.one _ rfl
  have ok : memoryArgumentsValid s (.LD d r (imm12 k))=true:=by
    change accessValid _ 8=true;rw [addr];exact safe.valid
  simp only [ordinaryStep,if_pos ok,execInstrBr,addr]

theorem writeWord (s : MachineState) (d r : Reg) (k a : Nat)
    (addr : s.getReg d+signExtend12 (imm12 k)=W a) (safe : Safe a 8) :
    let u:=(s.setMem (W a) (s.getReg r)).setPC (s.pc+4)
    Straight s [.SD d r (imm12 k)] u ∧ Wrote s u a 8 (extractByte (s.getReg r)) := by
  dsimp only
  constructor
  · apply Straight.one _ rfl
    have ok : memoryArgumentsValid s (.SD d r (imm12 k))=true:=by
      change accessValid _ 8=true;rw [addr];exact safe.valid
    simp only [ordinaryStep,if_pos ok,execInstrBr,addr]
  · intro q bq;by_cases inside:a≤q ∧ q<a+8
    · rw [if_pos inside,Machine.byteWord,show 8*(q/8)=a by have:=safe.2;omega]
      change extractByte ((s.setMem _ _).getMem _) _=_
      rw [MachineState.getMem_setMem_eq,show q%8=q-a by have:=safe.2;omega]
    · have ne : W (8*(q/8))≠W a:=by
        intro eq;have:=Machine.wordNumber (by omega) (by have:=safe.1; change a+8≤68719476736 at this;omega) eq
        have:=safe.2;omega
      rw [if_neg inside,Machine.byteWord,Machine.byteWord s]
      change extractByte ((s.setMem _ _).getMem _) _=_
      rw [MachineState.getMem_setMem_ne ne]

end CommitGolfCandidate.R4b
