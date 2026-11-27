import CommitGolfCandidate.RungAPlan
import CommitGolfCandidate.R4Header
namespace CommitGolfCandidate.RungA.Kernel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 R4 Late
set_option Elab.async false
set_option maxRecDepth 1500
set_option maxHeartbeats 180000
attribute [local irreducible] DetRun execute readBuffer writeBits R4.submission
def stableReg (q : Reg) := q≠.x10 ∧ q≠.x12 ∧ q≠.x6
def Stable (s t : MachineState) := ∀ q,stableReg q → t.getReg q=s.getReg q
theorem Stable.trans {s t u} (a : Stable s t) (b : Stable t u) : Stable s u :=
  fun q h=>(b q h).trans (a q h)

theorem listed_take {n} {a b : List Instr} (all : listed n (a++b)=true) : listed n a=true ∧ listed (n+a.length) b=true := by
  constructor
  · apply List.all_eq_true.mpr;intro j _
    have e:=List.all_eq_true.mp all ⟨j.val,by simp;omega⟩ (List.mem_finRange ..)
    simpa only [List.getElem_append_left j.isLt] using e
  · apply List.all_eq_true.mpr;intro j _
    have fit : a.length+j.val<(a++b).length:=by simp [j.isLt]
    have e:=List.all_eq_true.mp all ⟨a.length+j.val,fit⟩ (List.mem_finRange ..)
    simpa only [List.getElem_append_right (Nat.le_add_right ..),Nat.add_sub_cancel_left,Nat.add_assoc] using e

theorem setPointer (o : Oracle) (s : MachineState) (n : Nat) (rd rs : Reg) (imm : BitVec 12) (v : Word)
    (rd0 : rd≠.x0) (site : Site n (.ADDI rd rs imm)) (pc : s.pc=pcAt n)
    (eqn : s.getReg rs+signExtend12 imm=v) :
    ∃ t,MRun o s 1 t 1 0 ∧ t.pc=pcAt (n+1) ∧ t.mem=s.mem ∧ t.getReg rd=v ∧
      ∀ q,rd≠q → t.getReg q=s.getReg q := by
  let t:=execInstrBr s (.ADDI rd rs imm)
  refine ⟨t,DetRun.step1 (site s pc) rfl,(pc_exec_ADDI ..).trans (pc_step_idx s n pc),mem_exec_ADDI ..,?_,?_⟩
  · change (s.setReg rd _).getReg rd=_
    exact (MachineState.getReg_setReg_eq rd0).trans eqn
  · intro q ne;exact MachineState.getReg_setReg_ne _ _ _ _ ne

structure Assigned (o : Oracle) (s t : MachineState) (n k a b : Nat) : Prop where
  run : MRun o s k t k 0
  pc : t.pc=pcAt (n+k)
  mem : t.mem=s.mem
  src : t.getReg .x10=Z b
  dst : t.getReg .x12=Z a
  stay : ∀ q,q≠.x10 → q≠.x12 → t.getReg q=s.getReg q

theorem assign (o : Oracle) (s : MachineState) (n a b : Nat) (sr dr : Reg) (si di : BitVec 12) (set : Bool)
    (pc : s.pc=pcAt n) (source : s.getReg sr+signExtend12 si=Z b)
    (dest : s.getReg dr+signExtend12 di=Z a) (safe : dr≠.x10) (current : set=false → s.getReg .x12=Z a)
    (first : Site n (.ADDI .x10 sr si)) (second : set=true → Site (n+1) (.ADDI .x12 dr di)) :
    ∃ t,Assigned o s t n (if set then 2 else 1) a b := by
  obtain ⟨u,run,ip,mu,src,keep⟩:=setPointer o s n .x10 sr si _ (by decide) first pc source
  cases set with
  | false=>exact ⟨u,run,ip,mu,src,(keep _ (by decide)).trans (current rfl),fun q h _=>keep q h.symm⟩
  | true=>
    obtain ⟨t,run',end_,mt,dst,keep'⟩:=setPointer o u (n+1) .x12 dr di _ (by decide) (second rfl) ip
      (by rw [keep dr safe.symm,dest])
    exact ⟨t,run.trans run',end_,mt.trans mu,(keep' _ (by decide)).trans src,dst,fun q h j=>(keep' q j.symm).trans (keep q h.symm)⟩

end CommitGolfCandidate.RungA.Kernel
