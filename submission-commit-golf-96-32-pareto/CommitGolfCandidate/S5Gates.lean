import CommitGolfCandidate.S5PlainSites
import CommitGolfCandidate.S5Runs
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000

def disp13 (a b : Nat) := BitVec.ofInt 13 (4*((b:Int)-(a:Int)))
def disp21 (a b : Nat) := BitVec.ofInt 21 (4*((b:Int)-(a:Int)))
def gateWords (long : Bool) (more : Bool) := if long && more then 2 else 1
def gatePos (long : Bool) (endPC : Nat) := endPC-(if long then 2 else 1)
def gatePC (target donePC : Nat) (more : Bool) := pcAt (if more then target else donePC)

def Gate (long : Bool) (target donePC : Nat) : Prop :=
  let n:=gatePos long donePC
  n+1<18492 ∧ if long then
      n+2=donePC ∧ decoded n=some (.base (.BEQ .x20 .x0 8)) ∧
      decoded (n+1)=some (.base (.JAL .x0 (disp21 (n+1) target))) ∧
      pcAt (n+1)+signExtend21 (disp21 (n+1) target)=pcAt target
    else
      n+1=donePC ∧ decoded n=some (.base (.BNE .x20 .x0 (disp13 n target))) ∧
      pcAt n+signExtend13 (disp13 n target)=pcAt target
instance (long : Bool) (t e : Nat) : Decidable (Gate long t e) := by unfold Gate;infer_instance

theorem gate_run (long more : Bool) (target donePC : Nat) (s : MachineState) (o : Oracle)
    (pc : s.pc=pcAt (gatePos long donePC)) (code : Gate long target donePC)
    (nonzero : (s.getReg .x20 != 0)=more) :
    Runs .commit true o s (s.setPC (gatePC target donePC more)) (gateWords long more) (gateWords long more) 0 := by
  cases long with
  | false =>
    let n:=gatePos false donePC
    obtain ⟨small,ends,word,back⟩:=code
    have found:=decoded_site (pc:=n) (by change gatePos _ donePC<18492;omega) word s pc
    apply runs_step found
    change some (if s.getReg .x20 != s.getReg .x0 then s.setPC (s.pc+signExtend13 (disp13 n target)) else s.setPC (s.pc+4))=_
    rw [show s.getReg .x0=0 from rfl,nonzero,pc,back,pc_succ,ends]
    cases more <;> rfl
  | true =>
    let n:=gatePos true donePC
    obtain ⟨small,ends,beq,jal,back⟩:=code
    have found:=decoded_site (pc:=n) (by change gatePos _ donePC<18492;omega) beq s pc
    cases more with
    | false =>
      have zero : s.getReg .x20=0 := by simpa only [bne_eq_false_iff_eq] using nonzero
      apply runs_step found
      change some (if s.getReg .x20==s.getReg .x0 then s.setPC (s.pc+signExtend13 8) else _)=_
      rw [show s.getReg .x0=0 from rfl,zero,beq_self_eq_true,if_pos (rfl : true=true),pc]
      change some (s.setPC (pcAt n+8))=some (s.setPC (pcAt donePC))
      rw [←ends];congr 2;unfold pcAt;change BitVec.ofNat 64 _+BitVec.ofNat 64 8=_;rw [←BitVec.ofNat_add];congr 1 <;> omega
    | true =>
      have nz : s.getReg .x20≠0 := bne_iff_ne.mp nonzero
      let t:=s.setPC (pcAt (n+1))
      have step : ordinaryStep s (.base (.BEQ .x20 .x0 8))=some t := by
        change some (if s.getReg .x20==s.getReg .x0 then _ else s.setPC (s.pc+4))=_
        rw [show s.getReg .x0=0 from rfl,beq_eq_false_iff_ne.mpr nz,if_neg (by decide : ¬false=true),pc,pc_succ]
      have jump:=decoded_site (pc:=n+1) small jal t rfl
      have land : ordinaryStep t (.base (.JAL .x0 (disp21 (n+1) target)))=some (s.setPC (pcAt target)) := by
        change some (s.setPC (pcAt (n+1)+signExtend21 (disp21 (n+1) target)))=_
        rw [back]
      exact runs_comp (runs_step found step) (runs_step jump land)

theorem tiled_gate : ∀ d : Height,¬chained d→0<tileSize d→ Gate (decide (tileSize d=252)) (mainPC d) (mainExit d) := by decide +kernel

theorem tail_gate : ∀ d : Height,¬chained d→d.val<23→ Gate false (tailPC d) (passEnd d) := by decide +kernel

theorem chain_gate : ∀ d : Height,chained d→Gate false (mainPC d) (mainExit d) := by decide +kernel
end CommitGolfCandidate.S5Machine
