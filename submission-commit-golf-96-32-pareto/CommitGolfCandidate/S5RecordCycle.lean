import CommitGolfCandidate.S5RecordCount
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (Levels SaltTape)
attribute [local irreducible] afterLatch readBuffer ix perRecord
set_option maxHeartbeats 40000
private theorem advance_frame {s u v : MachineState} {r k dst : Nat} (old : OrdinaryRegs s r k dst)
    (pc : v.pc=pcAt (if r+1<k then 459+42 else 933+56))
    (remain : v.getReg .x22=W (k-(r+1)))
    (keep : ∀ q,q∉([.x4,.x6,.x7,.x9,.x14,.x19,.x28] : List Reg)→u.getReg q=s.getReg q)
    (last : ∀ q,q≠.x22→v.getReg q=u.getReg q)
    (ix : u.getReg .x9=W (indexBase+8*(r+1))) (dest : u.getReg .x19=W (dst+824)) :
    OrdinaryRegs v (r+1) k (dst+824) :=
  ⟨pc,(last .x3 (by decide)).trans ((keep .x3 (by decide)).trans old.table),
    (last .x9 (by decide)).trans ix,remain,(last .x20 (by decide)).trans ((keep .x20 (by decide)).trans old.salts),
    (last .x25 (by decide)).trans ((keep .x25 (by decide)).trans old.radix),
    (last .x18 (by decide)).trans ((keep .x18 (by decide)).trans old.proof),(last .x19 (by decide)).trans dest⟩

private theorem frame_relabel (s t : MachineState) (eq : t.mem=s.mem) (tab : Capacity s) : Capacity t :=
  fun j hj=>(congrFun eq (W (2048+8*j))).trans (tab j hj)

private theorem run_two (s u v : MachineState) (n m : Nat) (a : Runs s u n (n+12)) (b : Runs u v 2 2)
    (cost : n+2=m) : Runs s v m (m+12) := by
  have eq : n+12+2=m+12 := by omega
  exact (congrArg₂ (Runs s v) cost eq).mp (a.trans b)

private theorem cycle_cost (xs : List Index) (r : Nat) :
    (if (ix xs r).val%2=0 then 486 else 485)+2=perRecord xs r := by unfold perRecord;split <;> rfl

private theorem finish_record (s u v : MachineState) (r dst : Nat) (xs : List Index) (tree : Levels) (salt : SaltTape)
    (n : Nat) (mode : r+1<xs.length ↔ 0<n) (remaining : xs.length-(r+1)=n)
    (reg : OrdinaryRegs s r xs.length dst)
    (f : Nat) (cost : f+2=perRecord xs r)
    (head : Runs s u f (f+12)) (dest : u.getReg .x19=W (dst+824)) (ix' : u.getReg .x9=W (indexBase+8*(r+1)))
    (tab : Capacity u) (sources : Sources u xs tree salt)
    (keep : ∀ q,q∉([.x4,.x6,.x7,.x9,.x14,.x19,.x28] : List Reg) → u.getReg q=s.getReg q)
    (data : Written s u dst (normalBytes tree salt (ix xs r)))
    (back : Runs u v 2 2) (pc : v.pc=pcAt (if 0<n then 501 else 989)) (rem : v.getReg .x22=W n)
    (same : v.mem=u.mem) (regs : ∀ q,q≠.x22 → v.getReg q=u.getReg q) :
    Runs s v (perRecord xs r) (perRecord xs r+12) ∧ OrdinaryRegs v (r+1) xs.length (dst+824) ∧
      Capacity v ∧ Sources v xs tree salt ∧ Written s v dst (normalBytes tree salt (ix xs r)) := by
  have ep : v.pc=pcAt (if r+1<xs.length then 501 else 989) := by rw [show (if r+1<xs.length then 501 else 989)=(if 0<n then 501 else 989) by simp only [mode]];exact pc
  exact ⟨run_two s u v f _ head back cost,advance_frame reg ep (rem.trans (congrArg W remaining.symm)) keep regs ix' dest,
    frame_relabel u v same tab,sources.same_mem same,data.congr_mem rfl same⟩
theorem record_cycle (xs : List Index) (tree : Levels) (salt : SaltTape) (r dst : Nat) (s : MachineState)
    (lt : r<xs.length) (size : xs.length≤LENGTH) (reg : OrdinaryRegs s r xs.length dst) (tab : Capacity s)
    (src : Sources s xs tree salt) (high : proofBase≤dst) (valid : AddrOK dst 824) :
    ∃ v,Runs s v (perRecord xs r) (perRecord xs r+12) ∧ OrdinaryRegs v (r+1) xs.length (dst+824) ∧
      Capacity v ∧ Sources v xs tree salt ∧ Written s v dst (normalBytes tree salt (ix xs r)) := by
  rcases ordinary_record s r dst xs tree salt lt size (reg.pc.trans (by rw [if_pos lt]))
    reg.table tab reg.indices reg.salts reg.radix reg.dest high valid src with ⟨u,step⟩
  let n:=xs.length-(r+1)
  have left : n<LENGTH := by dsimp [n];omega
  have cnt : u.getReg .x22=W (n+1) := (step.2.2.2.2.2.2.1 .x22 (by decide)).trans
    (reg.remaining.trans (congrArg W (by dsimp [n];omega)))
  have ctrl:=latch u n left step.2.1 cnt
  exact ⟨afterLatch u,finish_record s u (afterLatch u) r dst xs tree salt n (by dsimp [n];omega) rfl reg _
    (cycle_cost xs r) step.1 step.2.2.1 step.2.2.2.1 step.2.2.2.2.1 step.2.2.2.2.2.1 step.2.2.2.2.2.2.1 step.2.2.2.2.2.2.2
    ctrl.1 ctrl.2.1 ctrl.2.2.1 ctrl.2.2.2.1 ctrl.2.2.2.2⟩
end CommitGolfCandidate.S5Machine.Open
