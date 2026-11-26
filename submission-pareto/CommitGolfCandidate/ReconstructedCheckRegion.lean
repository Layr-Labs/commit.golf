import CommitGolfCandidate.ReconstructedCheckParentWords

namespace CommitGolfCandidate.Reconstruction.CheckRegion
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckValues CheckParentRun
set_option maxHeartbeats 850000

def tab (size : Nat) : Tables where
  allowed:=fun a=>decide (a.region=1 ∧ a.offset.toNat%8=0 ∧ a.offset.toNat<size)
  initial:=fun _=>none

def env (s : MachineState) (base : Nat) : Env where
  initial:=s
  base:=fun r=>if r=1 then BitVec.ofNat 64 base else 0
  zero:=rfl
  answer:=fun _ _=>0

theorem addr (s : MachineState) (base : Nat) (r : Loc) (one : r.region=1) :
    physical (env s base) r=BitVec.ofNat 64 (base+r.offset.toNat) := by
  simp [physical,env,one,BitVec.ofNat_add]

theorem point (s : MachineState) (base offset : Nat) :
    physical (env s base) (loc 1 offset)=BitVec.ofNat 64 (base+offset) := by
  simp [physical,env,loc,BitVec.ofNat_add]

theorem layout (s : MachineState) (base size : Nat) (align : base%8=0) (len : size%8=0) (room : base+size≤MEMORY_BYTES) :
    Layout (env s base) (tab size) := by
  have small (a : Loc) (h : (tab size).allowed a=true) :
      a.region=1 ∧ a.offset.toNat%8=0 ∧ base+a.offset.toNat+8≤MEMORY_BYTES := by
    change decide (_ ∧ _ ∧ _)=true at h
    rw [decide_eq_true_eq] at h;exact ⟨h.1,h.2.1,by omega⟩
  constructor
  · intro a ok
    obtain ⟨one,al,rb⟩:=small a ok
    rw [addr _ _ _ one]
    simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold MEMORY_BYTES at rb;omega : base+a.offset.toNat<2^64),
      Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨rb,by omega⟩
  · intro a b va vb eq
    obtain ⟨ra,_,ha⟩:=small a va;obtain ⟨rb,_,hb⟩:=small b vb
    have num:=congrArg BitVec.toNat eq
    rw [addr s base a ra,addr s base b rb] at num
    unfold MEMORY_BYTES at ha hb
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : base+a.offset.toNat<2^64),
      Nat.mod_eq_of_lt (by omega : base+b.offset.toNat<2^64)] at num
    have offsets : a.offset=b.offset := BitVec.eq_of_toNat_eq (by omega)
    cases a;cases b;simp_all
  · intro a w impossible;cases impossible

theorem frame (s : MachineState) (base size : Nat) (xs : Writes) (safe : Safe (tab size) xs)
    (p : Word) (fresh : ∀ j, 8*j<size→p≠BitVec.ofNat 64 (base+8*j)) :
    memory (env s base) p xs=s.getMem p := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    obtain ⟨a,v⟩:=x
    have ok:=safe (a,v) (by simp)
    change decide (a.region=1 ∧ a.offset.toNat%8=0 ∧ a.offset.toNat<size)=true at ok
    rw [decide_eq_true_eq] at ok
    have off : 8*(a.offset.toNat/8)=a.offset.toNat := by omega
    have notHere:=fresh (a.offset.toNat/8) (by omega)
    rw [off,←addr s base a ok.1] at notHere
    rw [memory,ite_eq_right notHere];exact ih (fun w k=>safe _ (List.mem_cons_of_mem _ k))

end CommitGolfCandidate.Reconstruction.CheckRegion
