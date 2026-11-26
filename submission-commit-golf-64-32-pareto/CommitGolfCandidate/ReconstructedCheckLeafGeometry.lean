import CommitGolfCandidate.ReconstructedCheckLeaf

namespace CommitGolfCandidate.Reconstruction.CheckLeafGeometry
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckValues CheckOracleMemory CheckRecorded CheckLeafPlan CheckLeafCall CheckLeafWords
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxHeartbeats 1250000
set_option maxRecDepth 12000
set_option exponentiation.threshold 2048

structure Geometry where
  frame : Nat
  message : Nat

structure Placed (g : Geometry) : Prop where
  frameA : g.frame%8=0
  msgA : g.message%8=0
  frameRoom : g.frame+2400≤MEMORY_BYTES
  msgRoom : g.message+256≤MEMORY_BYTES
  apart : g.frame+2400≤g.message ∨ g.message+256≤g.frame

def base (g : Geometry) : Nat→Nat | 1=>g.frame | 2=>g.message | _=>0

def env (g : Geometry) (s : MachineState) (o : Oracle) (idx : Index) (n : Words 2) (msg : Words 32) : Env where
  initial:=s
  base:=fun r=>BitVec.ofNat 64 (base g r)
  zero:=rfl
  answer:=fun q i=>(o.permutation (request o idx n msg q)).extractLsb' (64*i) 64

private theorem phys (g : Geometry) (s : MachineState) (o : Oracle) (idx : Index) (n : Words 2) (msg : Words 32) (a : Loc) :
    physical (env g s o idx n msg) a=BitVec.ofNat 64 (base g a.region+a.offset.toNat) := by
  unfold physical env;rw [BitVec.ofNat_add];simp

theorem phys_loc (g : Geometry) (s : MachineState) (o : Oracle) (idx : Index) (n : Words 2) (msg : Words 32)
    (r k : Nat) (small : k<2^64) :
    physical (env g s o idx n msg) (CheckParentRun.loc r k)=BitVec.ofNat 64 (base g r+k) := by
  rw [phys];change BitVec.ofNat 64 (base g r+k%2^64)=_;rw [Nat.mod_eq_of_lt small]

private theorem allowed {a : Loc} (v : table.allowed a=true) :
    a.offset.toNat%8=0 ∧ ((a.region=1 ∧ a.offset.toNat+8≤2400) ∨ (a.region=2 ∧ a.offset.toNat+8≤256)) := by
  obtain ⟨r,k⟩:=a
  change (_ && _)=true at v
  rw [Bool.and_eq_true] at v
  obtain ⟨align,rng⟩:=v
  change decide (k.toNat%8=0)=true at align
  have al:=of_decide_eq_true align
  refine ⟨al,?_⟩
  change (r=1 ∧ k.toNat+8≤2400) ∨ (r=2 ∧ k.toNat+8≤256)
  cases r with
  | zero=>cases rng
  | succ r=>
    cases r with
    | zero=>change decide (k.toNat<2400)=true at rng;have:=of_decide_eq_true rng;omega
    | succ r=>
      cases r with
      | zero=>change decide (k.toNat<256)=true at rng;have:=of_decide_eq_true rng;omega
      | succ r=>cases rng

theorem layout (g : Geometry) (placed : Placed g) (s : MachineState) (marker : s.getMem (BitVec.ofNat 64 (g.frame+16))=3633)
    (o : Oracle) (idx : Index) (n : Words 2) (msg : Words 32) : Layout (env g s o idx n msg) table := by
  have room (a : Loc) (v : table.allowed a=true) :
      base g a.region + a.offset.toNat+8≤MEMORY_BYTES ∧ base g a.region%8=0 := by
    rcases (allowed v).2 with ⟨r,h⟩|⟨r,h⟩ <;> rw [r]
    · change g.frame+a.offset.toNat+8≤MEMORY_BYTES ∧ _
      exact ⟨by have:=placed.frameRoom;omega,placed.frameA⟩
    · change g.message+a.offset.toNat+8≤MEMORY_BYTES ∧ _
      exact ⟨by have:=placed.msgRoom;omega,placed.msgA⟩
  constructor
  · intro a v
    obtain ⟨b,al⟩:=room a v
    rw [phys]
    simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold MEMORY_BYTES at b;omega : base g a.region+a.offset.toNat<2^64),
      Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨b,by have:=(allowed v).1;omega⟩
  · intro a b va vb eq
    rw [phys,phys] at eq
    have num:=congrArg BitVec.toNat eq
    have x:=(room a va).1;have y:=(room b vb).1
    unfold MEMORY_BYTES at x y
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega :base g a.region+a.offset.toNat<2^64),
      Nat.mod_eq_of_lt (by omega :base g b.region+b.offset.toNat<2^64)] at num
    have same : a.region=b.region := by
      rcases (allowed va).2 with ⟨ra,ha⟩|⟨ra,ha⟩ <;> rcases (allowed vb).2 with ⟨rb,hb⟩|⟨rb,hb⟩ <;>
        simp only [ra,rb,base] at num ⊢ <;> have:=placed.apart <;> omega
    have offsets : a.offset=b.offset := by apply BitVec.eq_of_toNat_eq;rw [same] at num;omega
    cases a;cases b;simp_all
  · intro a w init
    change (if a=CheckParentRun.loc 1 16 then some 3633 else none)=some w at init
    split at init <;> try contradiction
    rename_i atMarker;subst a;cases init
    change s.getMem _=_
    rw [phys_loc _ _ _ _ _ _ _ _ (by decide)];exact marker

theorem params (g : Geometry) (placed : Placed g) (s : MachineState) (o : Oracle) (idx : Index) (n : Words 2) (msg : Words 32)
    (source : Source (env g s o idx n msg) idx n msg) : Params o (env g s o idx n msg) idx n msg := by
  refine ⟨input o _ idx n msg source (fun _ _ _ _=>rfl),fun _ _ _ _=>rfl,?_⟩
  intro q hq
  have room:=placed.frameRoom
  have align:=placed.frameA
  have bnd (j : Nat) (hj : j≤2400) : g.frame+j<2^64 := by unfold MEMORY_BYTES at room;omega
  unfold arg dst
  split_ifs <;>
    simp only [phys_loc _ _ _ _ _ _ 1 72 (by decide),phys_loc _ _ _ _ _ _ 1 128 (by decide),
      phys_loc _ _ _ _ _ _ 1 40 (by decide),phys_loc _ _ _ _ _ _ 1 2088 (by decide),base,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (bnd 72 (by decide)),Nat.mod_eq_of_lt (bnd 128 (by decide)),
      Nat.mod_eq_of_lt (bnd 40 (by decide)),Nat.mod_eq_of_lt (bnd 2088 (by decide))] <;> omega

end CommitGolfCandidate.Reconstruction.CheckLeafGeometry
