import CommitGolfCandidate.ReconstructedCheckParentExecution

namespace CommitGolfCandidate.Reconstruction.CheckParentGeometry
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine
open CheckValues CheckOrdinary CheckParentImage CheckParentRun CheckParentPlan CheckParentCall CheckParentWords CheckParentExecution CheckOracleMemory CheckRecorded
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

structure Geometry where
  stack : Nat
  pair : Nat
  out : Nat

def base (g : Geometry) : Nat→Nat | 1=>g.stack | 2=>g.pair | 3=>g.out | _=>0
def lo : Nat→Nat | 0=>2097560 | _=>0
def hi : Nat→Nat | 0=>2098152 | 1=>144 | 2=>64 | 3=>32 | _=>0

structure Placed (g : Geometry) : Prop where
  align : ∀ r : Fin 4, base g r%8=0
  room : ∀ r : Fin 4, base g r+hi r≤MEMORY_BYTES
  apart : ∀ r u : Fin 4, r≠u → base g r+hi r≤base g u+lo u ∨ base g u+hi u≤base g r+lo r

def constants (s : MachineState) :=
  ∀ a w, a%8=0 → ro a=some w → s.getMem (BitVec.ofNat 64 a)=w

def env (g : Geometry) (s : MachineState) (o : Oracle) (seed : Key) : Env where
  initial:=s
  base:=fun r=>BitVec.ofNat 64 (base g r)
  zero:=rfl
  answer:=fun q i=>(result o seed q).extractLsb' (64*i) 64

private theorem ro_bounds (a : Nat) (yes : (ro a).isSome=true) : 2097560≤a ∧ a<2098152 := by
  unfold ro at yes
  split_ifs at yes <;> simp_all <;> omega

private theorem allowed {a : Loc} (h : table.allowed a=true) :
    a.region<4 ∧ lo a.region≤a.offset.toNat ∧ a.offset.toNat+8≤hi a.region ∧ a.offset.toNat%8=0 := by
  obtain ⟨r,w⟩ := a
  change (_ && _) = true at h
  rw [Bool.and_eq_true] at h
  obtain ⟨al,valid⟩ := h
  change decide (w.toNat%8=0)=true at al
  have align := of_decide_eq_true al
  cases r with
  | zero=>
    have b:=ro_bounds w.toNat valid
    change 0<4 ∧ 2097560≤w.toNat ∧ w.toNat+8≤2098152 ∧ w.toNat%8=0
    omega
  | succ r=>
    cases r with
    | zero=>
      change decide (w.toNat<144)=true at valid;have b:=of_decide_eq_true valid
      change 1<4 ∧ 0≤w.toNat ∧ w.toNat+8≤144 ∧ w.toNat%8=0;omega
    | succ r=>
      cases r with
      | zero=>
        change decide (w.toNat<64)=true at valid;have b:=of_decide_eq_true valid
        change 2<4 ∧ 0≤w.toNat ∧ w.toNat+8≤64 ∧ w.toNat%8=0;omega
      | succ r=>
        cases r with
        | zero=>
          change decide (w.toNat<32)=true at valid;have b:=of_decide_eq_true valid
          change 3<4 ∧ 0≤w.toNat ∧ w.toNat+8≤32 ∧ w.toNat%8=0;omega
        | succ r=>cases valid

theorem physical_nat (g : Geometry) (s : MachineState) (o : Oracle) (seed : Key) (a : Loc) :
    physical (env g s o seed) a=BitVec.ofNat 64 (base g a.region+a.offset.toNat) := by
  unfold physical env;rw [BitVec.ofNat_add];simp

theorem layout (g : Geometry) (placed : Placed g) (s : MachineState) (rodata : constants s) (o : Oracle) (seed : Key) :
    CheckValues.Layout (env g s o seed) table := by
  have bound (a : Loc) (v : table.allowed a=true) : base g a.region+a.offset.toNat+8≤MEMORY_BYTES := by
    obtain ⟨hr,lb,ub,aligned⟩ := allowed v
    have room : base g a.region+hi a.region≤MEMORY_BYTES := placed.room ⟨_,hr⟩
    omega
  constructor
  · intro a v
    have b := bound a v
    have al : base g a.region%8=0 := placed.align ⟨_,(allowed v).1⟩
    have off := (allowed v).2.2.2
    rw [physical_nat]
    simp only [accessValid,rangeValid,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by unfold MEMORY_BYTES at b;omega : base g a.region+a.offset.toNat<2^64),
      Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨b,by omega⟩
  · intro a b va vb eq
    have aa:=allowed va;have bb:=allowed vb
    have ha:=bound a va;have hb:=bound b vb
    rw [physical_nat,physical_nat] at eq
    have num:=congrArg BitVec.toNat eq
    unfold MEMORY_BYTES at ha hb
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega :base g a.region+a.offset.toNat<2^64),
      Nat.mod_eq_of_lt (by omega :base g b.region+b.offset.toNat<2^64)] at num
    by_cases r : a.region=b.region
    · have w : a.offset=b.offset := by apply BitVec.eq_of_toNat_eq;rw [r] at num;omega
      cases a;cases b;simp_all
    · have apart := placed.apart ⟨_,aa.1⟩ ⟨_,bb.1⟩ (fun h=>r (congrArg Fin.val h))
      change base g a.region+hi a.region≤base g b.region+lo b.region ∨ base g b.region+hi b.region≤base g a.region+lo a.region at apart
      omega
  · intro a w init
    change (if a.region=0 ∧ a.offset.toNat%8=0 then ro a.offset.toNat else none)=some w at init
    split at init <;> try contradiction
    rename_i key
    have raw := rodata _ _ key.2 init
    change s.getMem _=_
    rw [physical_nat,key.1];simpa only [base,Nat.zero_add] using raw

theorem phys_loc (g : Geometry) (s : MachineState) (o : Oracle) (seed : Key) (r n : Nat) (small : n<2^64) :
    physical (env g s o seed) (loc r n)=BitVec.ofNat 64 (base g r+n) := by
  rw [physical_nat];change BitVec.ofNat 64 (base g r+n%2^64)=_;rw [Nat.mod_eq_of_lt small]

private theorem input_source (g : Geometry) (placed : Placed g) (s : MachineState) (o : Oracle)
    (d : Nat) (l r : Binding.Digest) (left : CommitParents.cell s g.pair=l) (right : CommitParents.cell s (g.pair+32)=r) :
    Source (env g s o (pairKey (d+1) l r)) l r := by
  intro i
  let e:=env g s o (pairKey (d+1) l r)
  change s.getMem (physical e (loc 2 (8*i.val)))=_
  rw [phys_loc _ _ _ _ 2 _ (by have:=i.isLt;omega)]
  change s.getMem (BitVec.ofNat 64 (g.pair+8*i.val))=_
  have both (a : Nat) (x : Binding.Digest) (cell : CommitParents.cell s a=x) : readBuffer s a 32=pack x := by
    rw [←cell];exact (Binding.pack_unpack _).symm
  have align : g.pair%8=0 := placed.align 2
  by_cases low : i.val<4
  · rw [ite_eq_left low,Nat.mod_eq_of_lt low,digWord,←both _ _ left]
    exact (read_digest_word s g.pair i align low).symm
  · have n : i.val%4<4 := Nat.mod_lt _ (by decide)
    rw [ite_eq_right low,digWord,←both _ _ right,read_digest_word s (g.pair+32) (i.val%4) (by omega) n]
    congr 2;have:=i.isLt;omega

theorem parameters (g : Geometry) (placed : Placed g) (s : MachineState) (o : Oracle) (d : Fin 24) (l r : Binding.Digest)
    (left : CommitParents.cell s g.pair=l) (right : CommitParents.cell s (g.pair+32)=r) :
    Params o (env g s o (pairKey (d.val+1) l r)) d (pairKey (d.val+1) l r) := by
  let seed:=pairKey (d.val+1) l r
  have answers : Answers (env g s o seed) o seed d := fun _ _ _ _=>rfl
  refine ⟨row_word o _ d l r (input_source g placed s o d l r left right) answers,answers,?_⟩
  intro q bound
  have stackRoom : g.stack+144≤MEMORY_BYTES := placed.room 1
  have outRoom : g.out+32≤MEMORY_BYTES := placed.room 3
  have stackAlign : g.stack%8=0 := placed.align 1
  have outAlign : g.out%8=0 := placed.align 3
  have s₀ : g.stack<2^64 := by unfold MEMORY_BYTES at stackRoom;omega
  have s₁ : g.stack+64<2^64 := by unfold MEMORY_BYTES at stackRoom;omega
  have out₀ : g.out<2^64 := by unfold MEMORY_BYTES at outRoom;omega
  unfold input output
  split_ifs <;> simp only [phys_loc _ _ _ _ 1 64 (by decide),phys_loc _ _ _ _ 1 0 (by decide),phys_loc _ _ _ _ 3 0 (by decide),base,Nat.add_zero,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt s₀,Nat.mod_eq_of_lt s₁,Nat.mod_eq_of_lt out₀] <;>
    refine ⟨by omega,by omega,by omega,by omega,by decide,by decide⟩

end CommitGolfCandidate.Reconstruction.CheckParentGeometry
