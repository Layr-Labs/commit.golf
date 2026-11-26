import CommitGolfCandidate.ReconstructedHonestProtected
import CommitGolfCandidate.ReconstructedHonestCuts

namespace CommitGolfCandidate.Reconstruction.HonestRegionBlocks
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestRanges HonestRegionStep HonestProtected HonestCuts

def callable (a : Abstract) (op : Instruction) := !isQuery op || singleton (a.regs .x5)==some 0

def check {n : Nat} (c : Context) (packed : ArtifactEncoding.Packed n)
    (cut : Word → Bool) (post : Word → Option Shape) : Nat → Word → Abstract → Bool
  | 0,_,_ => false
  | k+1,pc,a =>
    match HonestBlocks.readOp packed pc with
    | none => false
    | some op =>
      callable a op && HonestFlow.direct op && safe c a op &&
        (HonestAbstract.destinations pc (exactFile a.regs) op).all (fun target =>
          let b := advance a op
          if cut target then (post target).any (fits b) else check c packed cut post k target b)

private theorem unfold_walk {im : Image} {coins : Bool} {cut : Word → Bool} {s t : MachineState}
    (walk : Reaches im coins cut s t) : ∃ out, out ∈ support (execute im 1 s coins) ∧
    out.exit=.unfinished ∧ ((cut out.state.pc=true ∧ t=out.state) ∨
      (cut out.state.pc=false ∧ Reaches im coins cut out.state t)) := by
  cases walk with
  | hit a b c => exact ⟨_,a,b,Or.inl ⟨c,rfl⟩⟩
  | more a b c d => exact ⟨_,a,b,Or.inr ⟨c,d⟩⟩

/-- A block may branch on arbitrary input. Each real cutpoint must match its
specific successor shape and retain all immutable RAM zones. -/
theorem sound {n : Nat} (c : Context) (packed : ArtifactEncoding.Packed n) (im : Image)
    (code : im.code=ArtifactEncoding.decode 32 packed) (small : 4096+4*n<2^64)
    (cut : Word → Bool) (post : Word → Option Shape) (clock : Nat) (pc : Word) (a : Abstract)
    (cert : check c packed cut post clock pc a=true)
    (s t : MachineState) (coins : Bool) (entry : s.pc=pc) (meaning : Models s a)
    (frozen : ∀ q, protects c q=true → a.ram q=c.fixed q) (walk : Reaches im coins cut s t) :
    ∃ shape, post t.pc=some shape ∧ Holds c shape t := by
  induction clock generalizing pc a s with
  | zero => cases cert
  | succ k ih =>
    cases opAt : HonestBlocks.readOp packed pc with
    | none => simp [check,opAt] at cert
    | some op =>
      simp only [check,opAt,Bool.and_eq_true] at cert
      obtain ⟨⟨⟨call,direct⟩,safe⟩,edges⟩ := cert
      have pub : op=.base .ECALL → s.getReg .x5=0 := by
        rintro rfl
        simp only [callable,isQuery,Bool.not_true,Bool.false_or,beq_iff_eq] at call
        exact singleton_ok (meaning.1 _) call
      obtain ⟨out,run,cont,rest⟩ := unfold_walk walk
      have fetch := HonestBlocks.fetch_op packed im code small s op (entry ▸ opAt)
      obtain ⟨dest,next⟩ := one im s coins a op meaning fetch direct pub out run cont
      rw [entry] at dest
      have edge := List.all_eq_true.mp edges _ dest
      have keep (q : Word) (present : protects c q=true) : (advance a op).ram q=c.fixed q :=
        (unchanged c a s op meaning safe q present).trans (frozen _ present)
      rcases rest with ⟨done,rfl⟩ | ⟨more,tail⟩
      · simp only [done,ite_true] at edge
        cases shapeAt : post out.state.pc with
        | none => simp [shapeAt] at edge
        | some b =>
          simp only [shapeAt,Option.any_some] at edge
          have facts := fits_ok next edge
          exact ⟨b,rfl,facts.1,facts.2,fun q present => (keep q present) ▸ next.2 q⟩
      · simp only [more,Bool.false_eq_true,ite_false] at edge
        exact ih _ _ edge _ rfl next keep tail

theorem from_shape {n : Nat} (c : Context) (packed : ArtifactEncoding.Packed n) (im : Image)
    (code : im.code=ArtifactEncoding.decode 32 packed) (small : 4096+4*n<2^64)
    (cut : Word → Bool) (post : Word → Option Shape) (clock : Nat) (pc : Word) (a : Shape)
    (cert : check c packed cut post clock pc (a.model c)=true)
    (s t : MachineState) (coins : Bool) (entry : s.pc=pc) (meaning : Holds c a s)
    (walk : Reaches im coins cut s t) : ∃ shape, post t.pc=some shape ∧ Holds c shape t :=
  sound _ _ _ code small cut post clock pc _ cert s t coins entry (models_shape meaning)
    (fun q h => by simp only [Shape.model,h,ite_true]) walk

end CommitGolfCandidate.Reconstruction.HonestRegionBlocks
