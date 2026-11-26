import CommitGolfCandidate.ReconstructedOpeningLinear

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps OpeningOps
open TwoPermutationPrototype.RV64 OpeningCursor OpeningHeaderAddress OpeningLinear
set_option maxRecDepth 24000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode execute

structure Context where
  initial : Model
  index : Index
  cursor : Nat

def s237 (x : Context) : Model := ⟨fun
  | .x0 => 0 | .x7 => W x.cursor | .x8 => 68719476336 | .x15 => W x.index.val
  | .x22 => W heap | .x25 => wordAddress OpeningPut.base | r => x.initial.reg r, x.initial.mem⟩

theorem initial_eq (x : Context) (z : x.initial.reg .x0=0) (c : x.initial.reg .x7=W x.cursor)
    (sp : x.initial.reg .x8=68719476336) (i : x.initial.reg .x15=W x.index.val)
    (t : x.initial.reg .x22=W heap) (p : x.initial.reg .x25=wordAddress OpeningPut.base) :
    s237 x=x.initial := by
  cases h : x.initial with
  | mk r m =>
    simp only [h] at z c sp i t p
    unfold s237;rw [h];congr 1;funext n
    cases n <;> first | rfl | exact z.symm | exact c.symm | exact sp.symm | exact i.symm | exact t.symm | exact p.symm

def top (x : Context) (d : Nat) := x.initial.mem (wordAt x.index d 3)
def v237 (x : Context) : Word := (((4096 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)
def s238 (x : Context) := (s237 x).set .x10 (v237 x)
def v238 (x : Context) : Word := W (2^24+x.index.val)
def s239 (x : Context) := (s238 x).set .x10 (v238 x)
def v239 (x : Context) : Word := W (x.cursor+120)
def s240 (x : Context) := (s239 x).set .x19 (v239 x)
def v240 (x : Context) : Word := (v238 x) >>> (9 : Nat)
def s241 (x : Context) := (s240 x).set .x11 (v240 x)
def v241 (x : Context) : Word := (v240 x) &&& signExtend12 4064
def s242 (x : Context) := (s241 x).set .x11 (v241 x)
def v242 (x : Context) : Word := (v241 x) ^^^ signExtend12 32
def s243 (x : Context) := (s242 x).set .x11 (v242 x)
def v243 (x : Context) : Word := basePtr x.index 10
def s244 (x : Context) := (s243 x).set .x11 (v243 x)
def v244 (x : Context) : Word := (((1 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)
def s245 (x : Context) := (s244 x).set .x12 (v244 x)
def v245 (x : Context) : Word := (68719476336 : Word) - (v244 x)
def s246 (x : Context) := (s245 x).set .x12 (v245 x)
def s247 (x : Context) := (s246 x).store 8589934269 (v243 x)
theorem tree247 (x : Context) (d w : Nat) (p : 0<d) (q : d≤24) (u : w<4) :
    (s247 x).mem (wordAt x.index d w)=x.initial.mem (wordAt x.index d w) := by
  have sep : wordAt x.index d w ≠ 8589934269 := by have := word_room x.index d w p q u;omega
  change (if wordAt x.index d w=8589934269 then _ else _) = _
  rw [if_neg sep]
  rfl
def v247 (x : Context) := top x 10
def s248 (x : Context) := (s247 x).set .x11 (v247 x)

def code237 : List Instr := [
  (Expr.instr .x10 (.lui 4096)),
  (Expr.instr .x10 (.add .x15 .x10)),
  (Expr.instr .x19 (.addi .x7 120)),
  (Expr.instr .x11 (.srli .x10 9)),
  (Expr.instr .x11 (.andi .x11 4064)),
  (Expr.instr .x11 (.xori .x11 32)),
  (Expr.instr .x11 (.add .x11 .x22)),
  (Expr.instr .x12 (.lui 1)),
  (Expr.instr .x12 (.sub .x8 .x12)),
  .SD .x12 .x11 1912,
  .LD .x11 .x11 344]
theorem entries237 : OpeningStraight.Listed 237 code237 := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem span237 (o : Oracle) (x : Context) : Contract o code237 (s237 x) (s248 x) := by
  have h237 := OpeningLinear.register o (s237 x) .x10 (.lui 4096) (v237 x) rfl
  have h238 := OpeningLinear.register o (s238 x) .x10 (.add .x15 .x10) (v238 x) (by change W x.index.val+v237 x=W (2^24+x.index.val);rw [show v237 x=W (2^24) from (by decide : (((4096 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)=W (2^24)),←BitVec.ofNat_add,Nat.add_comm])
  have h239 := OpeningLinear.register o (s239 x) .x19 (.addi .x7 120) (v239 x) (BitVec.ofNat_add ..).symm
  have h240 := OpeningLinear.register o (s240 x) .x11 (.srli .x10 9) (v240 x) rfl
  have h241 := OpeningLinear.register o (s241 x) .x11 (.andi .x11 4064) (v241 x) rfl
  have h242 := OpeningLinear.register o (s242 x) .x11 (.xori .x11 32) (v242 x) rfl
  have h243 := OpeningLinear.register o (s243 x) .x11 (.add .x11 .x22) (v243 x) (OpeningHeaderAddress.sibling_ptr x.index 10 (by decide))
  have h244 := OpeningLinear.register o (s244 x) .x12 (.lui 1) (v244 x) rfl
  have h245 := OpeningLinear.register o (s245 x) .x12 (.sub .x8 .x12) (v245 x) rfl
  have h246 := OpeningLinear.write o (s246 x) .x12 .x11 1912 8589934269 (v243 x) (by decide) (by change ((v245 x) + signExtend12 1912)=wordAddress 8589934269; exact (by decide : ((68719476336 : Word)-(((1 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64))+signExtend12 1912=wordAddress 8589934269)) rfl
  have h247 := OpeningLinear.read o (s247 x) .x11 .x11 344 (wordAt x.index 10 3) (top x 10) (by have := word_room x.index 10 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset x.index 10 3 344 rfl) (tree247 x 10 3 (by decide) (by decide) (by decide))
  exact LeafModel.combine h237 (LeafModel.combine h238 (LeafModel.combine h239 (LeafModel.combine h240 (LeafModel.combine h241 (LeafModel.combine h242 (LeafModel.combine h243 (LeafModel.combine h244 (LeafModel.combine h245 (LeafModel.combine h246 (LeafModel.combine h247 (LeafModel.empty _ _)))))))))))

end CommitGolfCandidate.Reconstruction.OpeningHeader
