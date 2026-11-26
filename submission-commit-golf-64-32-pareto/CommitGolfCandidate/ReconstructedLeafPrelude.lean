import CommitGolfCandidate.ReconstructedLeafSpill
import CommitGolfCandidate.ReconstructedLeafContent

namespace CommitGolfCandidate.Reconstruction.LeafPrelude
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
open LeafCode LeafModel LeafMacros CommitWindows LeafSpill

structure Fixed (m : Model) : Prop where
  mode : m.reg .x5 = 0
  base : m.reg .x8 = wordAddress generatorBase
  len : m.reg .x11 = 200
  kind : m.reg .x13 = 1
  ones : m.reg .x17 = -1

def updateCounter (m : Model) (g : Fin 342) :=
  if g.val%16 = 0 then m.store (generatorBase+1) (m.reg .x10) else m

theorem updateCounter_regs (m : Model) (g : Fin 342) : (updateCounter m g).reg = m.reg := by
  unfold updateCounter; split <;> rfl

def afterTape (o : Oracle) (m : Model) (src : Nat) (g : Fin 342) :=
  tapeState o (rawState o (updateCounter m g) src) src g

def afterGroup (o : Oracle) (m : Model) (src : Nat) (g : Fin 342) :=
  let a := afterTape o m src g
  if g.val < 341 then intermediate a (src-15) 8 else a

theorem group (o : Oracle) (m : Model) (src : Nat) (g : Fin 342) (lo : 25 ≤ src)
    (room : src+32 ≤ 2^33) (entry : m.reg .x10 = wordAddress (src-25)) (f : Fixed m) :
    Contract o (groupSetup g.val) m (afterGroup o m src g) := by
  let a := updateCounter m g
  let b := rawState o a src
  let c := afterTape o m src g
  have s1 : Contract o (if g.val%16=0 then [.SD .x8 .x10 8] else []) m a := by
    dsimp only [a,updateCounter]
    split
    · exact LeafModel.store _ _ _ _ _ _ (by decide) (by rw [f.base,plus generatorBase 1 8 rfl])
    · exact LeafModel.empty _ _
  have fixed : Fixed a := by
    exact ⟨(congrFun (updateCounter_regs m g) _).trans f.mode,
        (congrFun (updateCounter_regs m g) _).trans f.base,
        (congrFun (updateCounter_regs m g) _).trans f.len,
        (congrFun (updateCounter_regs m g) _).trans f.kind,
        (congrFun (updateCounter_regs m g) _).trans f.ones⟩
  have s2 := raw_call o a src lo room ((congrFun (updateCounter_regs m g) _).trans entry)
    fixed.mode fixed.len fixed.kind
  have s3 : Contract o (tapeCode g) b c := generator_call o b src g (by omega) room rfl
    fixed.base fixed.mode fixed.len fixed.kind
  have s4 : Contract o (if g.val<341 then spill else []) c (afterGroup o m src g) := by
    unfold afterGroup
    split
    · exact capture _ _ _ (by omega) rfl
    · exact LeafModel.empty _ _
  exact LeafModel.combine (LeafModel.combine s1 (LeafModel.combine s2 s3)) s4

theorem after_group_read {o : Oracle} {m : Model} {src : Nat} {g : Fin 342} (r : Reg)
    (kept : ∀ k : Fin 8, saved k.val ≠ r) :
    (afterGroup o m src g).reg r = (afterTape o m src g).reg r := by
  unfold afterGroup
  split
  · exact other _ _ _ _ (fun k hk => kept ⟨k,hk⟩)
  · rfl

theorem after_group_mem (o : Oracle) (m : Model) (src : Nat) (g : Fin 342) :
    (afterGroup o m src g).mem = (afterTape o m src g).mem := by
  unfold afterGroup
  split
  · exact memory ..  
  · rfl

theorem after_group_saved (o : Oracle) (m : Model) (src : Nat) (g : Fin 342) (full : g.val < 341)
    (j : Fin 8) : (afterGroup o m src g).reg (saved j.val) =
      (afterTape o m src g).mem (src-15+14+j.val) := by
  unfold afterGroup
  rw [if_pos full]
  exact captured .. 

theorem after_group_reg (o : Oracle) (m : Model) (src : Nat) (g : Fin 342)
    (r : Reg) (unused : ∀ k : Fin 8, saved k.val ≠ r) (lhs : r ≠ .x10) (rhs : r ≠ .x12) :
    (afterGroup o m src g).reg r = m.reg r := by
  rw [after_group_read r unused]
  simp only [afterTape,tapeState,rawState,Model.permute,Model.set,Ne.symm lhs,Ne.symm rhs,false_and,ite_false,
    updateCounter_regs]

theorem after_group_fixed (o : Oracle) (m : Model) (src : Nat) (g : Fin 342) (f : Fixed m) :
    Fixed (afterGroup o m src g) := by
  constructor
  all_goals rw [after_group_reg o m src g _ (by decide) (by decide) (by decide)]
  exacts [f.mode,f.base,f.len,f.kind,f.ones]

theorem after_group_dst (o : Oracle) (m : Model) (src : Nat) (g : Fin 342) :
    (afterGroup o m src g).reg .x12 = wordAddress (src-15) := by
  rw [after_group_read _ (by decide)]
  rfl

end CommitGolfCandidate.Reconstruction.LeafPrelude
