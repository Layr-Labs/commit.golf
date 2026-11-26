import CommitGolfCandidate.ReconstructedCheckPairPhysical
import CommitGolfCandidate.ReconstructedCheckCapCall
import CommitGolfCandidate.ReconstructedCheckPath
import CommitGolfCandidate.ReconstructedHonestWords

namespace CommitGolfCandidate.Reconstruction.CheckEdge
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckPath CheckPairPhysical CheckParentGeometry
open TwoPermutationPrototype.Sampling
set_option maxHeartbeats 1100000
set_option maxRecDepth 15000

/-- Interpret the four untagged words in the checker’s digest format. -/
def digest (x0 x1 x2 x3 : Word) : Binding.Digest := ((x2++x1)++x0,x3)

theorem projected (d : Fin 24) (x y z lo digit : Word) (bits : Nat) (b : Nat)
    (tables : radix (d.val+1)=b*2^bits) (short : lo.toNat<2^bits) (rem : digit.toNat<b) :
    Canonical (d.val+1) (digest x y z ((digit <<< bits) ||| lo)) := by
  change (((digit <<< bits) ||| lo).toNat)<radix (d.val+1)
  rw [tables,BitVec.toNat_or,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  have controlled : digit.toNat*2^bits+lo.toNat < b*2^bits := by
    calc _ < digit.toNat*2^bits+2^bits:=Nat.add_lt_add_left short _
         _ = (digit.toNat+1)*2^bits:=(Nat.succ_mul ..).symm
         _ ≤ b*2^bits:=Nat.mul_le_mul_right _ rem
  have room : b*2^bits≤2^64:=by
    rw [←tables]
    exact (by decide : ∀ e : Fin 24,radix (e.val+1)≤2^64) d
  rw [Nat.mod_eq_of_lt (by omega : digit.toNat*2^bits<2^64),Nat.mul_comm digit.toNat,←Nat.two_pow_add_eq_or_of_lt short,
    Nat.mul_comm (2^bits)];exact controlled

theorem table : ∀ d : Fin 24, radix (d.val+1)=HonestWords.radix d*2^(HonestWords.low d) := by decide

theorem canonical_sibling (d : Fin 24) (x y z lo digit : Word) (short : lo.toNat<2^HonestWords.low d)
    (rem : digit.toNat<HonestWords.radix d) : Canonical (d.val+1) (digest x y z ((digit <<< HonestWords.low d) ||| lo)) :=
  projected d _ _ _ _ _ _ _ (table d) short rem

/-- Turn one successful lower-loop invocation into its recorded tree edge. -/
theorem lower (o : Oracle) (s : MachineState) (g : Geometry) (placed : Placed g) (d : Fin 24) (side : Bool)
    (call : Called s g d side) (ro : constants s) (cur sib : Binding.Digest)
    (current : child s CheckPair.current cur) (sibling : child s CheckPair.sibling sib)
    (curOk : Canonical (d.val+1) cur) (sibOk : Canonical (d.val+1) sib) :
    ∃ t, CheckRecorded.Segment o (23+CheckParent.Cost d) s t (log o d side cur sib) ∧ t.pc=CommitBlocks.addr 271 ∧
      Nonempty (Edge o (log o d side cur sib) d side cur (CommitParents.cell t g.out)) := by
  obtain ⟨t,sg,pc,computed,_⟩:=CheckPairPhysical.positive o s g placed d side call ro cur sib current sibling
  refine ⟨t,sg,pc,⟨(sides side cur sib).1,(sides side cur sib).2,?_,?_,?_,computed.symm,fun _ h=>h⟩⟩
  · cases side <;> assumption
  · cases side <;> assumption
  · cases side <;> rfl

/-- Each active cap-parent call records both paths through the same physical pair. -/
theorem upper (o : Oracle) (s : MachineState) (g : Geometry) (d : Fin 24) (placed : Placed g)
    (call : CheckCapCall.Called s g d) (ro : constants s) (l r : Binding.Digest)
    (left : CommitParents.cell s g.pair=l) (right : CommitParents.cell s (g.pair+32)=r)
    (leftOk : Canonical (d.val+1) l) (rightOk : Canonical (d.val+1) r) :
    let rows:=CheckParentExecution.rows o (pairKey (d.val+1) l r) 0 (work d)
    ∃ t, CheckRecorded.Segment o (5+CheckParent.Cost d) s t rows ∧ t.pc=CommitBlocks.addr 617 ∧
      ∀ side : Bool, Nonempty (Edge o rows d side (if side then r else l) (CommitParents.cell t g.out)) := by
  obtain ⟨t,sg,pc,computed,_⟩:=CheckCapCall.positive o s g d placed call ro l r left right
  exact ⟨t,sg,pc,fun _=>⟨l,r,leftOk,rightOk,rfl,computed.symm,fun _ h=>h⟩⟩

end CommitGolfCandidate.Reconstruction.CheckEdge
