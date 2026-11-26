import CommitGolfCandidate.ReconstructedCheckGroupPiece
import CommitGolfCandidate.ReconstructedCheckGroupPlan

namespace CommitGolfCandidate.Reconstruction.CheckGroupFrame
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckGroupRadix CheckGroupWalk CheckGroupPiece CheckGroupPlan CheckStream
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 13000
set_option maxHeartbeats 1400000

def Sources (s : MachineState) (proof stream c : Nat) (xs : List Nat) :=
  ∀ i, i<groups xs → let g:=reader proof (c+31*i);Placed g ∧ Source s g stream

theorem count (xs : List Nat) (non : xs≠[]) : groups xs=groups (xs.drop 4)+1 := by
  have h:=List.length_pos_iff.mpr non
  unfold groups;rw [List.length_drop];omega

theorem dropAccess (s t : MachineState) (xs : List Nat) (j base v : Nat)
    (input : Access (memoryView s) base j xs) (room : base+4*(j+xs.length)≤MEMORY_BYTES)
    (stack : 528384≤base/8) (ids : ∀ a∈xs,a<1024)
    (good : LeafMemory.Agrees (memoryView t) (patch (memoryView s) (xs.take 4) v)) :
    Access (memoryView t) base (j+4) (xs.drop 4) := by
  intro i hi
  have b : 4+i<xs.length:=by rw [List.length_drop] at hi;omega
  have use:=input (4+i) b
  simp only [List.getElem_drop]
  rw [←Nat.add_assoc] at use
  let w:=CheckCapSlots.cell base (j+4+i)
  have bound : w<2^33:=by dsimp [w,CheckCapSlots.cell];unfold MEMORY_BYTES at room;omega
  have apart : 528384≤w:=by dsimp [w,CheckCapSlots.cell];omega
  change extractWord32 (memoryView t w) _=_
  rw [good w bound,patch_frame _ _ _ _ (fun k hk=>ids k (List.mem_of_mem_take hk)) (Or.inl apart)]
  exact use

theorem takeAccess (m : Memory) (xs : List Nat) (j base : Nat) (input : Access m base j xs) :
    Access m base j (xs.take 4) := by
  intro i hi
  simp only [List.getElem_take]
  exact input i (by rw [List.length_take] at hi;omega)

theorem sources (s t : MachineState) (xs : List Nat) (proof stream c v : Nat) (non : xs≠[])
    (src : Sources s proof stream c xs) (separate : 528384≤proof/8) (ids : ∀ a∈xs,a<1024)
    (good : LeafMemory.Agrees (memoryView t) (patch (memoryView s) (xs.take 4) v)) :
    Sources t proof stream (c+31) (xs.drop 4) := by
  intro i hi
  have more : i+1<groups xs:=by rw [count xs non];omega
  have src:=src (i+1) more
  rw [show c+31*(i+1)=c+31+31*i by omega] at src
  refine ⟨src.1,?_⟩
  intro j hj
  let g:=reader proof (c+31+31*i)
  let off:=wordBase g+8*j
  have al : off%8=0 := by have z:=src.1.align;change proof%8=0 at z;dsimp [off,wordBase,g,reader];omega
  have bounded : off/8<2^33 := by have z:=src.1.room;change wordBase g+40≤MEMORY_BYTES at z;dsimp [off];unfold MEMORY_BYTES at z;omega
  have away : 528384≤off/8:=by dsimp [off,wordBase,g,reader];omega
  have pos : W off=wordAddress (off/8):=by change W off=W (8*(off/8));congr 1;omega
  have ref:=src.2 j hj
  change s.getMem (W off)=_ at ref
  change t.getMem (W off)=_
  rw [pos] at ref ⊢
  exact (good (off/8) bounded).trans ((patch_frame _ _ _ _ (fun k hk=>ids k (List.mem_of_mem_take hk)) (.inl away)).trans ref)

end CommitGolfCandidate.Reconstruction.CheckGroupFrame

