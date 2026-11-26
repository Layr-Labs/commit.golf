import CommitGolfCandidate.LateOrdinaryRecord

namespace CommitGolfCandidate.Late.Check.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open scoped Classical
open CommitGolfCandidate.Late.Open (W wordAt indexBase proofBase)

private def targetRegs := [Reg.x8,.x19,.x21,.x24,.x25,.x26,.x27,.x30]
private theorem target_keep (s : MachineState) (j : Reg) (mem : j∈targetRegs) :
    (checkTargetState s).getReg j=s.getReg j := by cases j <;> first | rfl | contradiction

private theorem subOne (k r : Nat) (lt : r<k) :
    W (k-r)-1=W (k-(r+1)) := by
  change BitVec.ofNat 64 (k-r)-BitVec.ofNat 64 1=_
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  exact congrArg W (by omega)

private theorem isZero {n : Nat} (bounded : n<2^64) : W n=0 ↔ n=0 := by
  constructor
  · intro e;have step:=congrArg BitVec.toNat e
    rw [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bounded] at step;exact step.trans (by decide)
  · rintro rfl;rfl

attribute [local irreducible] checkEvaluation checkRootWordsState lower readBuffer

theorem compareRecord (o : Oracle) (x : CheckInput) (r : Nat) (s : MachineState) (ok : Hashed o x r s)
    (hr : r<x.positions.card) :
    if lower o.compression x r 24=x.commitment then ∃ u, Runs o s u 17 0 ∧ RowState x (r+1) u
    else Finishes o s 17 0 .failure := by
  let t:=checkTargetState s
  let same := ∀ j<4,t.getMem (t.getReg .x21+BitVec.ofNat 64 (8*j))=t.getMem (t.getReg .x23+BitVec.ofNat 64 (8*j))
  have tg:=rawBlock o (fun f=>check_target s ok.pc f false)
  have left : t.getReg .x21=256 := (target_keep s _ (by decide)).trans ok.scratch
  have right : t.getReg .x23=W rootBase := by
    change s.getReg .x26+(s.getReg .x20 <<< 5)=_;rw [ok.index,ok.root];simp
  have law : same ↔ lower o.compression x r 24=x.commitment := by
    have ref:=read_digest_eq_iff t t 256 rootBase (by decide) (by decide)
    have root := (ok.high rootBase 32 (by decide) (by decide)).trans (loaded_root x)
    have cb : readBuffer t 256 32=lower o.compression x r 24 := (read_congr_mem _ _ _ _ (show t.mem=s.mem from rfl)).trans ok.digest
    have cr : readBuffer t rootBase 32=x.commitment := (read_congr_mem _ _ _ _ (show t.mem=s.mem from rfl)).trans root
    rw [cb,cr] at ref
    unfold same
    rw [left,right]
    change (∀ j<4, t.getMem (BitVec.ofNat 64 256+BitVec.ofNat 64 (8*j))=t.getMem (BitVec.ofNat 64 rootBase+BitVec.ofNat 64 (8*j))) ↔ _
    simpa only [BitVec.ofNat_add] using ref.symm
  have sv (j : Nat) (hj : j<4) : accessValid (t.getReg .x21+BitVec.ofNat 64 (8*j)) 8=true := by
    rw [left];exact (by decide : ∀ i : Fin 4, accessValid (256+BitVec.ofNat 64 (8*i.val)) 8=true) ⟨j,hj⟩
  have dv (j : Nat) (hj : j<4) : accessValid (t.getReg .x23+BitVec.ofNat 64 (8*j)) 8=true := by
    rw [right];exact (by decide : ∀ i : Fin 4,accessValid (W rootBase+BitVec.ofNat 64 (8*i.val)) 8=true) ⟨j,hj⟩
  by_cases eq : lower o.compression x r 24=x.commitment
  · rw [if_pos eq]
    have agrees:=law.mpr eq
    let v:=checkRootWordsState t 66 4
    have pc : v.pc=4408 := check_root_words_pc t 66 (Or.inl rfl) rfl 4 (by decide) agrees
    let u:=checkPositionNextState v
    have cmp:=rawBlock o (fun f=>check_root_matches t 66 (Or.inl rfl) rfl sv dv agrees f false)
    have next:=rawBlock o (fun f=>check_position_next v pc f false)
    have keeps (j : Reg) (hj : j∈targetRegs) : v.getReg j=s.getReg j := by
      have ne : j≠.x6 ∧ j≠.x7 := (by intro r;cases r <;> decide : ∀ j : Reg,j∈targetRegs → j≠.x6 ∧ j≠.x7) j hj
      exact (check_root_words_preserves t 66 4 j ne.1 ne.2).1.trans (target_keep s j hj)
    have memory : u.mem=s.mem := (check_root_words_preserves t 66 4 .x8 (by decide) (by decide)).2
    have count := (keeps .x27 (by decide)).trans ok.left
    have dec : v.getReg .x27-1=W (x.positions.card-(r+1)) := by rw [count];exact subOne x.positions.card r hr
    have k : x.positions.card≤LENGTH := by simpa using Finset.card_le_univ x.positions
    change x.positions.card≤16777216 at k
    refine ⟨u,(tg.trans cmp).trans next,?_,dec,?_,(keeps _ (by decide)).trans ok.value,
      (keeps _ (by decide)).trans ok.proof,(keeps _ (by decide)).trans ok.root,
      (keeps _ (by decide)).trans ok.scratch,(keeps _ (by decide)).trans ok.depth,
      ok.high.trans (Micro.High.memory memory)⟩
    · rw [check_position_next_pc,dec]
      by_cases last : r+1=x.positions.card
      · rw [if_pos last,if_pos ((isZero (by omega)).mpr (by omega))]
      · rw [if_neg last,if_neg (fun e=>last (by have :=(isZero (by omega)).mp e;omega))]
    · change v.getReg .x24+W 8=_
      rw [keeps _ (by decide),ok.cursor,W,W,←BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
  · rw [if_neg eq]
    apply tg.finish (b:=15) (d:=0)
    intro f
    obtain ⟨e,exec,fail,_,_⟩:=check_root_rejects t 66 (Or.inl rfl) rfl sv dv (fun w=>eq (law.mp w)) f false
    unfold obs;rw [exec,check_evaluation_pure];exact Prod.ext fail rfl

end CommitGolfCandidate.Late.Check.Normal
