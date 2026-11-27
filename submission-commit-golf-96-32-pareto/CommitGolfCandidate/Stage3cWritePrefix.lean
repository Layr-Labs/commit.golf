import CommitGolfCandidate.Stage3cWireWords
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W wordAt)
open Reader (window)

theorem push_prefix {s t : MachineState} {base n v rem : Nat} (old : PackedPrefix s base n v)
    (progress : ChunkProgress s t rem (n%64)) (effect : ChunkPayload s t (n%64) (min rem 64))
    (space : base+8*(n/64)<2^64) (fit : (s.getMem (s.getReg .x10)).toNat<2^(min rem 64)) :
    PackedPrefix t base (n+min rem 64) (pushBits v n (s.getMem (s.getReg .x10)).toNat) := by
  let k:=n%64
  let w:=min rem 64
  let used:=k+w
  let x:=(s.getMem (s.getReg .x10)).toNat
  let updated:=pushBits v n x
  have wlim : w≤64:=min_le_right .. 
  have count := completed_add n w wlim
  have bits : (n+w)%64=used%64 := by dsimp [used,k];omega
  have word : (appendedWord s k).toNat=window updated (completedBits n) 64 := by
    rw [appendedWord,joined_word _ _ _ (old.held ▸ held_fits old.value),old.held,BitVec.toNat_ofNat]
    have eq:=word_at_end v n x
    change _=heldValue updated n%2^64
    rw [eq]
  refine ⟨new_prefix_bound old.value fit,?_,?_,next_held old wlim effect fit,?_⟩
  · rw [progress.dest,old.ptr]
    by_cases low : used<64
    · rw [if_pos low];apply congrArg W;dsimp [used,k] at low;omega
    · rw [if_neg low];change BitVec.ofNat 64 (base+8*(n/64))+BitVec.ofNat 64 8=_;rw [←BitVec.ofNat_add];apply congrArg W;dsimp [used,k] at low;omega
  · exact progress.bits.trans (congrArg W bits.symm)
  · intro j hj
    by_cases earlier : j<n/64
    · apply Eq.trans _ (earlier_word v n x j earlier).symm
      have addr := old.ptr
      by_cases low : used<64
      · have mem : t.mem=s.mem:=effect.memory.trans (if_pos low)
        exact (congrArg BitVec.toNat (congrFun mem (W (base+8*j)))).trans (old.words _ earlier)
      · have mem:=effect.memory.trans (if_neg low)
        have ne : W (base+8*j)≠s.getReg .x19 := by
          rw [addr];intro eq
          have e:=congrArg BitVec.toNat eq
          simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt space,Nat.mod_eq_of_lt (show base+8*j<2^64 by omega)] at e
          omega
        have get : wordAt t (base+8*j)=wordAt s (base+8*j) :=
          (congrFun mem (W (base+8*j))).trans (MachineState.getMem_setMem_ne ne)
        exact (congrArg BitVec.toNat get).trans (old.words _ earlier)
    · have same : j=n/64 := by change j<(n+w)/64 at hj;omega
      subst j
      have overflow : ¬used<64 := by change n/64<(n+w)/64 at hj;dsimp [used,k];omega
      have mem:=effect.memory.trans (if_neg overflow)
      have get : wordAt t (base+8*(n/64))=appendedWord s k := by
        unfold wordAt;change t.mem (W (base+8*(n/64)))=_
        rw [mem,old.ptr];exact MachineState.getMem_setMem_eq
      exact (congrArg BitVec.toNat get).trans word
end CommitGolfCandidate.Chained.BinaryMachine.Writer
