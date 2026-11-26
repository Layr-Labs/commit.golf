import CommitGolfCandidate.S5Trapdoor
import CommitGolfCandidate.S5Commit
import CommitGolfCandidate.InputMemory
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (PairCoins)
private theorem slice_exact (s : MachineState) (a n : Nat) (lo : tdBase≤a) (hi : a+n≤tdBase+2818576384) :
    slice (readBuffer s tdBase 2818576384) a n = readBuffer s a n := by
  change (readBuffer s tdBase 2818576384).extractLsb' (8*(a-tdBase)) (8*n)=_
  exact (read_buffer_slice s tdBase 2818576384 (a-tdBase) n (by omega)).trans
    (congrArg (fun x => readBuffer s x n) (show tdBase+(a-tdBase)=a by omega))

theorem committed_trapdoor (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    TrapdoorAgrees (Artifact.submission.readCommit (endCommit o m ws)).2
      (S5Hiding.tree o.compression m (wordTape ws)) (wordTape ws) := by
  let s := beforeExit o m ws
  obtain ⟨_,cm,tree,_⟩:=before_spec o m ws len
  constructor
  · intro d hd i hi
    have lo : tdBase≤nodeAddress d i := by unfold nodeAddress tdBase;omega
    have upper := parent_below_salts d i hi
    unfold rowBase at upper
    change slice (readBuffer (exited s) tdBase 2818576384) _ 32 = _
    rw [slice_exact _ _ _ lo (by unfold tdBase;omega),exited_retains s cm _ lo (by change _≤2^36;omega) (aligned_node d i)]
    exact (tree.nodes d hd i hi).trans (fixed_tree_node _ _ _ _ _ hd hi).symm
  · intro i
    have bound := salt_limits i
    obtain ⟨lo',hi'⟩:=bound
    unfold rowBase at lo'
    unfold scratchBase at hi'
    have lo : tdBase≤saltAddress i := by unfold tdBase;omega
    have aligned : saltAddress i % 8=0 := by unfold saltAddress rowBase;split <;> omega
    have full := exited_retains s cm _ lo (by change _≤2^36;omega) aligned
    have sub (t : MachineState) : (readBuffer t (saltAddress i) 32).extractLsb' 0 192 = readBuffer t (saltAddress i) 24 :=
      read_buffer_slice _ _ 32 0 24 (by decide)
    change slice (readBuffer (exited s) tdBase 2818576384) _ 24 = _
    exact (slice_exact _ _ _ lo (by unfold tdBase;omega)).trans
      ((sub _).symm.trans ((congrArg (fun v : Output => v.extractLsb' 0 192) full).trans ((sub _).trans (tree.salts i))))
  · intro d p k hd hp hk missing
    let a:=unusedSlotAddr d p k
    have pad : Padding d p k := ⟨hd,hp,by unfold S4.radix at hk;split at hk <;> omega,Or.inr missing⟩
    have bound:=padValid _ _ _ pad
    have lo : tdBase≤a := by dsimp [tdBase,a,unusedSlotAddr,rowAddress];omega
    have al : a%8=0 := by dsimp [a,unusedSlotAddr];have :=rowAligned d p;omega
    have raw : readBuffer s a 32=0 := by
      obtain ⟨high,low⟩:=tree.pads d p k pad
      have full:=low (by unfold S4.radix at hk;split at hk <;> omega)
      have joint:=read_join s a 8 24
      change readBuffer s (a+8) 24 ++ readBuffer s a 8=(readBuffer s a 32).extractLsb' 0 256 at joint
      rw [show readBuffer s (a+8) 24=0 from high,show readBuffer s a 8=0 from full,BitVec.extractLsb'_eq_self] at joint
      exact joint.symm
    rw [fixed_tree_node_all o.compression m (wordTape ws) d (S4.radix d*p+k) (show d≤LOG_LENGTH from (show d≤24 by omega)),missing_node _ _ _ _ missing]
    change slice (readBuffer (exited s) tdBase 2818576384) a 32=0
    apply (slice_exact _ _ _ lo (by change a+32≤5502935040 at bound;unfold tdBase;omega)).trans
    exact (exited_retains s cm a lo (bound.trans (by decide)) al).trans raw
end CommitGolfCandidate.S5Machine
