import CommitGolfCandidate.Stage3cCommit
import CommitGolfCandidate.InputMemory
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (PairCoins)
abbrev Trapdoor := BitVec (8*Artifact.submission.sizes.trapdoor)
def slice (td : Trapdoor) (addr n : Nat) := td.extractLsb' (8*(addr-tdBase)) (8*n)

structure TrapdoorAgrees (td : Trapdoor) (levels : Late.Levels) (salt : Late.SaltTape) : Prop where
  nodes : ∀ d ≤ LOG_LENGTH, ∀ i < levelCount d, slice td (nodeAddress d i) 32 = Late.node levels d i
  salts : ∀ i : Index, slice td (saltAddress i) 24 = salt i

private theorem slice_exact (s : MachineState) (a n : Nat) (lo : tdBase≤a) (hi : a+n≤tdBase+3221229568) :
    slice (readBuffer s tdBase 3221229568) a n = readBuffer s a n := by
  unfold slice
  exact (read_buffer_slice s tdBase 3221229568 (a-tdBase) n (by omega)).trans
    (congrArg (fun x => readBuffer s x n) (show tdBase+(a-tdBase)=a by omega))

theorem committed_trapdoor (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    TrapdoorAgrees (Artifact.submission.readCommit (endCommit o m ws)).2
      (Binary.treeM (M:=Id) o.compression m (wordTape ws)) (wordTape ws) := by
  let s := beforeExit o m ws
  obtain ⟨_,cm,tree,_⟩:=before_spec o m ws len
  constructor
  · intro d hd i hi
    have lo : tdBase≤nodeAddress d i := by unfold nodeAddress tdBase;omega
    have upper := parent_below_salts d i hi
    unfold rowBase at upper
    change slice (readBuffer (exited s) tdBase 3221229568) _ 32 = _
    rw [slice_exact _ _ _ lo (by unfold tdBase;omega),exited_retains s cm _ lo (by change _≤2^36;omega) (aligned_node d i)]
    exact (tree.nodes d hd i hi).trans (fixed_tree_node _ _ _ _ _ hd hi).symm
  · intro i
    have bound := salt_limits i
    obtain ⟨lo',hi'⟩:=bound
    unfold rowBase at lo'
    unfold scratchBase at hi'
    have lo : tdBase≤saltAddress i := by unfold tdBase;omega
    have aligned : saltAddress i % 8=0 := by unfold saltAddress rowBase;omega
    have full := exited_retains s cm _ lo (by change _≤2^36;omega) aligned
    have sub (t : MachineState) : (readBuffer t (saltAddress i) 32).extractLsb' 0 192 = readBuffer t (saltAddress i) 24 :=
      read_buffer_slice _ _ 32 0 24 (by decide)
    change slice (readBuffer (exited s) tdBase 3221229568) _ 24 = _
    exact (slice_exact _ _ _ lo (by unfold tdBase;omega)).trans
      ((sub _).symm.trans ((congrArg (fun v : Output => v.extractLsb' 0 192) full).trans ((sub _).trans (tree.salts i))))
end CommitGolfCandidate.Chained.BinaryMachine
