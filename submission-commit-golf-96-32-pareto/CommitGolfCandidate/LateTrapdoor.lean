import CommitGolfCandidate.LateCommit

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

abbrev Trapdoor := BitVec (8*submission.sizes.trapdoor)
def slice (td : Trapdoor) (addr n : Nat) : BitVec (8*n) :=
  td.extractLsb' (8*(addr-4294971424)) (8*n)

structure TrapdoorAgrees (td : Trapdoor) (levels : Levels) (salts : SaltTape) : Prop where
  nodes : ∀ d ≤ LOG_LENGTH, ∀ i < levelCount d, slice td (nodeAddress d i) 32 = node levels d i
  salt : ∀ i : Index, slice td (saltAddress i) 24 = salts i
  padding : ∀ h p k,Padding h p k → slice td (unusedSlotAddr h p k) 32=0
  missing : ∀ h≤LOG_LENGTH,∀ j,levelCount h≤j → node levels h j=0

private theorem preserved32 (s : MachineState) (src : s.getReg .x12=BitVec.ofNat 64 rootSource)
    (dst : s.getReg .x26=BitVec.ofNat 64 rootDestination) (a : Nat)
    (lo : 4294971424 ≤ a) (hi : a+32≤MEMORY_BYTES) (aligned : a%8=0) :
    readBuffer (haltState (rootCopy s)) a 32 = readBuffer s a 32 := by
  apply (read_digest_eq_iff _ _ _ _ aligned aligned).mpr
  intro w hw
  apply root_copy_away _ src dst
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold MEMORY_BYTES at hi;omega)]
  unfold rootDestination; omega

private theorem slice_exact (s : MachineState) (a n : Nat) (lo : 4294971424≤a) (hi : a+n≤7650414624) :
    slice (readBuffer s 4294971424 3355443200) a n = readBuffer s a n := by
  unfold slice
  exact (read_buffer_slice s 4294971424 3355443200 (a-4294971424) n (by omega)).trans
    (congrArg (fun x => readBuffer s x n) (show 4294971424+(a-4294971424)=a by omega))

theorem committed_trapdoor (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    TrapdoorAgrees (submission.readCommit (endCommit o m ws)).2
      (S4Hiding.tree o.compression m (wordTape ws)) (wordTape ws) := by
  let s := lastParent o m ws
  obtain ⟨_,src,dst⟩ := last_pointers o m ws len
  obtain ⟨tree,salts⟩ := committed_nodes o m ws len
  constructor
  · intro d hd i hi
    have lo : 4294971424≤nodeAddress d i := by unfold nodeAddress;omega
    have endNode := parent_below_salts d i hi
    change _ ≤ 5905584160 at endNode
    exact (slice_exact _ _ 32 lo (by omega)).trans
      ((preserved32 s src dst _ lo (by change _ ≤ 2^36;omega)
        (by exact nodeAligned _ _)).trans (tree d hd i hi))
  · intro i
    have small := i.isLt; change i.val < 16777216 at small
    have bounds : 4294971424≤saltAddress i ∧ saltAddress i+32≤7650414624 ∧ saltAddress i%8=0 := by
      unfold saltAddress rowBase; split <;> omega
    have full := preserved32 s src dst _ bounds.1 (by change _ ≤ 2^36;omega) bounds.2.2
    have sub (t : MachineState) : (readBuffer t (saltAddress i) 32).extractLsb' 0 192 = readBuffer t (saltAddress i) 24 :=
      read_buffer_slice _ _ 32 0 24 (by decide)
    exact (slice_exact _ _ 24 bounds.1 (by omega)).trans
      ((sub _).symm.trans ((congrArg (fun v : Digest => v.extractLsb' 0 192) full).trans ((sub _).trans (salts i))))
  · intro h p k gap
    let a:=unusedSlotAddr h p k
    have lo : 4294971424≤a:=by dsimp [a,unusedSlotAddr,rowAddress];omega
    have hi : a+32≤5905584160:=padValid h p k gap
    have al : a%8=0:=by dsimp only [a,unusedSlotAddr];have:=rowAligned h p;omega
    exact (slice_exact _ a 32 lo (by omega)).trans
      ((preserved32 s src dst a lo (by change a+32≤2^36;omega) al).trans (committed_padding o m ws len h p k gap))
  · intro h bh j outside
    exact (fixed_tree_node_all o.compression m (wordTape ws) h j bh).trans (missing_node _ _ _ _ outside)

end CommitGolfCandidate.Late
