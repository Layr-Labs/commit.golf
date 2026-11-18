import CommitGolfCandidate.GroupedKeySetup
import CommitGolfCandidate.TwoPermutationPackedLeafInput

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.RV64.PackedLeaves (wide_message_byte)
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000

private theorem written_words {w : Nat} (s : MachineState) (a : Nat) (v : BitVec w)
    (off cnt : Nat) (size : off+cnt ≤ (w+7)/8) (bound : (w+7)/8 ≤ 2^64) :
    readBuffer (writeBits s (BitVec.ofNat 64 a) v) (a+off) cnt =
      v.extractLsb' (8*off) (8*cnt) := by
  apply read_serialized_slice
  intro j hj
  simpa only [BitVec.ofNat_add,Nat.add_assoc,BitVec.add_assoc] using
    write_bits_byte s (BitVec.ofNat 64 a) v (off+j) (by omega) bound

private theorem high_word_zero (msg : Message) (w : Nat) (lo : 4294971392≤8*w) (hi : w+1≤2^33) :
    memoryView (Artifact.submission.initialState .commit msg) w=0 := by
  let s:=Artifact.submission
  change (s.initialState .commit msg).getMem (BitVec.ofNat 64 (8*w))=_
  rw [initial_input_word s .commit msg (8*w) (by omega)]
  have empty (j : Nat) (hj : j<8) : inputByte s .commit msg (8*w+j)=0 := by
    have gone : ¬(4096≤8*w+j ∧ 8*w+j<4096+LENGTH*(LEAF_SIZE/8)) := by change ¬(_ ∧ _<4096+16777216*256);omega
    have mb : s.layout.message=4096:=rfl
    have d : (s.image .commit).data=[]:=rfl
    simp only [inputByte,Submission.inputBuffers,List.find?_cons,messageBuffer,mb,gone,decide_false,
      Bool.false_eq_true,ite_false,List.find?_nil,d];simp
  rw [Finset.sum_eq_zero (fun j hj => by rw [empty j (Finset.mem_range.mp hj)];simp)];rfl

theorem seed_memory (s : MachineState) (k : Key) : (keyReady s k).mem=
    (writeBits s (BitVec.ofNat 64 (8*keyWord+8)) k).mem := by
  have adr : wordAddress (keyWord+1)=BitVec.ofNat 64 (8*keyWord+8) := by decide
  change (writeBits (keySetup s) (wordAddress (keyWord+1)) k).mem=_
  rw [adr]
  exact write_bits_memory_congr (keySetup s) s _ k rfl

theorem initially_good (o : Oracle) (k : Key) (msg : Message) :
    Good o k msg (memoryView (keyReady (Artifact.submission.initialState .commit msg) k)) 0 := by
  let s:=Artifact.submission.initialState .commit msg
  let st:=keyReady s k
  have same := seed_memory s k
  have outside (w : Nat) (hi : w+1≤2^33) (disjoint : w<keyWord+1 ∨ keyWord+4≤w) :
      memoryView st w=memoryView s w := by
    rw [←read_word,read_buffer_memory_congr _ _ same,write_bits_read_outside _ k _ _ _ (by decide)
      (by omega) (by dsimp [Key];rcases disjoint with h|h;left;omega;right;omega),read_word]
  constructor
  · intro i _;funext j
    have hi : i.val<16777216:=i.isLt
    have hj:=j.isLt
    rw [show window (memoryView st) (msgWord i.val) j=memoryView st (msgWord i.val+j.val) from rfl,
      outside _ (by unfold msgWord;omega) (Or.inl (by unfold msgWord keyWord leafSalt;omega)),←read_word]
    have atByte (l : Nat) (hl : l<8) :
        s.getByte (BitVec.ofNat 64 (8*(msgWord i.val+j.val)+l))=(msg i).extractLsb' (8*(8*j.val+l)) 8 := by
      rw [show 8*(msgWord i.val+j.val)+l=4096+256*i.val+(8*j.val+l) by unfold msgWord;omega]
      exact wide_message_byte Artifact.submission rfl msg i _ (by omega)
    simpa only [messageWords,←Nat.mul_assoc] using read_serialized_slice s (msg i) (8*(msgWord i.val+j.val)) (8*j.val) 8 atByte
  · intro _ h;omega
  · intro j lo hi
    by_cases inKey : j<4
    · rw [←read_word,read_buffer_memory_congr _ _ same,show 8*(keyWord+j)=(8*keyWord+8)+8*(j-1) by omega,
        written_words _ _ k (8*(j-1)) 8 (by dsimp [Key];omega) (by decide)]
      simp only [keyBlock,←Nat.mul_assoc]
    · rw [outside _ (by unfold keyWord leafSalt;omega) (Or.inr (by omega)),high_word_zero msg _ (by unfold keyWord leafSalt;omega) (by unfold keyWord leafSalt;omega)]
      apply BitVec.eq_of_getLsbD_eq;intro n hn
      simp [keyBlock,hn,show 192≤64*(j-1)+n by omega]
  · intro i _ nz;exact (nz rfl).elim

def fixedLeaf (o : Oracle) (s : MachineState) (i : Nat) :=
  ((plan i).foldl (fixedStep o) s).setPC (startPC (i+1))

def fixedScan (o : Oracle) : Nat → Nat → MachineState → MachineState
  | 0,_,s => s
  | n+1,i,s => fixedScan o n (i+1) (fixedLeaf o s i)

theorem fixed_leaf_run (o : Oracle) (s : MachineState) (i : Nat) :
    o.run (stepTrace s i)=pure (fixedLeaf o s i,opCalls (plan i)) := by
  rw [stepTrace,oracle_run_bind,fixed_ops,pure_bind];simp [oracle_run_pure,fixedLeaf]

theorem fixed_leaf_supported (o : Oracle) (s : MachineState) (i : Nat) :
    fixedLeaf o s i ∈ support (stepTrace s i) := by
  apply writer_support (o.world.withAddCost Oracle.callCost) _ (fixedLeaf o s i,opCalls (plan i))
  change (_,_)∈support (o.run (stepTrace s i))
  rw [fixed_leaf_run];simp

theorem fixed_scan_run (o : Oracle) (n i : Nat) (s : MachineState) (bound : i+n≤N) :
    o.run (scan n i s)=pure (fixedScan o n i s,Q (i+n)-Q i) := by
  induction n generalizing s i with
  | zero => simp [scan,fixedScan,oracle_run_pure]
  | succ n ih =>
    have h:=cumul i (by omega)
    have m:=monotone_counts (i+1) n (by omega)
    rw [scan,oracle_run_bind,fixed_leaf_run,pure_bind]
    dsimp only
    rw [ih (i+1) _ (by omega)]
    simp only [fixedScan,pure_bind]
    apply congrArg pure
    apply congrArg (Prod.mk _)
    change opCalls (plan i)+(Q ((i+1)+n)-Q (i+1))=Q (i+(n+1))-Q i
    rw [show i+(n+1)=(i+1)+n by omega];omega

theorem scan_content (o : Oracle) (k : Key) (msg : Message) (n i : Nat) (s : MachineState)
    (bound : i+n≤N) (r : Live s i) (good : Good o k msg (memoryView s) i) :
    Good o k msg (memoryView (fixedScan o n i s)) (i+n) := by
  induction n generalizing i s with
  | zero => exact good
  | succ n ih =>
    have hi : i<N:=by omega
    let idx : Index := ⟨i,hi⟩
    have next := fixed_packet_good o k msg s idx r.toPacketRegs good
    have live := step_live s i hi r _ (fixed_leaf_supported o s i)
    exact (show i+(n+1)=(i+1)+n by omega) ▸ ih (i+1) _ (by omega) live next

end TwoPermutationPrototype.Grouped
