import CommitGolfCandidate.QuartetCommitSetup
import CommitGolfCandidate.QuartetCommitLeafSpill
import CommitGolfCandidate.TwoPermutationInputWords
namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate (initial_input_word initial_input_byte inputByte read_buffer_memory_congr read_serialized_slice write_bits_read_outside write_bits_byte splitBlocks)
set_option maxRecDepth 8192
set_option maxHeartbeats 900000
attribute [local irreducible] qReady writeBits
theorem wide_message_byte (s : Submission) (messageBase : s.layout.message=4096) (msg : Message) (i : Index) (j : Nat) (hj : j<256) :
    (s.initialState .commit msg).getByte (BitVec.ofNat 64 (4096+256*i.val+j)) = (msg i).extractLsb' (8*j) 8 := by
  have n : i.val<2^24 := i.isLt
  rw [initial_input_byte s .commit msg _ (by omega)]
  have selected : 4096 ≤ 4096+256*i.val+j ∧ 4096+256*i.val+j < 4096+LENGTH*(LEAF_SIZE/8) := by
    change _ ∧ _ < 4096+16777216*256;omega
  simp only [inputByte,Submission.inputBuffers,List.find?_cons,messageBuffer,messageBase,
    selected,and_self,decide_true]
  have quotient : (4096+256*i.val+j-4096)/(LEAF_SIZE/8)=i.val := by change _/256=_;omega
  have remainder : (4096+256*i.val+j-4096)%(LEAF_SIZE/8)=j := by change _%256=_;omega
  simp only [quotient,remainder,i.isLt,dite_true]

theorem wide_ready_messages (candidate : Submission) (messageBase : candidate.layout.message=4096) (msg : Message)
    (packed : BitVec (128*LENGTH)) (i : Index) :
    window (memoryView (qReady (candidate.initialState .commit msg) packed)) (leafStart i.val+5) =
      messageWords msg i := by
  let init := candidate.initialState .commit msg
  let ready := qReady init packed
  funext k
  change memoryView ready (leafStart i.val+5+k.val)=_
  rw [←read_word,read_buffer_memory_congr _ _ (q_ready_mem init packed)]
  have hi : i.val<2^24 := i.isLt
  have hk := k.isLt
  have sep := write_bits_read_outside init packed (8*qSalt 0) (8*(leafStart i.val+5+k.val)) 8
    (by change 6979325984+268435456≤2^64;decide) (by unfold leafStart;omega)
    (by left;unfold leafStart qSalt;omega)
  rw [wordAddress,sep]
  have slice := read_serialized_slice init (msg i) (8*(leafStart i.val+5+k.val)) (8*k.val) 8 (by
    intro j hj
    rw [show 8*(leafStart i.val+5+k.val)+j=4096+256*i.val+(8*k.val+j) by unfold leafStart;omega]
    exact wide_message_byte candidate messageBase msg i (8*k.val+j) (by omega))
  simpa only [messageWords,←Nat.mul_assoc] using slice


theorem ready_salts (s : MachineState) (packed : BitVec (128*LENGTH)) (i : Index) :
    window (memoryView (qReady s packed)) (qSalt i.val) = saltWords (splitBlocks 128 LENGTH packed i) := by
  funext k
  change memoryView (qReady s packed) (qSalt i.val+k.val)=_
  rw [←read_word,read_buffer_memory_congr _ _ (q_ready_mem s packed)]
  let offset := 16*i.val+8*k.val
  have iBound : i.val<16777216 := i.isLt
  have kBound := k.isLt
  have bound : (128*LENGTH+7)/8 ≤ 2^64 := by decide
  have slice := read_serialized_slice (writeBits s (wordAddress (qSalt 0)) packed) packed
    (8*(qSalt i.val+k.val)) offset 8 (by
      intro j hj
      have inside : offset+j < (128*LENGTH+7)/8 := by change offset+j < 268435456;dsimp [offset];omega
      have byte := write_bits_byte s (wordAddress (qSalt 0)) packed (offset+j) inside bound
      simpa only [wordAddress,←BitVec.ofNat_add,
        show 8*qSalt 0+(offset+j)=8*(qSalt i.val+k.val)+j by dsimp [offset,qSalt];omega] using byte)
  rw [slice]
  apply BitVec.eq_of_getLsbD_eq
  intro bit within
  have small : 64*k.val+bit < 128 := by omega
  have eq : 8*offset+bit=128*i.val+(64*k.val+bit) := by dsimp [offset];omega
  simp [saltWords,splitBlocks,within,small,eq,←Nat.add_assoc]


theorem initial_padding (msg : Message) (g k : Nat) (hg : g<4194304) (hk : k<9) :
    memoryView (Artifact.submission.initialState .commit msg) (qSource g+k)=0 := by
  let atWord := 8*(qSource g+k)
  change (Artifact.submission.initialState .commit msg).getMem (BitVec.ofNat 64 atWord)=0
  rw [initial_input_word Artifact.submission .commit msg atWord (by dsimp [atWord,qSource];omega)]
  have byte (j : Nat) (hj : j<8) : inputByte Artifact.submission .commit msg (atWord+j)=0 := by
    have gone : ¬(4096≤atWord+j ∧ atWord+j<4096+LENGTH*(LEAF_SIZE/8)) := by
      change ¬(_ ∧ atWord+j<4096+16777216*256);dsimp [atWord,qSource];omega
    have base : Artifact.submission.layout.message=4096 := rfl
    have data : (Artifact.submission.image .commit).data=[] := rfl
    simp only [inputByte,Submission.inputBuffers,List.find?_cons,messageBuffer,base,gone,
      decide_false,Bool.false_eq_true,ite_false,List.find?_nil,data]
    simp
  have zero : (∑ j ∈ Finset.range 8, (inputByte Artifact.submission .commit msg (atWord+j)).toNat * 2^(8*j))=0 := by
    apply Finset.sum_eq_zero;intro j hj;rw [byte j (Finset.mem_range.mp hj)];simp
  rw [zero];rfl

theorem ready_padding (msg : Message) (packed : BitVec (128*LENGTH)) (g : Nat) (hg : g<4194304) (k : Nat) (hk : k<9) :
    memoryView (qReady (Artifact.submission.initialState .commit msg) packed) (qSource g+k)=0 := by
  let s := Artifact.submission.initialState .commit msg
  change memoryView (qReady s packed) _=0
  rw [←read_word,read_buffer_memory_congr _ _ (q_ready_mem s packed)]
  have sep:=write_bits_read_outside s packed (8*qSalt 0) (8*(qSource g+k)) 8
    (by decide) (by unfold qSource;omega) (by left;unfold qSource qSalt;omega)
  rw [wordAddress,sep,read_word];exact initial_padding msg g k hg hk

theorem ready_leaf_reference (oracle : Oracle) (msg : Message) (packed : BitVec (128*LENGTH)) (i : Index) :
    outputDigest (QuartetLeaves.pinnedFinalReply oracle (memoryView (qReady (Artifact.submission.initialState .commit msg) packed)) i.val) =
      pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) msg (splitBlocks 128 LENGTH packed) i := by
  unfold QuartetLeaves.pinnedFinalReply
  rw [wide_ready_messages Artifact.submission rfl msg packed i,ready_salts _ packed i]
  simp only [pinnedFullLeafDigests,pinnedLeafDigest,pinnedFirstRow,pinnedSecondRow,QuartetLeaves.pinned_typed_words]
  rfl
end TwoPermutationPrototype.QuartetCommit
