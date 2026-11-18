import CommitGolfCandidate.QuartetManifest
import CommitGolfCandidate.Execution
import CommitGolfCandidate.QuartetCommitRanges
import CommitGolfCandidate.TwoPermutationCommitSetup
import CommitGolfCandidate.TwoPermutationManifest
import CommitGolfCandidate.TwoPermutationPackedParents
import CommitGolfCandidate.QuartetCommitLeafSpill
import CommitGolfCandidate.TwoPermutationInputWords
namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate (initial_input_word initial_input_byte inputByte read_buffer_memory_congr read_serialized_slice write_bits_read_outside write_bits_byte splitBlocks)
set_option maxRecDepth 8192
set_option maxHeartbeats 900000
attribute [local irreducible] writeBits
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

theorem initial_padding (msg : Message) (g k : Nat) (hg : g<4194304) (hk : k<9) :
    memoryView (QuartetArtifact.submission.initialState .commit msg) (qSource g+k)=0 := by
  let atWord := 8*(qSource g+k)
  change (QuartetArtifact.submission.initialState .commit msg).getMem (BitVec.ofNat 64 atWord)=0
  rw [initial_input_word QuartetArtifact.submission .commit msg atWord (by dsimp [atWord,qSource];split_ifs <;> omega)]
  have byte (j : Nat) (hj : j<8) : inputByte QuartetArtifact.submission .commit msg (atWord+j)=0 := by
    have gone : ¬(4096≤atWord+j ∧ atWord+j<4096+LENGTH*(LEAF_SIZE/8)) := by
      change ¬(_ ∧ atWord+j<4096+16777216*256);dsimp [atWord,qSource];split_ifs <;> omega
    have base : QuartetArtifact.submission.layout.message=4096 := rfl
    have data : (QuartetArtifact.submission.image .commit).data=[] := rfl
    simp only [inputByte,Submission.inputBuffers,List.find?_cons,messageBuffer,base,gone,
      decide_false,Bool.false_eq_true,ite_false,List.find?_nil,data]
    simp
  have zero : (∑ j ∈ Finset.range 8, (inputByte QuartetArtifact.submission .commit msg (atWord+j)).toNat * 2^(8*j))=0 := by
    apply Finset.sum_eq_zero;intro j hj;rw [byte j (Finset.mem_range.mp hj)];simp
  rw [zero];rfl

/-- What the leaf loop needs from memory at its entry: the message words, the salt words and the
zero headers of the quartet source blocks. Any ready state with these facts and `StartLeafRegs`
gives the same commitment (the chain-salt generator produces such a state). -/
structure BodyContent (s : MachineState) (msg : Message) (salts : CompleteSaltTape) : Prop where
  messages : ∀ i : Index, window (memoryView s) (leafStart i.val+5) = messageWords msg i
  nonces : ∀ i : Index, window (memoryView s) (qSalt i.val) = saltWords (salts i)
  padding : ∀ g<4194304, ∀ k<9, memoryView s (qSource g+k) = 0

end TwoPermutationPrototype.QuartetCommit
