import CommitGolfCandidate.ReconstructedCheckLoader
import CommitGolfCandidate.ReconstructedHonestCopy

namespace CommitGolfCandidate.Reconstruction.CheckCopy
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecordABI
open Binding.Machine CheckRecorded CheckLoader
open CommitBlocks (addr)
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000
attribute [local irreducible] ArtifactEncoding.decode execute

def body (input : CheckInput) := HonestCopy.ready true (initial input)

structure Copy (input : CheckInput) : Prop where
  pc : (body input).pc=addr 24
  returnPC : (body input).getReg .x1=addr 20
  count : (body input).getReg .x10=W input.positions.card
  length : (body input).getReg .x11=W input.proof.length
  stack : (body input).getReg .x2=W CheckLayout.fp
  image : ∀ j<126,(body input).getMem (W (2097152+8*j))=(initial input).getMem (W (68719475728+8*j))
  frame : ∀ a,2098160≤a → a<2^36 → (body input).getMem (W a)=(initial input).getMem (W a)

theorem start (o : Oracle) (input : CheckInput) (pos : 0 < input.positions.card) :
    Segment o 767 (initial input) (body input) [] ∧ Copy input := by
  let s := initial input
  have card := positions_card_bound input.positions
  have nonzero : s.getReg .x16≠0 := by
    intro h;have eq := congrArg BitVec.toNat h
    change input.positions.card%2^64=0 at eq;omega
  have sp : s.getReg .x2=W 68719475728 := by
    change W (dataBase (Artifact.submission.image .check))=_;rw [image_base]
  have launch (fuel : Nat) := HonestCopy.enter_body true s rfl nonzero sp fuel false
  obtain ⟨_,pc,ra,co,len,st,im,fr⟩ := launch 0
  constructor
  · refine ⟨767,fun fuel => ?_⟩
    have step := Binding.Machine.step_ordinary o s (body input) 767 767 (fun f => (launch f).1) fuel
    simpa only [List.length_nil,List.nil_append,Nat.zero_add] using step
  · refine ⟨pc,ra,co,len,st.trans sp,im,?_⟩
    intro a lo hi
    exact fr (W a) (by
      intro j hj eq
      change j<126 at hj
      have number := congrArg BitVec.toNat eq
      change a%2^64=(2097152+8*j)%2^64 at number;omega)

end CommitGolfCandidate.Reconstruction.CheckCopy
