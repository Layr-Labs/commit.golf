import CommitGolf.Statements

namespace CommitGolfCandidate.Reconstruction
open CommitGolf CommitGolf.Riscv

def sizes : Sizes := ⟨1610612736, 8355061248⟩
def layout : Layout := ⟨4096, 4294971392, 4294971424, 5905584160, 6039801952, 10334769248⟩
def fuel : Program → Nat
  | .commit => 1073741824
  | .opening => 68719476736
  | .check => 274877906944

private theorem buffers_end :
    ∀ b ∈ layout.buffers sizes, b.1 % 8 = 0 ∧ b.1 + b.2 ≤ 18689830496 := by decide

private theorem buffers_disjoint : (layout.buffers sizes).Pairwise DisjointBuffers := by decide

/-- Applies to any three delivered images that meet the verifier's strict byte-size limit.
The maximum size includes embedded data as well as instructions. -/
theorem admission_for_images (s : Submission) (hs : s.sizes = sizes)
    (hl : s.layout = layout) (hf : s.steps = fuel)
    (small : ∀ p, (s.image p).byteSize < MAX_PROGRAM_BYTES) : s.Admission := by
  intro p
  rw [hs, hl, hf]
  have hi := small p
  have hd : (s.image p).data.length < 2 ^ 20 := by
    change 4 * _ + _ < 2 ^ 20 at hi
    omega
  have base : 18689830496 ≤ dataBase (s.image p) := by
    unfold dataBase MEMORY_BYTES
    omega
  refine ⟨⟨hi, ⟨?_, buffers_disjoint⟩⟩, ?_⟩
  · intro b hb
    exact ⟨(buffers_end b hb).1, (buffers_end b hb).2.trans base⟩
  · cases p <;> decide

end CommitGolfCandidate.Reconstruction
