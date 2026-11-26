import CommitGolfCandidate.ReconstructedHonestCallFlow
import CommitGolfCandidate.ReconstructedHonestFinishes
import CommitGolfCandidate.ReconstructedHonestCapFrame

namespace CommitGolfCandidate.Reconstruction.HonestCapPrices
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestFlow HonestCapStages HonestCuts
open CommitBlocks (addr)

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
attribute [local irreducible] ArtifactEncoding.decode

private def costs : ArtifactEncoding.Packed 1660 := (.join
    (.join
    (.join
    (.join
    (.join
    (.chunk 64 0)
    (.chunk 64 0))
    (.join
    (.chunk 64 0)
    (.chunk 64 0)))
    (.join
    (.join
    (.chunk 64 0)
    (.chunk 64 0))
    (.join
    (.chunk 64 0)
    (.chunk 64 0))))
    (.join
    (.join
    (.join
    (.chunk 64 0)
    (.chunk 64 0))
    (.join
    (.chunk 64 0)
    (.chunk 64 0)))
    (.join
    (.join
    (.chunk 64 0)
    (.chunk 64 0))
    (.join
    (.chunk 64 0)
    (.chunk 64 0)))))
    (.join
    (.join
    (.join
    (.join
    (.chunk 64 0)
    (.chunk 64 0))
    (.join
    (.chunk 64 0)
    (.chunk 64 0)))
    (.join
    (.join
    (.chunk 64 0)
    (.chunk 64 0))
    (.join
    (.chunk 64 6066096954567056458836701719602761072275015375355626912009309360450661957719214451097413165549326175978064302162743051065272488110724319489184111125207575313554162561920562997537849536953196827857514874077047556277124847378628608)
    (.chunk 64 13648603284034868570390807167896200834486524620802970423786128919113571450694263200143339978009956246944076447879262275726502263277136668408239975806518526535539842129163270884567026535237497942507944485003041269111335594319994895))))
    (.join
    (.chunk 64 1137468474257980800362809165664076615398509070281592566872141042227840582875107184042549080465086787691514467063677554058029287971657013085605414113208398606276298250542841060754165974372047677458515689087015589326962249854754851)
    (.chunk 60 15613316928291476241721639729035826527814108372518721847104274859486863541463784246463300695513463665668471042863659575912572428956460506310250498))))
private abbrev active := HonestBinaryRank.active costs
private abbrev rank := HonestBinaryRank.rank costs
private def zero (_ : Word) := false
private theorem ranked : Ranking (Artifact.submission.image .opening) active stops zero rank :=
  HonestBinaryRank.of_table _ Artifact.openingCode (Eq.refl (ArtifactEncoding.decode 32 _))
    (by decide) costs stops zero (by decide +kernel)

def Budget (s : MachineState) (coins : Bool) (bound : Nat) :=
  ∀ f r, r ∈ support (execute (Artifact.submission.image .opening) f s coins) → r.cycles ≤ bound

theorem segment (idx fee : Nat) (mem : (idx,fee) ∈ HonestCapFrame.prices) (s : MachineState)
    (coins : Bool) (pc : s.pc = addr idx) (tail : Nat) (boundary : ∀ t,
      Reaches (Artifact.submission.image .opening) coins stops s t → Budget t coins tail) :
    Budget s coins (fee+tail) := by
  have good : ∀ p ∈ HonestCapFrame.prices, active (addr p.1) = true ∧ rank (addr p.1) = p.2 := by
    intro p member
    simp only [HonestCapFrame.prices,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  obtain ⟨here,value⟩ := good _ mem
  intro f r run
  have b := HonestCuts.bounded ranked s coins tail (pc ▸ here) (by intro impossible; cases impossible) boundary f r run
  rwa [pc,value] at b

theorem mono {s : MachineState} {coins : Bool} {a b : Nat} (le : a ≤ b) (h : Budget s coins a) : Budget s coins b :=
  fun f r run => (h f r run).trans le

theorem segment_success {good : MachineState→Prop} (idx fee : Nat) (mem : (idx,fee)∈HonestCapFrame.prices)
    (s : MachineState) (coins : Bool) (pc : s.pc=addr idx) (boundary : ∀ t,
      Reaches (Artifact.submission.image .opening) coins stops s t →
        HonestFinishes.SuccessPost (Artifact.submission.image .opening) coins good t) :
    HonestFinishes.SuccessPost (Artifact.submission.image .opening) coins good s := by
  apply HonestFinishes.from_cut ranked s coins _ (by intro h; cases h) boundary
  rw [pc]
  simp only [HonestCapFrame.prices,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> decide +kernel

theorem segment_calls (idx fee : Nat) (mem : (idx,fee)∈HonestCapFrame.prices) (s : MachineState)
    (coins : Bool) (pc : s.pc=addr idx) (tail : Nat) (boundary : ∀ t,
      Reaches (Artifact.submission.image .opening) coins stops s t →
        HonestCallFlow.Calls (Artifact.submission.image .opening) t coins tail) :
    HonestCallFlow.Calls (Artifact.submission.image .opening) s coins tail := by
  have entry : active s.pc=true := by
    rw [pc]
    simp only [HonestCapFrame.prices,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> decide +kernel
  simpa only [Nat.zero_add] using HonestCallFlow.bounded _ Artifact.openingCode costs (Eq.refl (ArtifactEncoding.decode 32 _))
    (by decide) stops zero (fun _ => 0) ranked (by decide +kernel) s entry (by intro h; cases h) coins tail boundary

end CommitGolfCandidate.Reconstruction.HonestCapPrices
