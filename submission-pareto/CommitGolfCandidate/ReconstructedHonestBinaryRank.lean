import CommitGolfCandidate.ReconstructedHonestFlow
import CommitGolfCandidate.ReconstructedCommitBlocks

namespace CommitGolfCandidate.Reconstruction.HonestBinaryRank
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestFlow
open CommitBlocks (addr)

def index (pc : Word) := (pc.toNat-4096)/4
def rank {n : Nat} (costs : ArtifactEncoding.Packed n) (pc : Word) : Nat :=
  if h : index pc < n then (costs.get 12 ⟨index pc,h⟩).toNat else 0
def active {n : Nat} (costs : ArtifactEncoding.Packed n) (pc : Word) :=
  pc == addr (index pc) && decide (0 < rank costs pc)
private def isCall : Instruction → Bool
  | .base .ECALL => true
  | _ => false

def check {n : Nat} (costs : ArtifactEncoding.Packed n) (cut zero : Word → Bool) (i : Nat) (raw : BitVec 32) : Bool :=
  let pc := addr i
  if active costs pc then
    match decodeInstruction raw with
    | none => false
    | some op => direct op && (!isCall op || zero pc) && decide (price op ≤ rank costs pc) &&
      (targets pc op).all fun target => cut target ||
        (active costs target && decide (rank costs target + price op ≤ rank costs pc) && (!zero target || raw == 0x293))
  else true

theorem of_table {n : Nat} (image : Image) (packed : ArtifactEncoding.Packed n)
    (same : image.code = ArtifactEncoding.decode 32 packed) (small : 4096+4*n < 2^64)
    (costs : ArtifactEncoding.Packed n) (cut zero : Word → Bool)
    (checked : CommitBlocks.allWords packed 0 (check costs cut zero) = true) :
    Ranking image (active costs) cut zero (rank costs) := by
  constructor
  intro s hs
  have parts := hs
  simp only [active,Bool.and_eq_true] at parts
  obtain ⟨hpc,positive⟩ := parts
  have pc : s.pc = addr (index s.pc) := beq_iff_eq.mp hpc
  have pos : 0 < rank costs s.pc := of_decide_eq_true positive
  have inside : index s.pc < n := by
    by_contra h
    simp only [rank,dite_eq_right h,Nat.lt_irrefl] at pos
  let raw := packed.get 32 ⟨index s.pc,inside⟩
  have receipt : check costs cut zero (index s.pc) raw = true := by
    simpa only [Nat.zero_add] using CommitBlocks.checked_word _ _ _ checked ⟨index s.pc,inside⟩
  have read := fetch_packed image packed same (index s.pc) inside (by omega) s pc
  change fetch _ s = decodeInstruction raw at read
  unfold check at receipt
  simp only [←pc,hs,ite_true] at receipt
  cases decoded : decodeInstruction raw with
  | none => simp [decoded] at receipt
  | some op =>
    simp only [decoded,Bool.and_eq_true,decide_eq_true_eq] at receipt
    obtain ⟨⟨⟨dir,mode⟩,fee⟩,edges⟩ := receipt
    refine ⟨op,read.trans decoded,dir,?_,fee,?_⟩
    · rintro rfl; exact mode
    · intro target mem
      have edge := List.all_eq_true.mp edges target mem
      simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',beq_iff_eq] at edge
      rcases edge with stop | ⟨⟨act,drops⟩,extra⟩
      · exact Or.inl stop
      · refine Or.inr ⟨act,drops,?_⟩
        intro marked
        rcases extra with clean | rawEq
        · simp [marked] at clean
        · rw [rawEq] at decoded
          exact (Option.some.inj decoded).symm

end CommitGolfCandidate.Reconstruction.HonestBinaryRank
