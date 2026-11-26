import CommitGolfCandidate.ReconstructedCheckInitLower

namespace CommitGolfCandidate.Reconstruction.CheckRecordSpec
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckLayout CheckRecordABI CheckWalkValues
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 16000
set_option maxHeartbeats 1400000
set_option exponentiation.threshold 2048
abbrev W:=BitVec.ofNat 64

def cursor (i : Nat) := 3633*i

def leaf (o : Oracle) (idx : Index) (stream c : Nat) (msg : Words 32) : Binding.Digest :=
  unpack (leafDigestW 240 (o.permutation (CheckLeafCall.request o idx (CheckRecordHeader.salt stream c) msg 1)))

def start (o : Oracle) (idx : Index) (stream c : Nat) (msg : Words 32) : View :=
  ⟨c+222,CheckRecordHeader.header stream c,leaf o idx stream c msg⟩

def lower (o : Oracle) (idx : Index) (stream c : Nat) (msg : Words 32) :=
  CheckWalk.evaluate o idx stream 15 (start o idx stream c msg)

def rows (o : Oracle) (idx : Index) (stream c : Nat) (msg : Words 32) :=
  CheckLeaf.rows o idx (CheckRecordHeader.salt stream c) msg ++ (lower o idx stream c msg).2

theorem leafCanonical (b : TwoPermutationPrototype.Sampling.Block) : Canonical 24 (unpack (leafDigestW 240 b)) := by
  change ((leafDigestW 240 b).extractLsb' 192 64).toNat < radix 24
  have small : (leafDigestW 240 b).toNat < 2^240 := by
    change ((outputDigest b).toNat % 2^240) % 2^256 < 2^240
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (Nat.two_pow_pos 240))
  change ((leafDigestW 240 b).toNat >>> 192) % 2^64 < radix 24
  rw [Nat.shiftRight_eq_div_pow,show radix 24=2^48 by decide]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)

theorem boundedHead (stream c : Nat) : bounded (CheckRecordHeader.header stream c) := by
  unfold bounded CheckRecordHeader.header HonestDivision.fromFields
  intro x hx;simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with eq|eq|eq|eq <;> subst x <;> exact Nat.mod_lt _ (by decide)

theorem ready (o : Oracle) (idx : Index) (stream i : Nat) (msg : Words 32) (lim : i<2^24) :
    Ready (start o idx stream (cursor i) msg) 24 :=
  ⟨by change 3633*i+222+240*(24-9)≤70000000000;omega,boundedHead stream (cursor i),leafCanonical _⟩

def advance : Nat→Nat | 0=>0 | k+1=>CheckMixed.width (CheckWalk.idx15 k)+advance k

theorem moves (o : Oracle) (idx : Index) (bits k : Nat) (v : View) :
    (CheckWalk.evaluate o idx bits k v).1.cursor=v.cursor+advance k := by
  induction k generalizing v with
  | zero=>exact (Nat.add_zero _).symm
  | succ k ih=>rw [CheckWalk.evaluate,ih];change v.cursor+CheckMixed.width _+advance k=v.cursor+(_+_);omega

theorem next (o : Oracle) (idx : Index) (stream i : Nat) (msg : Words 32) :
    (lower o idx stream (cursor i) msg).1.cursor=cursor (i+1) := by
  rw [lower,moves,show advance 15=3411 by decide];change 3633*i+222+3411=3633*(i+1);omega

theorem ordinal_limit (input : CheckInput) (i : Fin input.positions.card) : i.val<2^24 := by
  have bound : input.positions.card≤2^24:=by simpa only [Fintype.card_fin,LENGTH,LOG_LENGTH] using Finset.card_le_univ input.positions
  exact Nat.lt_of_lt_of_le i.isLt bound

theorem contents (s : MachineState) (input : CheckInput) (i : Fin input.positions.card) (p : Persistent s input)
    (regs : Registers s i.val (cursor i)) :
    CheckRecordStart.Contents (CheckRecordHeader.model s) 8589934466 i (position input i).val (entryWords (input.values (position input i))) := by
  have bound:=ordinal_limit input i
  refine ⟨⟨by decide,bound,regs.fp,regs.ordinal,p.indexPtr,p.valuesPtr⟩,p.indices i,p.marker,p.values i,regs.beginCopy,regs.endCopy,?_⟩
  right;unfold CheckEntry.valuesBase;omega

end CommitGolfCandidate.Reconstruction.CheckRecordSpec
