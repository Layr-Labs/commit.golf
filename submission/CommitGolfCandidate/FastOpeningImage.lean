import CommitGolfCandidate.FastOpeningPath
/-! Literal unrolled opening image and checked fetches for every repeated body
instruction. Setup and outer-loop targets use the actual relocated addresses. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def fastHead : List (BitVec 32) := [394387, 429075, 494739, 527763, 16779703, 1073742647, 6588723, 50331759, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 1477282915, 801283, 1708819, 21168947, 3347219, 6884275, 766723, 7122979, 9155331, 7124003, 17543939, 7125027, 834595, 34376851, 20580915, 25169427, 12583023, 19, 19]
def fastBody : List (BitVec 32) := [1721235, 5477267, 7637939, 766723, 7122979, 9155331, 7124003, 17543939, 7125027, 25932547, 7126051, 34376851, 1726995, 4294839827]
def fastTail : List (BitVec 32) := [9178131, 4294806931, 2785908963, 1090291123, 1049235, 1299, 115]
def fastImage : Image := ⟨fastHead ++ (List.replicate 24 fastBody).flatten ++ fastTail,[]⟩
theorem fast_path_fetched (level : Nat) (bound : level<24) :
    UnrolledPathFetched fastImage (BitVec.ofNat 64 (4248+56*level)) := by
  intro s i hi pc
  have pcNat : s.pc.toNat=4248+56*level+4*i := by
    rw [pc,←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    omega
  rw [fetch,pcNat,if_pos (by omega)]
  have index : (4248+56*level+4*i-4096)/4=38+14*level+i := by omega
  rw [index]
  interval_cases level <;> interval_cases i <;> rfl

theorem fast_fetch (s : MachineState) (index : Nat) (instruction : Instr)
    (bound : index<381) (pc : s.pc=BitVec.ofNat 64 (4096+4*index))
    (decoded : (fastImage.code[index]?).bind decodeInstruction=some (.base instruction)) :
    fetch fastImage s=some (.base instruction) := by
  have pcNat : s.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt];omega
  rw [fetch,pcNat,if_pos (by omega)]
  have idx : (4096+4*index-4096)/4=index := by omega
  rw [idx]
  cases h : fastImage.code[index]? with
  | none => simp [h] at decoded
  | some word => simpa [h] using decoded
end CommitGolfCandidate
