import CommitGolfCandidate.Compact.SlimPath
/-! Actual 357-word opening image. The per-position counter setup is skipped, and the counter-free path falls directly into the outer latch. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def noInitHead : List (BitVec 32) := [394387, 429075, 494739, 527763, 16779703, 1073742647, 6588723, 50331759, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 1376619619, 801283, 1708819, 21168947, 3347219, 6884275, 766723, 7122979, 9155331, 7124003, 17543939, 7125027, 834595, 25988243, 20580915, 16777327, 19, 19, 19]
def noInitBody : List (BitVec 32) := [1721235, 5477267, 7637939, 766723, 7122979, 9155331, 7124003, 17543939, 7125027, 25932547, 7126051, 34376851, 1726995]
def noInitTail : List (BitVec 32) := [9178131, 4294806931, 2886572259, 1090291123, 1049235, 1299, 115]
def noInitImage : Image := ⟨noInitHead ++ (List.replicate 24 noInitBody).flatten ++ noInitTail,[]⟩
theorem noInit_path_fetched (level : Nat) (bound : level<24) :
    SlimPathFetched noInitImage (BitVec.ofNat 64 (4248+52*level)) := by
  intro s i hi pc
  have pcNat : s.pc.toNat=4248+52*level+4*i := by
    rw [pc,←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    omega
  rw [fetch,pcNat,if_pos (by omega)]
  have index : (4248+52*level+4*i-4096)/4=38+13*level+i := by omega
  rw [index]
  interval_cases level <;> interval_cases i <;> rfl

theorem noInit_fetch (s : MachineState) (index : Nat) (instruction : Instr)
    (bound : index<357) (pc : s.pc=BitVec.ofNat 64 (4096+4*index))
    (decoded : (noInitImage.code[index]?).bind decodeInstruction=some (.base instruction)) :
    fetch noInitImage s=some (.base instruction) := by
  have pcNat : s.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt];omega
  rw [fetch,pcNat,if_pos (by omega)]
  have idx : (4096+4*index-4096)/4=index := by omega
  rw [idx]
  cases h : noInitImage.code[index]? with
  | none => simp [h] at decoded
  | some word => simpa [h] using decoded
end CommitGolfCandidate.Compact
