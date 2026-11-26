import CommitGolfCandidate.TruncImage
import CommitGolfCandidate.CommitLeaf
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
theorem fetchAt (im : Image) (s : MachineState) (i : Nat) (op : Instr) (small : i<2048)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*i)) (decoded : (im.code[i]?).bind decodeInstruction=some (.base op)) :
    fetch im s=some (.base op) := by
  have pn : s.pc.toNat=4096+4*i := by rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt];omega
  rw [fetch,pn,if_pos (by omega),show (4096+4*i-4096)/4=i by omega]
  cases eqn : im.code[i]? <;> simpa [eqn] using decoded

private abbrev oldCommit := (CommitGolfCandidate.submission.image .commit).code
theorem originalWord (i : Nat) (hi : i<796) (a : i≠592) (b : i≠691) (c : i≠692) :
    (submission.image .commit).code[i]?=oldCommit[i]? := by
  change ((List.set (List.set (List.set oldCommit 592 _) 691 _) 692 _) ++ _)[i]?=_
  rw [List.getElem?_append_left (by simpa only [List.length_set,show oldCommit.length=796 from rfl] using hi)]
  rw [List.getElem?_set_ne (by omega),List.getElem?_set_ne (by omega),List.getElem?_set_ne (by omega)]

theorem prefixFetch (s : MachineState) (i : Nat) (op : Instr) (hi : i<592)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*i)) (d : (oldCommit[i]?).bind decodeInstruction=some (.base op)) :
    fetch (submission.image .commit) s=some (.base op) :=
  fetchAt _ s i op (by omega) pc (by rw [originalWord i (by omega) (by omega) (by omega) (by omega)];exact d)
end CommitGolfCandidate.Trunc
