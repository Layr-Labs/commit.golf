import CommitGolfCandidate.TruncFetch
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000

abbrev checkOld := PairCap.submission.image .check
def untouched (i : Nat) := i<409 ∧ i≠6 ∧ i≠15 ∧ i≠277 ∧ i≠281 ∧ i≠359 ∧ i≠389

theorem oldCheckWord (i : Nat) (h : untouched i) : (submission.image .check).code[i]?=checkOld.code[i]? := by
  rcases h with ⟨bd,a,b,c,d,e,f⟩
  change ((((((((checkOld.code.set 6 _).set 15 _).set 277 _).set 281 _).set 359 _).set 389 _) ++ _)[i]?)=_
  rw [List.getElem?_append_left (by simpa only [List.length_set,show checkOld.code.length=409 by rfl] using bd)]
  repeat rw [List.getElem?_set_ne (by omega)]

theorem sharedFetch (s : MachineState) (i : Nat) (op : Instr) (hi : untouched i)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*i)) (d : (checkOld.code[i]?).bind decodeInstruction=some (.base op)) :
    fetch (submission.image .check) s=some (.base op) :=
  fetchAt _ s i op (by have :=hi.1;omega) pc (by rw [oldCheckWord i hi];exact d)

theorem originalOpenWord (i : Nat) (h : i<141) : (submission.image .opening).code[i]?=(PairCap.submission.image .opening).code[i]? := by
  change ((((PairCap.submission.image .opening).code.set 141 _) ++ _)[i]?)=_
  rw [List.getElem?_append_left (by simp only [List.length_set,show (PairCap.submission.image .opening).code.length=142 by rfl];omega),
      List.getElem?_set_ne (by omega)]

theorem openingFetch (s : MachineState) (i : Nat) (op : Instr) (hi : i<141)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*i)) (d : (((PairCap.submission.image .opening).code[i]?).bind decodeInstruction)=some (.base op)) :
    fetch (submission.image .opening) s=some (.base op) :=
  fetchAt _ s i op (by omega) pc (by rw [originalOpenWord i hi];exact d)

end CommitGolfCandidate.Trunc
