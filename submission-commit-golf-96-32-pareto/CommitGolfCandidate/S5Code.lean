import CommitGolfCandidate.S5PairDraw
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 20000

deriving instance DecidableEq for Instruction

abbrev image (p : Program) := Artifact.submission.image p
def words : Program→Nat
  | .commit=>18492
  | .opening=>993
  | .check=>2336

def atWord (p : Program) (n : Fin (words p)) : BitVec 32 :=
  match p with
  | .commit=>Artifact.commitCode.get 32 n
  | .opening=>Artifact.openingCode.get 32 n
  | .check=>Artifact.checkCode.get 32 n

private theorem get_code {n : Nat} (a : ArtifactEncoding.Packed n) (i : Fin n) :
    (ArtifactEncoding.decode 32 a)[i.val]?=some (a.get 32 i) := by
  simp only [ArtifactEncoding.decode,List.getElem?_ofFn,dif_pos i.isLt]

attribute [local irreducible] ArtifactEncoding.decode Artifact.commitCode Artifact.openingCode Artifact.checkCode in
theorem word_delivered (p : Program) (n : Fin (words p)) :
    (image p).code[n.val]?=some (atWord p n) := by
  cases p with
  | commit=>exact get_code Artifact.commitCode n
  | opening=>exact get_code Artifact.openingCode n
  | check=>exact get_code Artifact.checkCode n

def Site (p : Program) (n : Nat) (op : Instr) :=
  ∀ s : MachineState, s.pc=pcAt n → fetch (image p) s=some (.base op)

theorem site {p : Program} {n : Nat} {op : Instr} (h : n<words p)
    (code : decodeInstruction (atWord p ⟨n,h⟩)=some (.base op)) : Site p n op := by
  intro s pc
  have below : n<18493 := by cases p <;> simp only [words] at h <;> omega
  have bound : 4096+4*n<2^64:=by omega
  simp only [fetch,pc,pcAt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound]
  rw [if_pos (by constructor <;> omega)]
  rw [Nat.add_sub_cancel_left,Nat.mul_div_cancel_left _ (by decide : 0<4)]
  have read : (image p).code[n]?=some (atWord p ⟨n,h⟩) := word_delivered p ⟨n,h⟩
  rw [read];exact code

theorem pc_succ (n : Nat) : pcAt n+4=pcAt (n+1) := by
  change BitVec.ofNat 64 (4096+4*n)+BitVec.ofNat 64 4=_
  rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);omega

def straight (op : Instr) := ∀ s, ordinaryStep s (.base op) = some (execInstrBr s op) ∧
  instructionCycles (.base op) = 1 ∧ (execInstrBr s op).pc = s.pc+4

theorem execute_linear (p : Program) (coins : Bool) (ops : List Instr) (n : Nat) (s : MachineState) (fuel : Nat)
    (pc : s.pc = pcAt n) (plain : ∀ op ∈ ops, straight op)
    (code : ∀ i (hi : i < ops.length), Site p (n+i) ops[i]) :
    execute (image p) (fuel+ops.length) s coins =
      (do let r ← execute (image p) fuel (ops.foldl execInstrBr s) coins
          return r.charge ops.length 0) := by
  induction ops generalizing n s with
  | nil => simp [Execution.charge]
  | cons op ops ih =>
    obtain ⟨step,cost,inc⟩ := plain op (List.mem_cons_self ..) s
    have next := ih (n+1) (execInstrBr s op) (by rw [inc,pc,pc_succ])
      (fun o h => plain o (List.mem_cons_of_mem _ h))
      (fun i hi => by
        rw [show n+1+i = n+(i+1) by omega]
        exact code (i+1) (by simp; omega))
    have fetch : fetch (image p) s = some (.base op) := code 0 (by simp) s (by simpa using pc)
    simp only [List.length_cons, List.foldl_cons, ← Nat.add_assoc]
    rw [execute_ordinary_step _ _ _ _ _ _ fetch step, next, cost]
    simp [Execution.charge, ← Nat.add_assoc, Nat.add_comm 1 ops.length]

end CommitGolfCandidate.S5Machine
