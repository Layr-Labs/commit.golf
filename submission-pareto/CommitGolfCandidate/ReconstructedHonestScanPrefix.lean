import CommitGolfCandidate.ReconstructedHonestCapSpan
import CommitGolfCandidate.ReconstructedHonestFlagState

namespace CommitGolfCandidate.Reconstruction.HonestScanBytes
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestCapStages HonestCapState
open HonestCapTables (scratch w)
open CommitBlocks (addr)

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
attribute [local irreducible] ArtifactEncoding.decode

private def words : List (Nat × Instr) := [(1470,.LBU .x14 .x23 0),(1471,.LBU .x15 .x16 0),
  (1472,.OR .x6 .x15 .x14),(1473,.BEQ .x6 .x0 8),(1474,.SB .x24 .x11 0)]

private theorem read_at (i : Fin 1660) : HonestBlocks.readOp Artifact.openingCode (addr i.val) =
    decodeInstruction (Artifact.openingCode.get 32 i) := by
  have bound := i.isLt
  have exactIdx : HonestBinaryRank.index (addr i.val) = i.val := by
    unfold HonestBinaryRank.index addr
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  unfold HonestBlocks.readOp
  simp only [exactIdx,beq_self_eq_true,ite_true,dite_eq_left bound]

private theorem words_read (i : Nat) (op : Instr) (h : (i,op)∈words) :
    HonestBlocks.readOp Artifact.openingCode (addr i)=some (.base op) := by
  simp only [words,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h
  · rw [read_at (i:=⟨1470,by decide⟩),show Artifact.openingCode.get 32 ⟨1470,by decide⟩=0xbc703 by decide +kernel]; rfl
  · rw [read_at (i:=⟨1471,by decide⟩),show Artifact.openingCode.get 32 ⟨1471,by decide⟩=0x84783 by decide +kernel]; rfl
  · rw [read_at (i:=⟨1472,by decide⟩),show Artifact.openingCode.get 32 ⟨1472,by decide⟩=0xe7e333 by decide +kernel]; rfl
  · rw [read_at (i:=⟨1473,by decide⟩),show Artifact.openingCode.get 32 ⟨1473,by decide⟩=0x30463 by decide +kernel]; rfl
  · rw [read_at (i:=⟨1474,by decide⟩),show Artifact.openingCode.get 32 ⟨1474,by decide⟩=0xbc0023 by decide +kernel]; rfl


private theorem peel {i : Nat} {op : Instr} {s t : MachineState} {coins : Bool} (word : (i,op)∈words)
    (loc : s.pc=addr i) (pass : stops (execInstrBr s op).pc=false) (path : Path coins s t) :
    Path coins (execInstrBr s op) t := by
  have read := HonestBlocks.fetch_op Artifact.openingCode image (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide)
    s (.base op) (loc ▸ words_read i op word)
  have result (out : Execution) (run : out∈support (execute image 1 s coins)) (cont : out.exit=.unfinished) :
      out.state=execInstrBr s op := by
    have plain : Instruction.base op≠.base .ECALL := by
      simp only [words,List.mem_cons,List.not_mem_nil,or_false] at word
      rcases word with h|h|h|h|h <;> cases h <;> simp
    have eq := HonestAbstract.continued_step _ s _ coins read plain out run cont
    simp only [words,List.mem_cons,List.not_mem_nil,or_false] at word
    rcases word with h|h|h|h|h <;> cases h <;>
      simp only [ordinaryStep,Option.ite_none_right_eq_some,Option.some.injEq] at eq <;> exact eq.2.symm
  cases path with
  | hit run cont stop => rw [result _ run cont,pass] at stop; cases stop
  | more run cont h tail => rwa [result _ run cont] at tail

def readLeft (s : MachineState) := execInstrBr s (.LBU .x14 .x23 0)
def readPair (s : MachineState) := execInstrBr (readLeft s) (.LBU .x15 .x16 0)
def combine (s : MachineState) := execInstrBr (readPair s) (.OR .x6 .x15 .x14)
def branch (s : MachineState) := execInstrBr (combine s) (.BEQ .x6 .x0 8)
def store (s : MachineState) := execInstrBr (branch s) (.SB .x24 .x11 0)

private theorem via (s t : MachineState) (coins : Bool) (pc0 : s.pc=addr 1470) (path : Path coins s t) :
    Path coins (combine s) t ∧ (combine s).pc=addr 1473 := by
  have a : (readLeft s).pc=addr 1471 := by change s.pc+4=_; rw [pc0]; rfl
  have b : (readPair s).pc=addr 1472 := by change (readLeft s).pc+4=_; rw [a]; rfl
  have c : (combine s).pc=addr 1473 := by change (readPair s).pc+4=_; rw [b]; rfl
  have h1 := peel (i:=1470) (op:=.LBU .x14 .x23 0) (by simp [words]) pc0 (by change stops (readLeft s).pc=false; rw [a]; rfl) path
  have h2 := peel (i:=1471) (op:=.LBU .x15 .x16 0) (by simp [words]) a (by change stops (readPair s).pc=false; rw [b]; rfl) h1
  exact ⟨peel (i:=1472) (op:=.OR .x6 .x15 .x14) (by simp [words]) b (by change stops (combine s).pc=false; rw [c]; rfl) h2,c⟩

def after (s : MachineState) (active : Bool) := if active then store s else branch s

theorem getCombine (s : MachineState) (l r : Bool) (lo : s.getByte (s.getReg .x23)=HonestFlagState.code l)
    (hi : s.getByte (s.getReg .x16)=HonestFlagState.code r) :
    (combine s).getReg .x6=w (l||r).toNat ∧ (combine s).getReg .x14=w l.toNat ∧ (combine s).getReg .x15=w r.toNat := by
  have lval : (readLeft s).getReg .x14=(s.getByte (s.getReg .x23)).zeroExtend 64 := by
    change (s.getByte (s.getReg .x23+signExtend12 0)).zeroExtend 64=_
    rw [show signExtend12 0=0#64 from rfl,BitVec.add_zero]
  have rval : (readPair s).getReg .x15=(s.getByte (s.getReg .x16)).zeroExtend 64 := by
    change (s.getByte (s.getReg .x16+signExtend12 0)).zeroExtend 64=_
    rw [show signExtend12 0=0#64 from rfl,BitVec.add_zero]
  change ((readPair s).getReg .x15 ||| (readLeft s).getReg .x14)=_ ∧ (readLeft s).getReg .x14=_ ∧ (readPair s).getReg .x15=_
  rw [lval,rval]
  rw [lo,hi]; cases l <;> cases r <;> decide

theorem afterPath (s t : MachineState) (coins : Bool) (pc0 : s.pc=addr 1470) (path : Path coins s t)
    (l r : Bool) (lo : s.getByte (s.getReg .x23)=HonestFlagState.code l)
    (hi : s.getByte (s.getReg .x16)=HonestFlagState.code r) :
    Path coins (after s (l||r)) t ∧ (after s (l||r)).pc=addr 1475 := by
  obtain ⟨path,atOR⟩ := via s t coins pc0 path
  have logic := (getCombine s l r lo hi).1
  have whereTo : (branch s).pc=if l||r then addr 1474 else addr 1475 := by
    simp only [branch,execInstrBr,logic,show (combine s).getReg .x0=0 from rfl]
    cases l <;> cases r <;> simp [MachineState.setPC,atOR,w,addr,signExtend13]
  have step := peel (i:=1473) (op:=.BEQ .x6 .x0 8) (by simp [words]) atOR (by
    change stops (branch s).pc=false; rw [whereTo]; split <;> rfl) path
  cases active : l||r with
  | false => exact ⟨step,by change (branch s).pc=_; simpa [active] using whereTo⟩
  | true =>
    have start : (branch s).pc=addr 1474 := by simpa [active] using whereTo
    have donePC : (store s).pc=addr 1475 := by change (branch s).pc+4=_; rw [start]; rfl
    exact ⟨peel (i:=1474) (op:=.SB .x24 .x11 0) (by simp [words]) start (by change stops (store s).pc=false; rw [donePC]; rfl) step,donePC⟩

private theorem branch_reg (s : MachineState) (x : Reg) : (branch s).getReg x=(combine s).getReg x := by
  simp only [branch,execInstrBr]; split <;> rfl

private theorem branch_byte (s : MachineState) (q : Word) : (branch s).getByte q=s.getByte q := by
  simp only [branch,execInstrBr]; split <;> rfl

private theorem store_reg (s : MachineState) (x : Reg) : (store s).getReg x=(branch s).getReg x := by cases x <;> rfl

theorem after_reg (s : MachineState) (active : Bool) (x : Reg) : (after s active).getReg x=(combine s).getReg x := by
  cases active <;> simp only [after,ite_true,Bool.false_eq_true,ite_false,store_reg,branch_reg]

theorem after_byte (s : MachineState) (active : Bool) (unit : s.getReg .x11=1) (q : Word) :
    (after s active).getByte q=if active && q==s.getReg .x24 then 1 else s.getByte q := by
  cases active with
  | false => exact branch_byte s q
  | true =>
    change ((branch s).setByte ((branch s).getReg .x24+signExtend12 0)
        (((branch s).getReg .x11).truncate 8)).getByte q=_
    rw [set_byte_read,branch_reg,branch_reg,branch_byte]
    change (if q=s.getReg .x24+0#64 then (s.getReg .x11).truncate 8 else s.getByte q)=_
    rw [unit]; simp only [BitVec.add_zero,Bool.true_and,beq_iff_eq]; rfl

end CommitGolfCandidate.Reconstruction.HonestScanBytes
