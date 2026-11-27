import CommitGolfCandidate.Stage3cFieldCall
import CommitGolfCandidate.Stage3cStreamPayload
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W wordAt)

def writerOp : Instr → Bool
  | .SD .x19 _ 0=>true
  | .ADDI .x19 .x19 8=>true
  | .LD d .. | .ADDI d .. | .SLL d .. | .SRL d .. | .ADD d .. | .SUB d .. | .OR d .. | .JAL d .. | .JALR d ..=>d != .x19
  | .BGEU .. | .BLTU .. | .BEQ .. =>true
  | _=>false

private theorem one {op : Instr} (legal : writerOp op) (s : MachineState) :
    let t:=execInstrBr s op
    (t.getReg .x19=s.getReg .x19 ∨ t.getReg .x19=s.getReg .x19+8) ∧
      ∀ q : Word,q≠s.getReg .x19 → t.getMem q=s.getMem q := by
  unfold writerOp at legal
  split at legal
  all_goals first
    | contradiction
    | (refine ⟨Or.inl rfl,?_⟩;intro q ne;change (s.setMem (s.getReg .x19+0#64) _).getMem q=_;rw [BitVec.add_zero];exact MachineState.getMem_setMem_ne ne)
    | exact ⟨Or.inr rfl,fun _ _=>rfl⟩
    | (have ne:=bne_iff_ne.mp legal
       exact ⟨Or.inl (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne)),
         fun _ _=>MachineState.getMem_setPC.trans MachineState.getMem_setReg⟩)
    | (simp only [execInstrBr];split <;> exact ⟨Or.inl rfl,fun _ _=>rfl⟩)

theorem low_path (s : MachineState) (code : PathCode) (d : Nat) (start : s.getReg .x19=W d)
    (space : d+8*code.length<2^64) (legal : code.all fun x=>writerOp x.2) :
    Below s (pathEnd s code) d := by
  induction code generalizing s d with
  | nil=>exact fun _ _=>rfl
  | cons x xs ih=>
    simp only [List.all_cons,Bool.and_eq_true] at legal
    simp only [List.length_cons] at space
    let u:=execInstrBr s x.2
    obtain ⟨cursor,mem⟩:=one legal.1 s
    intro j hj
    have ne : W j≠s.getReg .x19 := by
      rw [start];intro eq;have e:=congrArg BitVec.toNat eq
      simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show j<2^64 by omega),Nat.mod_eq_of_lt (show d<2^64 by omega)] at e;omega
    have before : wordAt u j=wordAt s j := mem _ ne
    rcases cursor with same | advance
    · exact (ih u d (same.trans start) (by omega) legal.2 j hj).trans before
    · have inc : u.getReg .x19=W (d+8):=advance.trans ((congrArg (·+8) start).trans (BitVec.ofNat_add d 8).symm)
      exact (ih u (d+8) inc (by omega) legal.2 j (by omega)).trans before

private theorem good_chunk (b : Bool) (used : Nat) : (chunkCode b used).all (fun x=>writerOp x.2) := by
  simp only [chunkCode,List.all_append]
  have fetch : ∀ b : Bool,(fetchWord b).all (fun x=>writerOp x.2) := by decide
  have m : mix.all (fun x=>writerOp x.2) := by decide
  have saved : ∀ b : Bool,(spill b).all (fun x=>writerOp x.2) := by decide
  rw [fetch,m];split <;> first | rfl | simp [saved]

theorem field_below (s : MachineState) (n k d : Nat) (start : s.getReg .x19=W d)
    (space : d+8*(fieldCode n k).length<2^64) :
    Below s (pathEnd s (fieldCode n k)) d := by
  apply low_path _ _ _ start space
  have good (ws : List Nat) (i : Nat) : (stream ws i).all (fun x=>writerOp x.2) := by
    induction ws generalizing i with
    | nil=>rfl
    | cons w ws ih=>simp only [stream,List.all_append,good_chunk,ih,Bool.true_and]
  rw [fieldCode,List.all_append,good];decide
end CommitGolfCandidate.Chained.BinaryMachine.Writer
