import CommitGolfCandidate.S4Catalog

set_option Elab.async false
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt pc_succ)

theorem Matches.head {c : Code} {pc : Nat} {op : Instr} {ops : List Instr} (h : Matches c pc (op::ops)) :
    decodeInstruction (c.word pc)=some (.base op):=h 0 (by simp)
theorem Matches.tail {c : Code} {pc : Nat} {op : Instr} {ops : List Instr} (h : Matches c pc (op::ops)) :
    Matches c (pc+1) ops:=by
  intro j bj;rw [show pc+1+j=pc+(j+1) by omega];exact h (j+1) (by simp;omega)
theorem Matches.left {c : Code} {pc : Nat} {a b : List Instr} (h : Matches c pc (a++b)) :
    Matches c pc a:=by
  intro j bj;have e:=h j (by rw [List.length_append];omega)
  rwa [List.getElem_append_left bj] at e
theorem Matches.right {c : Code} {pc : Nat} {a b : List Instr} (h : Matches c pc (a++b)) :
    Matches c (pc+a.length) b:=by
  intro j bj
  have e:=h (a.length+j) (by simp only [List.length_append];omega)
  simpa only [List.getElem_append_right (show a.length≤a.length+j by omega),Nat.add_sub_cancel_left,Nat.add_assoc] using e

theorem stepAdd (c : Code) (s : MachineState) (pc : Nat) (d r : Reg) (imm : BitVec 12)
    (small : pc<c.count) (atPC : s.pc=pcAt pc)
    (code : decodeInstruction (c.word pc)=some (.base (.ADDI d r imm))) :
    Runs c s (execInstrBr s (.ADDI d r imm)) 1 1 := one small atPC _ code rfl
theorem getAfterAdd (s : MachineState) (d r : Reg) (imm : BitVec 12) (nonzero : d≠.x0) :
    (execInstrBr s (.ADDI d r imm)).getReg d=s.getReg r+signExtend12 imm:=by
  simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq nonzero]
theorem keepAdd (s : MachineState) (d r k : Reg) (imm : BitVec 12) (away : d≠k) :
    (execInstrBr s (.ADDI d r imm)).getReg k=s.getReg k :=
  MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ away)
theorem addPC {s : MachineState} (d r : Reg) (imm : BitVec 12) {n : Nat} (h : s.pc=pcAt n) :
    (execInstrBr s (.ADDI d r imm)).pc=pcAt (n+1):=(congrArg (·+4) h).trans (pc_succ n).symm

def countBytes (n : Nat) := List.replicate n Width.unsignedByte
set_option maxRecDepth 6000 in
private theorem immediates : ∀ i : Fin 257,signExtend12 (BitVec.ofNat 12 i.val)=W i.val := by decide
theorem validBytes (src dst j n : Nat) (sm : j+n≤256) (sb : src+j+n≤MEMORY_BYTES) (db : dst+j+n≤MEMORY_BYTES) :
    validOffsets src dst j j (countBytes n) := by
  induction n generalizing j with
  | zero=>trivial
  | succ n ih=>
    have imm:=immediates ⟨j,by omega⟩
    rw [countBytes,List.replicate_succ,validOffsets]
    exact ⟨⟨by change src+j+1≤MEMORY_BYTES;omega,Nat.mod_one _⟩,⟨by change dst+j+1≤MEMORY_BYTES;omega,Nat.mod_one _⟩,imm,imm,
      ih (j+1) (by omega) (by omega) (by omega)⟩
theorem countSize (n : Nat) : bytesOf (countBytes n)=n := by
  induction n with
  | zero=>rfl
  | succ k ih=>rw [countBytes,List.replicate_succ];change 1+bytesOf (countBytes k)=_;rw [ih,Nat.add_comm]

theorem readIndexed {s : MachineState} {src : Nat} (aligned : src%8=0) :
    s.getMem (W src)=readBuffer s src 8:=by
  exact (read_digest_word s src 0 aligned (by decide)).symm.trans (read_buffer_slice s src 32 0 8 (by decide))

end CommitGolfCandidate.S4.Machine
