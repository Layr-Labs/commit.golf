import CommitGolfCandidate.ReconstructedOpeningHeaderAddress

namespace CommitGolfCandidate.Reconstruction.OpeningLinear
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps OpeningOps
open OpeningCursor TwoPermutationPrototype.RV64
set_option maxRecDepth 16000
attribute [local irreducible] ArtifactEncoding.decode execute

theorem register (o : Oracle) (m : Model) (rd : Reg) (e : Expr) (v : Word)
    (eqn : e.eval m.reg=v) : Contract o [e.instr rd] m (m.set rd v) := by
  rw [←eqn];exact assign o m rd e 

theorem read (o : Oracle) (m : Model) (rd rs : Reg) (imm : BitVec 12) (w : Nat) (v : Word)
    (room : w<2^33) (loc : m.reg rs+signExtend12 imm=wordAddress w) (val : m.mem w=v) :
    Contract o [.LD rd rs imm] m (m.set rd v) := by
  rw [←val];exact LeafModel.load _ _ _ _ _ _ room loc

theorem write (o : Oracle) (m : Model) (rs rv : Reg) (imm : BitVec 12) (w : Nat) (v : Word)
    (room : w<2^33) (loc : m.reg rs+signExtend12 imm=wordAddress w) (val : m.reg rv=v) :
    Contract o [.SD rs rv imm] m (m.store w v) := by
  rw [←val];exact LeafModel.store _ _ _ _ _ _ room loc

def upper (v : Word) : Word := ((v >>> (32 : Nat)).truncate 32).zeroExtend 64

theorem readUpper (o : Oracle) (m : Model) (rd rs : Reg) (imm : BitVec 12) (w : Nat) (v : Word)
    (room : w<2^33) (loc : m.reg rs+signExtend12 imm=W (8*w+4)) (val : m.mem w=v) :
    Contract o [.LWU rd rs imm] m (m.set rd (upper v)) := by
  intro s fits
  have access : accessValid (W (8*w+4)) 4=true := by
    simp [accessValid,rangeValid,MEMORY_BYTES,W,BitVec.toNat_ofNat];omega
  have off : byteOffset (W (8*w+4))=4 := by
    unfold byteOffset
    rw [BitVec.toNat_and,BitVec.toNat_ofNat]
    change (8*w+4)%2^64 &&& (2^3-1)=4
    rw [Nat.and_two_pow_sub_one_eq_mod];omega
  have address : alignToDword (W (8*w+4))=wordAddress w := by
    rw [aligned];change W (8*((8*w+4)/8))=W (8*w);congr 2;omega
  have physical : s.getMem (wordAddress w)=v := (fits.memory w room).trans val
  let t := (s.setReg rd (upper v)).setPC (s.pc+4)
  have step : ordinaryStep s (.base (.LWU rd rs imm))=some t := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,fits.registers,loc,access,
      ite_true,MachineState.getWord32,address,off,physical,t,upper,extractWord32]
  exact ⟨t,Run.one (.ordinary _ _ _ step rfl),(fits.reg rd _).pc _⟩

theorem block {o : Oracle} {m n : Model} {ops : List Instr} {i : Nat}
    (h : Contract o ops m n) (room : i+ops.length≤1660) (entries : OpeningStraight.Listed i ops)
    (s : MachineState) (pc : s.pc=CommitBlocks.addr i) (fits : Fits s m) :
    ∃ t, CommitExact.Segment o OpeningStraight.image ops.length s t ∧
      t.pc=CommitBlocks.addr (i+ops.length) ∧ Fits t n := by
  obtain ⟨t,r,ht⟩ := h s fits
  exact ⟨t,OpeningStraight.segment r i room pc entries,r.next_pc i pc,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningLinear
