import CommitGolfCandidate.TwoPermutationPackedImage
import CommitGolfCandidate.ProjectedMask

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp OracleSpec ShortTree
set_option maxRecDepth 8192
set_option maxHeartbeats 850000
attribute [local irreducible] execute readBuffer writeBits capCompressionAnswer

/-- The scratch value the masking stub leaves in x31. -/
def stubTop (answer : BitVec 256) : Word := (padLow answer).extractLsb' 192 64

private theorem state_ext {a b : MachineState} (h1 : a.regs = b.regs) (h2 : a.mem = b.mem)
    (h3 : a.code = b.code) (h4 : a.pc = b.pc) (h5 : a.committed = b.committed)
    (h6 : a.publicValues = b.publicValues) (h7 : a.privateInput = b.privateInput)
    (h8 : a.inputBufBase = b.inputBufBase) : a = b := by
  cases a; cases b; cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; cases h7; cases h8; rfl

private theorem set_reg_set_pc (t : MachineState) (r : Reg) (v a : Word) :
    (t.setPC a).setReg r v=(t.setReg r v).setPC a := by cases r <;> rfl

private theorem set_pc_twice (t : MachineState) (a b : Word) : (t.setPC a).setPC b=t.setPC b := rfl

private theorem set_mem_set_pc (t : MachineState) (q v a : Word) :
    (t.setPC a).setMem q v=(t.setMem q v).setPC a := rfl

private theorem set_mem_set_reg (t : MachineState) (r : Reg) (q v w : Word) :
    (t.setReg r v).setMem q w=(t.setMem q w).setReg r v := by cases r <;> rfl

private theorem set_reg_twice (t : MachineState) (v w : Word) :
    (t.setReg .x31 v).setReg .x31 w=t.setReg .x31 w := by
  simp only [MachineState.setReg]
  congr 1
  funext r
  split <;> rfl

private theorem stub_chain_reg (t : MachineState) (d : Reg) (dNe : d ≠ .x31) (enter leave : BitVec 21)
    (base : Nat) (x : Word) (dest : t.getReg d=BitVec.ofNat 64 base)
    (top : t.getMem (BitVec.ofNat 64 base+signExtend12 24)=x) :
    execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr t
      (.JAL .x0 enter)) (.LD .x31 d 24)) (.SLLI .x31 .x31 18)) (.SRLI .x31 .x31 18)) (.SD d .x31 24))
      (.JAL .x0 leave) =
    ((t.setMem (BitVec.ofNat 64 base+signExtend12 24) ((x <<< 18) >>> 18)).setReg .x31
      ((x <<< 18) >>> 18)).setPC (t.pc+signExtend21 enter+4+4+4+4+signExtend21 leave) := by
  let p1 := t.pc+signExtend21 enter
  let t1 := t.setPC p1
  have e1 : execInstrBr t (.JAL .x0 enter)=t1 := rfl
  have e2 : execInstrBr t1 (.LD .x31 d 24)=(t1.setReg .x31 x).setPC (p1+4) := by
    change (t1.setReg .x31 (t1.getMem (t1.getReg d+signExtend12 24))).setPC (t1.pc+4) = _
    have g : t1.getReg d=t.getReg d := MachineState.getReg_setPC
    have m : t1.getMem (BitVec.ofNat 64 base+signExtend12 24)=x := top
    rw [g,dest,m]
    rfl
  let t2 := (t1.setReg .x31 x).setPC (p1+4)
  have g2 : t2.getReg .x31=x := by
    simp only [t2,MachineState.getReg_setPC,MachineState.getReg_setReg_eq (show Reg.x31≠Reg.x0 by decide)]
  have e3 : execInstrBr t2 (.SLLI .x31 .x31 18)=(t2.setReg .x31 (x <<< 18)).setPC (p1+4+4) := by
    change (t2.setReg .x31 (t2.getReg .x31 <<< (18 : BitVec 6).toNat)).setPC (t2.pc+4) = _
    rw [g2]
    rfl
  let t3 := (t2.setReg .x31 (x <<< 18)).setPC (p1+4+4)
  have g3 : t3.getReg .x31=x <<< 18 := by
    simp only [t3,MachineState.getReg_setPC,MachineState.getReg_setReg_eq (show Reg.x31≠Reg.x0 by decide)]
  have e4 : execInstrBr t3 (.SRLI .x31 .x31 18)=(t3.setReg .x31 ((x <<< 18) >>> 18)).setPC (p1+4+4+4) := by
    change (t3.setReg .x31 (t3.getReg .x31 >>> (18 : BitVec 6).toNat)).setPC (t3.pc+4) = _
    rw [g3]
    rfl
  let t4 := (t3.setReg .x31 ((x <<< 18) >>> 18)).setPC (p1+4+4+4)
  have g4 : t4.getReg .x31=(x <<< 18) >>> 18 := by
    simp only [t4,MachineState.getReg_setPC,MachineState.getReg_setReg_eq (show Reg.x31≠Reg.x0 by decide)]
  have g4d : t4.getReg d=BitVec.ofNat 64 base := by
    simp only [t4,t3,t2,t1,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm dNe)]
    exact dest
  have e5 : execInstrBr t4 (.SD d .x31 24)=
      (t4.setMem (BitVec.ofNat 64 base+signExtend12 24) ((x <<< 18) >>> 18)).setPC (p1+4+4+4+4) := by
    change (t4.setMem (t4.getReg d+signExtend12 24) (t4.getReg .x31)).setPC (t4.pc+4) = _
    rw [g4d,g4]
    rfl
  rw [e1,e2,e3,e4,e5]
  change ((t4.setMem _ _).setPC (p1+4+4+4+4)).setPC (p1+4+4+4+4+signExtend21 leave) = _
  simp only [t4,t3,t2,t1,set_reg_set_pc,set_pc_twice,set_mem_set_pc,set_reg_twice,set_mem_set_reg]
  rfl

private theorem stub_chain (site : ProjectSite) (t : MachineState) (base : Nat) (x : Word)
    (dest : t.getReg site.dest=BitVec.ofNat 64 base)
    (top : t.getMem (BitVec.ofNat 64 base+signExtend12 24)=x) :
    execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr t
      (.JAL .x0 site.enter)) (site.op 0)) (site.op 1)) (site.op 2)) (site.op 3)) (site.op 4) =
    ((t.setMem (BitVec.ofNat 64 base+signExtend12 24) ((x <<< 18) >>> 18)).setReg .x31
      ((x <<< 18) >>> 18)).setPC (t.pc+signExtend21 site.enter+4+4+4+4+signExtend21 site.leave) := by
  cases site
  · exact stub_chain_reg t .x23 (by decide) _ _ base x dest top
  · exact stub_chain_reg t .x12 (by decide) _ _ base x dest top

/-- The compression call followed by the out-of-line mask: the stored digest
is the padded reply, and x31 holds its top word. -/
theorem parent_hash_step (site : ProjectSite) (s : MachineState) (source target : Nat)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*site.start))
    (src : s.getReg .x10=BitVec.ofNat 64 source) (dst : s.getReg .x12=BitVec.ofNat 64 target)
    (mask : s.getReg site.dest=s.getReg .x12)
    (selector : s.getReg .x5=0 ∧ s.getReg .x11=64 ∧ s.getReg .x13=0)
    (srcRoom : source+64≤MEMORY_BYTES) (dstRoom : target+32≤MEMORY_BYTES)
    (srcAlign : source%8=0) (dstAlign : target%8=0) (fuel : Nat) :
    execute packedImage (7+fuel) s false = do
      let answer ← World.query (.inr (.inl (readBuffer s (source+32) 32 ++ readBuffer s source 32)))
      let result ← execute packedImage fuel
        (((capCompressionAnswer s (padLow answer)).setReg .x31 (stubTop answer)).setPC (s.pc+8)) false
      return result.charge 14 1 := by
  have lim : MEMORY_BYTES<2^64 := by decide
  have srcV : rangeValid (s.getReg .x10) 64=true := by
    simp only [src,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : source<2^64),decide_eq_true_eq];exact srcRoom
  have dstV : rangeValid (s.getReg .x12) 32=true := by
    simp only [dst,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : target<2^64),decide_eq_true_eq];exact dstRoom
  have asrc : (s.getReg .x10).toNat%8=0 := by simpa [src,Nat.mod_eq_of_lt (by omega : source<2^64)] using srcAlign
  have adst : (s.getReg .x12).toNat%8=0 := by simpa [dst,Nat.mod_eq_of_lt (by omega : target<2^64)] using dstAlign
  have hash := cap_compression_execute packedImage s (project_fetch _ _ pc) selector srcV dstV asrc adst (fuel+6) false
  change execute packedImage (1+(fuel+6)) s false = (do
    let answer ← World.query (.inr (.inl (readBuffer s (s.getReg .x10).toNat 64)))
    let result ← execute packedImage (fuel+6) (capCompressionAnswer s answer) false
    return result.charge 8 1) at hash
  rw [src,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : source<2^64),read_compression_halves s source srcAlign] at hash
  rw [show 7+fuel=1+(fuel+6) by omega,hash]
  congr 1
  funext answer
  change BitVec 256 at answer
  let raw := capCompressionAnswer s answer
  let j1 := execInstrBr raw (.JAL .x0 site.enter)
  let l := execInstrBr j1 (site.op 0)
  let sl := execInstrBr l (site.op 1)
  let sr := execInstrBr sl (site.op 2)
  let st := execInstrBr sr (site.op 3)
  let j2 := execInstrBr st (site.op 4)
  have rawPC : raw.pc=BitVec.ofNat 64 (4096+4*(site.start+1)) := by
    have moved : raw.pc=s.pc+4 := by unfold raw capCompressionAnswer writeBits;rfl
    rw [moved,pc]
    cases site <;> rfl
  have j1PC : j1.pc=BitVec.ofNat 64 (4096+4*(site.stub+0)) := by
    change raw.pc+signExtend21 site.enter=_
    rw [rawPC]; cases site <;> rfl
  have lPC : l.pc=BitVec.ofNat 64 (4096+4*(site.stub+1)) := by
    change j1.pc+4=_; rw [j1PC]; cases site <;> rfl
  have slPC : sl.pc=BitVec.ofNat 64 (4096+4*(site.stub+2)) := by
    change l.pc+4=_; rw [lPC]; cases site <;> rfl
  have srPC : sr.pc=BitVec.ofNat 64 (4096+4*(site.stub+3)) := by
    change sl.pc+4=_; rw [slPC]; cases site <;> rfl
  have stPC : st.pc=BitVec.ofNat 64 (4096+4*(site.stub+4)) := by
    change sr.pc+4=_; rw [srPC]; cases site <;> rfl
  have destNe : site.dest ≠ .x31 := by cases site <;> decide
  have rawDest : raw.getReg site.dest=BitVec.ofNat 64 target := by
    unfold raw; rw [cap_compression_register,mask,dst]
  have srDest : sr.getReg site.dest=BitVec.ofNat 64 target := by
    cases site <;> exact rawDest
  have addr : BitVec.ofNat 64 target+signExtend12 24=BitVec.ofNat 64 (target+24) := by
    change BitVec.ofNat 64 target+BitVec.ofNat 64 24=_
    rw [←BitVec.ofNat_add]
  have valid : accessValid (BitVec.ofNat 64 (target+24)) 8=true := by
    simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : target+24<2^64),
      Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨by omega,by omega⟩
  have rawMem : raw = writeBits s (BitVec.ofNat 64 target) answer := by
    unfold raw capCompressionAnswer; rw [dst]
  have top : raw.getMem (BitVec.ofNat 64 (target+24)) = answer.extractLsb' 192 64 := by
    rw [rawMem]; exact reply_top_word s target answer dstAlign
  have j1Reg : ∀ r, j1.getReg r=raw.getReg r := by
    intro r; simp only [j1,execInstrBr,MachineState.getReg_setPC]; rfl
  have a1 : j1.getReg site.dest+signExtend12 24=BitVec.ofNat 64 (target+24) := by
    rw [j1Reg,rawDest,addr]
  have lStep : ordinaryStep j1 (.base (site.op 0))=some l := by
    cases site <;> simp only [ProjectSite.op,ProjectSite.dest] at a1 ⊢ <;>
      simp only [ordinaryStep,memoryArgumentsValid,memAccess,a1,valid,↓reduceIte] <;> rfl
  have stStep : ordinaryStep sr (.base (site.op 3))=some st := by
    have a3 : sr.getReg site.dest+signExtend12 24=BitVec.ofNat 64 (target+24) := by rw [srDest,addr]
    cases site <;> simp only [ProjectSite.op,ProjectSite.dest] at a3 ⊢ <;>
      simp only [ordinaryStep,memoryArgumentsValid,memAccess,a3,valid,↓reduceIte] <;> rfl
  have srTop : sr.getReg .x31=stubTop answer := by
    have lv : l.getReg .x31=answer.extractLsb' 192 64 := by
      have : l.getReg .x31=j1.getMem (j1.getReg site.dest+signExtend12 24) := by
        cases site <;> simp only [l,ProjectSite.op,execInstrBr,MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (show Reg.x31≠Reg.x0 by decide)]
      rw [this,a1]
      exact top
    have : sr.getReg .x31=(l.getReg .x31 <<< (18 : BitVec 6).toNat) >>> (18 : BitVec 6).toNat := by
      simp only [sr,sl,ProjectSite.op,execInstrBr,MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (show Reg.x31≠Reg.x0 by decide)]
    rw [this,lv]
    exact top_word_shift answer
  have final : j2=((capCompressionAnswer s (padLow answer)).setReg .x31 (stubTop answer)).setPC (s.pc+8) := by
    have chain := stub_chain site raw target (answer.extractLsb' 192 64) rawDest (by rw [addr]; exact top)
    rw [top_word_shift] at chain
    change execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr raw
      (.JAL .x0 site.enter)) (site.op 0)) (site.op 1)) (site.op 2)) (site.op 3)) (site.op 4) = _
    rw [chain,addr]
    have endPC : raw.pc+signExtend21 site.enter+4+4+4+4+signExtend21 site.leave=s.pc+8 := by
      rw [rawPC,pc]; cases site <;> rfl
    rw [endPC]
    have whole := masked_reply_memory s target answer dstAlign (by omega)
    have rawFrame := write_frame s (BitVec.ofNat 64 target) answer
    have padFrame := write_frame s (BitVec.ofNat 64 target) (padLow answer)
    have target' : capCompressionAnswer s (padLow answer) = writeBits s (BitVec.ofNat 64 target) (padLow answer) := by
      unfold capCompressionAnswer; rw [dst]
    congr 2
    rw [rawMem,target']
    rw [rawFrame] at whole ⊢
    conv => rhs; rw [padFrame]
    rw [padFrame] at whole
    simp only [MachineState.setMem] at whole ⊢
    rw [whole]
  rw [CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (project_fetch_jump site raw rawPC)
      (show ordinaryStep raw _=some j1 from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (project_fetch_stub site 0 (by decide) j1 j1PC) lStep,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (project_fetch_stub site 1 (by decide) l lPC)
      (show ordinaryStep l _=some sl by cases site <;> rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (project_fetch_stub site 2 (by decide) sl slPC)
      (show ordinaryStep sl _=some sr by cases site <;> rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (project_fetch_stub site 3 (by decide) sr srPC) stStep,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (project_fetch_stub site 4 (by decide) st stPC)
      (show ordinaryStep st _=some j2 by cases site <;> rfl),
    final]
  have cyc : ∀ k, instructionCycles (.base (site.op k))=1 := by
    intro k; cases site <;> rcases k with _|_|_|_|_|k <;> rfl
  have cycJ : instructionCycles (.base (.JAL .x0 site.enter))=1 := by cases site <;> rfl
  simp only [bind_assoc,pure_bind,Execution.charge,cyc,cycJ,Nat.zero_add]
  congr 1
  funext x
  congr 2
  omega

end TwoPermutationPrototype.Packed.Checker
