import CommitGolfCandidate.S5FlushBytes
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem byte_mem {s t : MachineState} (mem : t.mem=s.mem) (a : Nat) : byteAt t a=byteAt s a := by
  simp only [byteAt,MachineState.getByte,MachineState.getMem,mem]

def flushStore : PathCode := [(383,.SB .x19 .x23 0),(384,.ADDI .x19 .x19 1),(385,.SRLI .x23 .x23 8),
  (386,.ADDI .x24 .x24 4088),(387,.JAL .x0 2097128)]
theorem flush_store (s : MachineState) (a i : Nat) (small : i<4) (pc : s.pc=pcAt 383) (ptr : s.getReg .x19=W a)
    (room : a+1≤MEMORY_BYTES) (bits : s.getReg .x24=W (34-8*i)) :
    let t:=pathEnd s flushStore
    Runs s t 5 5 ∧ t.pc=pcAt 381 ∧ t.getReg .x19=W (a+1) ∧ t.getReg .x23=s.getReg .x23 >>> 8 ∧
      t.getReg .x24=W (34-8*(i+1)) ∧ t.getReg .x18=s.getReg .x18 ∧ t.mem=(s.setByte (W a) ((s.getReg .x23).truncate 8)).mem := by
  let u:=execInstrBr s (.SB .x19 .x23 0)
  let z:=execInstrBr u (.ADDI .x19 .x19 1)
  let w:=execInstrBr z (.SRLI .x23 .x23 8)
  let y:=execInstrBr w (.ADDI .x24 .x24 4088)
  have loc : s.getReg .x19+signExtend12 0=W a:=by rw [ptr];exact BitVec.add_zero _
  have av : memoryArgumentsValid s (.SB .x19 .x23 0)=true := by
    change accessValid (_+_) 1=true;rw [loc];apply access_ok <;> change a+1≤2^36 at room <;> first | omega | (change _≤2^36;omega)
  have store : ordinaryStep s (.base (.SB .x19 .x23 0))=some u:=by simp only [ordinaryStep,av,↓reduceIte];rfl
  have pu : u.pc=pcAt 384:=by change s.pc+4=_;rw [pc];rfl
  have pz : z.pc=pcAt 385:=by change u.pc+4=_;rw [pu];rfl
  have pw : w.pc=pcAt 386:=by change z.pc+4=_;rw [pz];rfl
  have py : y.pc=pcAt 387:=by change w.pc+4=_;rw [pw];rfl
  have ready : pathReady s flushStore:=⟨pc,store,rfl,pu,rfl,rfl,pz,rfl,rfl,pw,rfl,rfl,py,rfl,rfl,True.intro⟩
  refine ⟨path_run _ true _ _ (by decide +kernel) ready,?_,?_,rfl,?_,rfl,?_⟩
  · change y.pc+signExtend21 2097128=_;rw [py];rfl
  · exact (congrArg (·+signExtend12 1) ptr).trans (BitVec.ofNat_add a 1).symm
  · change s.getReg .x24+(-8#64)=_
    rw [bits,←BitVec.sub_eq_add_neg]
    have num:=BitVec.ofNat_sub_ofNat_of_le (w:=64) (34-8*i) 8 (by decide) (show 8≤34-8*i by omega)
    exact num.trans (congrArg W (by omega))
  · change (s.setByte (s.getReg .x19+signExtend12 0) _).mem=_;rw [loc]

theorem flush_step (s : MachineState) (valid : Prop) (v i : Nat) (small : i<4) (old : FlushState s valid v i) :
    ∃ t,Runs s t 7 7 ∧ FlushState t valid v (i+1) := by
  let u:=pathEnd s flushStop
  obtain ⟨test,ip,mem,keep⟩:=flush_guard s (34-8*i) (by omega) old.pc old.bits
  rw [if_neg (show ¬34-8*i<8 by omega)] at ip
  let a:=proofBase+69392+i
  let t:=pathEnd u flushStore
  obtain ⟨emit,ep,ptr,shift,count,base,last⟩:=flush_store u a i small ip ((keep _ (by decide)).trans old.dest)
    (by dsimp [a,proofBase,MEMORY_BYTES];omega) ((keep _ (by decide)).trans old.bits)
  refine ⟨t,test.trans emit,⟨ep,ptr.trans (congrArg W (by dsimp [a];omega)),count,base.trans ((keep _ (by decide)).trans old.base),?_,?_⟩⟩
  · intro good
    rw [shift,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,keep _ (by decide),old.held good,Nat.div_div_eq_div_mul,←pow_add]
    apply congrArg (fun n=>v/2^n);omega
  · intro good j bound
    have post :=set_byte_read u (W a) (W (proofBase+j)) ((u.getReg .x23).truncate 8)
    have same : byteAt t (proofBase+j)=(u.setByte (W a) ((u.getReg .x23).truncate 8)).getByte (W (proofBase+j)) :=byte_mem last _
    rw [same,post]
    by_cases finalByte : j=69392+i
    · subst j;rw [if_pos (show W (proofBase+(69392+i))=W a from congrArg W (by dsimp [a];omega))]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth,show u.getReg .x23=s.getReg .x23 from keep .x23 (by decide),old.held good,byteOf,BitVec.toNat_ofNat]
    · have early : j<69392+i:=by omega
      have away : W (proofBase+j)≠W a := by
        intro eq;have h:=congrArg BitVec.toNat eq
        simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show proofBase+j<2^64 by unfold proofBase;omega),
          Nat.mod_eq_of_lt (show a<2^64 by dsimp [a,proofBase];omega)] at h;dsimp [a] at h;omega
      rw [if_neg away]
      exact (byte_mem (show u.mem=s.mem from mem) _).trans (old.bytes good j early)
end CommitGolfCandidate.S5Machine.Open
