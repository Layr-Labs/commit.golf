import CommitGolfCandidate.R4bTrace
set_option Elab.async false
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.S4
open Machine (W Wrote Safe byte)

def alu (s : MachineState) (d : Reg) (v : Word) := (s.setReg d v).setPC (s.pc+4)
theorem aluGet (s : MachineState) (d : Reg) (v : Word) (nz : d≠.x0) : (alu s d v).getReg d=v :=
  MachineState.getReg_setPC.trans (MachineState.getReg_setReg_eq nz)
theorem aluKeep (s : MachineState) (d : Reg) (v : Word) (r : Reg) (ne : d≠r) :
    (alu s d v).getReg r=s.getReg r := MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne)
theorem shiftL (s : MachineState) (d r : Reg) (n : Nat) (h : n<64) :
    Straight s [.SLLI d r (imm6 n)] (alu s d (s.getReg r <<< n)) := by
  apply Straight.one _ rfl
  change some (alu s d (s.getReg r <<< (imm6 n).toNat))=_
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt h]
theorem shiftR (s : MachineState) (d r : Reg) (n : Nat) (h : n<64) :
    Straight s [.SRLI d r (imm6 n)] (alu s d (s.getReg r >>> n)) := by
  apply Straight.one _ rfl
  change some (alu s d (s.getReg r >>> (imm6 n).toNat))=_
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt h]

def joinOps (r : Nat) : List Instr := if r=0 then [] else [.SLLI .x7 .x6 (imm6 (8*r)),.OR .x7 .x7 .x20]
def dataReg (r : Nat) := if r=0 then Reg.x6 else .x7
theorem doJoin (s : MachineState) (r : Nat) (small : r<8) :
    ∃ t, Straight s (joinOps r) t ∧ t.mem=s.mem ∧
      t.getReg (dataReg r)=mergeWord r (s.getReg .x6) (s.getReg .x20) ∧
      ∀ k, k≠.x7 → t.getReg k=s.getReg k := by
  by_cases z:r=0
  · subst r;exact ⟨s,.nil _,rfl,rfl,fun _ _=>rfl⟩
  let u:=alu s .x7 (s.getReg .x6 <<< (8*r))
  let t:=alu u .x7 (u.getReg .x7 ||| u.getReg .x20)
  have a:=shiftL s .x7 .x6 (8*r) (by omega)
  have b : Straight u [.OR .x7 .x7 .x20] t:=.one rfl rfl
  rw [joinOps,if_neg z]
  refine ⟨t,a.append b,rfl,?_,fun k ne=>(aluKeep _ _ _ _ ne.symm).trans (aluKeep _ _ _ _ ne.symm)⟩
  simp only [dataReg,mergeWord,if_neg z];change t.getReg .x7=_
  rw [show t.getReg .x7=u.getReg .x7 ||| u.getReg .x20 from aluGet _ _ _ (by decide),
    show u.getReg .x7=_ from aluGet _ _ _ (by decide),show u.getReg .x20=_ from aluKeep _ _ _ _ (by decide)]

def shiftPair (a b : Nat) : List Instr := [.SLLI .x20 .x6 (imm6 a),.SRLI .x20 .x20 (imm6 b)]
theorem doPair (s : MachineState) (a b : Nat) (ha : a<64) (hb : b<64) :
    ∃ t,Straight s (shiftPair a b) t ∧ t.mem=s.mem ∧ t.getReg .x20=(s.getReg .x6 <<< a) >>> b ∧
      ∀ k,k≠.x20 → t.getReg k=s.getReg k := by
  let u:=alu s .x20 (s.getReg .x6 <<< a)
  let t:=alu u .x20 (u.getReg .x20 >>> b)
  refine ⟨t,(shiftL _ _ _ _ ha).append (shiftR _ _ _ _ hb),rfl,?_,
    fun k ne=>(aluKeep _ _ _ _ ne.symm).trans (aluKeep _ _ _ _ ne.symm)⟩
  exact (aluGet u .x20 (u.getReg .x20 >>> b) (by decide)).trans (congrArg (fun x : Word=> x >>> b) (aluGet s .x20 _ (by decide)))

def restOps (r n : Nat) : List Instr :=
  if (r+n)%8=0 then [] else if r+n<8 then shiftPair (8*(8-n)) (8*(8-n))
  else if n=8 then [.SRLI .x20 .x6 (imm6 (8*(8-r)))] else shiftPair (8*(8-n)) (8*(16-r-n))
theorem doRest (s : MachineState) (r n : Nat) (r8 : r<8) (n8 : n=6 ∨ n=8) :
    ∃ t,Straight s (restOps r n) t ∧ t.mem=s.mem ∧
      ((r+n)%8≠0 → t.getReg .x20=restWord r n (s.getReg .x6)) ∧ ∀ k,k≠.x20 → t.getReg k=s.getReg k := by
  unfold restOps
  split
  next zero=>exact ⟨s,.nil _,rfl,fun h=>False.elim (h zero),fun _ _=>rfl⟩
  next nz=>
    by_cases low:r+n<8
    · rw [if_pos low];obtain ⟨t,a,m,v,k⟩:=doPair s (8*(8-n)) (8*(8-n)) (by omega) (by omega)
      exact ⟨t,a,m,fun _=>by simpa only [restWord,if_pos low] using v,k⟩
    · rw [if_neg low];by_cases whole:n=8
      · subst n;rw [if_pos rfl]
        let t:=alu s .x20 (s.getReg .x6 >>> (8*(8-r)))
        refine ⟨t,shiftR _ _ _ _ (by omega),rfl,fun _=>?_,fun k ne=>aluKeep _ _ _ _ ne.symm⟩
        rw [restWord,if_neg low,show 16-r-8=8-r by omega];simpa using aluGet s .x20 _ (by decide)
      · rw [if_neg whole];obtain ⟨t,a,m,v,k⟩:=doPair s (8*(8-n)) (8*(16-r-n)) (by omega) (by omega)
        exact ⟨t,a,m,fun _=>by simpa only [restWord,if_neg low] using v,k⟩

def storeOps (r n off : Nat) : List Instr := if 8≤r+n then [.SD .x19 (dataReg r) (imm12 off)] else []
def chunkOps (r n so off : Nat) : List Instr :=
  [.LD .x6 .x12 (imm12 so)] ++ joinOps r ++ storeOps r n off ++ restOps r n

theorem doChunk (s : MachineState) (r n so off src dst : Nat) (r8 : r<8) (n8 : n=6 ∨ n=8)
    (srcPtr : s.getReg .x12+signExtend12 (imm12 so)=W src)
    (dstPtr : s.getReg .x19+signExtend12 (imm12 off)=W dst) (ss : Safe src 8) (ds : Safe dst 8) :
    let v:=s.getMem (W src)
    ∃ t,Straight s (chunkOps r n so off) t ∧
      (∀ k,k≠.x6 → k≠.x7 → k≠.x20 → t.getReg k=s.getReg k) ∧
      ((r+n)%8≠0 → t.getReg .x20=restWord r n v) ∧
      (if 8≤r+n then Wrote s t dst 8 (extractByte (mergeWord r v (s.getReg .x20))) else t.mem=s.mem) := by
  let v:=s.getMem (W src)
  let u:=alu s .x6 v
  have load : Straight s [.LD .x6 .x12 (imm12 so)] u:=justLoad _ _ _ _ _ srcPtr ss
  obtain ⟨m,join,memJ,regJ,keepJ⟩:=doJoin u r r8
  have six : u.getReg .x6=v:=aluGet _ _ _ (by decide)
  have saved : m.getReg .x6=v:=(keepJ _ (by decide)).trans six
  have prev : u.getReg .x20=s.getReg .x20:=aluKeep _ _ _ _ (by decide)
  rw [six,prev] at regJ
  have out := (keepJ .x19 (by decide)).trans (aluKeep s .x6 v .x19 (by decide))
  let value := mergeWord r v (s.getReg .x20)
  have store : ∃ w,Straight m (storeOps r n off) w ∧ (∀ k,w.getReg k=m.getReg k) ∧
      (if 8≤r+n then Wrote s w dst 8 (extractByte value) else w.mem=s.mem) := by
    by_cases flush:8≤r+n
    · obtain ⟨x,wr⟩:=writeWord m .x19 (dataReg r) off dst (by rw [out];exact dstPtr) ds
      simp only [storeOps,if_pos flush]
      refine ⟨_,x,fun k=>by cases k <;> rfl,?_⟩
      intro a ba;rw [wr a ba,regJ];change _=if _ then _ else byte s a
      have eqB : byte m a=byte s a:=by simp only [byte,MachineState.getByte,MachineState.getMem,memJ];rfl
      rw [eqB]
    · simp only [storeOps,if_neg flush];exact ⟨m,.nil _,fun _=>rfl,memJ⟩
  obtain ⟨w,wr,keepW,result⟩:=store
  obtain ⟨t,rest,memT,tail,keepT⟩:=doRest w r n r8 n8
  refine ⟨t,((load.append join).append wr).append rest,fun k a b c=>(keepT k c).trans
    ((keepW k).trans ((keepJ k b).trans (aluKeep s .x6 v k a.symm))),fun h=>(tail h).trans
    (congrArg (restWord r n) ((keepW _).trans saved)),?_⟩
  by_cases h:8≤r+n
  · simp only [if_pos h] at result ⊢;exact result.mem memT
  · simp only [if_neg h] at result ⊢;exact memT.trans result
end CommitGolfCandidate.R4b
