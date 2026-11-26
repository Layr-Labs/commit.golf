import CommitGolfCandidate.ReconstructedCommitParentsTree

namespace CommitGolfCandidate.Reconstruction.CommitParents.RootCopy
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CommitExact
set_option maxHeartbeats 1400000
set_option maxRecDepth 16000
attribute [local irreducible] readBuffer

def src := 4294971456
def dst := 4294971392
def wordAddr (a i : Nat) := BitVec.ofNat 64 (a+8*i)
def imm (i : Nat) := BitVec.ofNat 12 (8*i)
def loadWord (i : Nat) := Instr.LD .x7 .x12 (imm i)
def saveWord (i : Nat) := Instr.SD .x6 .x7 (imm i)
def put (s : MachineState) (i : Nat) := execInstrBr (execInstrBr s (loadWord i)) (saveWord i)
def copies : Nat → MachineState → MachineState
  | 0,s => s
  | n+1,s => put (copies n s) n

private def baseOp : Option Instruction → Option Instr
  | some (.base i) => some i
  | _ => none

private theorem read_ops (i : Fin 4) (save : Bool) (s : MachineState)
    (pc : s.pc=CommitBlocks.addr (150121+2*i.val+save.toNat)) :
    fetch CommitSetup.im s=some (.base (if save then saveWord i else loadWord i)) := by
  have bounds : 150121+2*i.val+save.toNat<150132 := by cases save <;> have := i.isLt <;> simp_all <;> omega
  have receipt : ∀ j : Fin 4, ∀ b : Bool, baseOp (decodeInstruction (Image.readAt (150121+2*j.val+b.toNat))) =
      some (if b then saveWord j else loadWord j) := by decide
  have check := receipt i save
  rw [Image.readAt,dite_eq_left bounds] at check
  apply CommitSetup.fetch_at ⟨_,bounds⟩ _ _ s pc
  generalize eq : decodeInstruction (Artifact.commitCode.get 32 ⟨_,bounds⟩) = x at check ⊢
  cases x <;> simp_all [baseOp]
  rename_i op;cases op <;> simp_all [baseOp] <;> rfl

private theorem add_word : ∀ a : Fin 2, ∀ i : Fin 4,
    let b := if a.val=0 then src else dst
    BitVec.ofNat 64 b + signExtend12 (imm i) = wordAddr b i := by decide

private theorem one (o : Oracle) (s : MachineState) (i : Fin 4)
    (pc : s.pc=CommitBlocks.addr (150121+2*i.val))
    (input : s.getReg .x12=BitVec.ofNat 64 src) (out : s.getReg .x6=BitVec.ofNat 64 dst) :
    let t := put s i
    Segment o CommitSetup.im 2 s t ∧ t.pc=CommitBlocks.addr (150121+2*(i.val+1)) ∧
    t.getReg .x12=s.getReg .x12 ∧ t.getReg .x6=s.getReg .x6 ∧
    t.mem=(s.setMem (wordAddr dst i) (s.getMem (wordAddr src i))).mem := by
  let v := execInstrBr s (loadWord i)
  have va : v.pc=CommitBlocks.addr (150121+2*i.val+1) := by
    rw [CommitBlocks.addr_next,←pc];rfl
  have room : ∀ f : Fin 4, accessValid (wordAddr src f) 8=true ∧ accessValid (wordAddr dst f) 8=true := by decide
  have p1 : s.getReg .x12+signExtend12 (imm i)=wordAddr src i := input ▸ add_word 0 i
  have p2 : v.getReg .x6+signExtend12 (imm i)=wordAddr dst i := out ▸ add_word 1 i
  have run1 : Segment o CommitSetup.im 1 s v := by
    apply plain o _ s v (.base (loadWord i)) (read_ops i false s pc)
    simp [ordinaryStep,loadWord,memoryArgumentsValid,memAccess,p1,(room i).1,v]
  have run2 : Segment o CommitSetup.im 1 v (put s i) := by
    apply plain o _ v (put s i) (.base (saveWord i)) (read_ops i true v va)
    simp [ordinaryStep,saveWord,memoryArgumentsValid,memAccess,p2,(room i).2,put,v]
  refine ⟨compose run1 run2,?_,rfl,rfl,?_⟩
  · change s.pc+4+4=_
    rw [pc,show 150121+2*(i.val+1)=(150121+2*i.val+1)+1 by omega,CommitBlocks.addr_next,CommitBlocks.addr_next]
  · change (s.setMem (s.getReg .x6+signExtend12 (imm i)) (s.getMem (s.getReg .x12+signExtend12 (imm i)))).mem=_
    have p2s : s.getReg .x6+signExtend12 (imm i)=wordAddr dst i := out ▸ add_word 1 i
    rw [p1,p2s]

private theorem addrs_distinct : ∀ i j : Fin 4, wordAddr src i ≠ wordAddr dst j := by decide
private theorem dst_injective : ∀ i j : Fin 4, i.val≠j.val → wordAddr dst i ≠ wordAddr dst j := by decide

structure Copied (s t : MachineState) (n : Nat) : Prop where
  same : ∀ i, i<n → t.getMem (wordAddr dst i)=s.getMem (wordAddr src i)
  outside : ∀ q, (∀ i, i<n → q≠wordAddr dst i) → t.getMem q=s.getMem q

private theorem copy_loop (o : Oracle) (s : MachineState) (pc : s.pc=CommitBlocks.addr 150121)
    (input : s.getReg .x12=BitVec.ofNat 64 src) (out : s.getReg .x6=BitVec.ofNat 64 dst) (n : Nat) (hn : n≤4) :
    let t := copies n s
    Segment o CommitSetup.im (2*n) s t ∧ t.pc=CommitBlocks.addr (150121+2*n) ∧
    t.getReg .x12=BitVec.ofNat 64 src ∧ t.getReg .x6=BitVec.ofNat 64 dst ∧ Copied s t n := by
  induction n with
  | zero => exact ⟨empty ..,pc,input,out,⟨by omega,fun _ _=>rfl⟩⟩
  | succ n ih =>
    let u := copies n s
    obtain ⟨sg,p,a,b,mem⟩ := ih (by omega)
    let i : Fin 4 := ⟨n,by omega⟩
    obtain ⟨go,p',a',b',written⟩ := one o u i p a b
    have val : u.getMem (wordAddr src n)=s.getMem (wordAddr src n) := mem.outside _ (fun j hj=>addrs_distinct i ⟨j,by omega⟩)
    have content (q : Word) : (copies (n+1) s).getMem q = (u.setMem (wordAddr dst n) (u.getMem (wordAddr src n))).getMem q :=
      congrFun written q
    refine ⟨by simpa only [copies,i,u,Nat.mul_add,Nat.mul_one] using compose sg go,p',a'.trans a,b'.trans b,⟨?_,?_⟩⟩
    · intro k h;rw [content]
      by_cases same : k=n
      · rw [same,MachineState.getMem_setMem_eq,val]
      · rw [MachineState.getMem_setMem_ne (dst_injective ⟨k,by omega⟩ i same)]
        exact mem.same k (by omega)
    · intro q h
      rw [content,MachineState.getMem_setMem_ne (h n (by omega))]
      exact mem.outside q (fun j hj=>h j (by omega))

private theorem byte_at (s : MachineState) (a : Nat) :
    s.getByte (BitVec.ofNat 64 a)=extractByte (s.getMem (BitVec.ofNat 64 (8*(a/8)))) (a%8) := by
  have h := aligned_byte s (a/8) (a%8) (by omega)
  simpa only [show 8*(a/8)+a%8 = a by omega,Nat.div_eq_of_lt (show a%8<8 by omega),Nat.mul_zero,Nat.add_zero,Nat.mod_mod] using h

theorem contents {s t : MachineState} (p : Copied s t 4) :
    cell t dst=cell s src ∧ Frame dst s t := by
  constructor
  · apply congrArg unpack
    apply (read_digest_eq_iff _ _ _ _ (by decide : dst%8=0) (by decide : src%8=0)).2
    exact p.same
  · intro a len limit separate
    unfold readBuffer;apply congrArg (BitVec.ofNat _);apply Finset.sum_congr rfl
    intro j hj
    have jlt := Finset.mem_range.1 hj
    have diff (i : Nat) (h : i<4) : BitVec.ofNat 64 (8*((a+j)/8)) ≠ wordAddr dst i := by
      intro eq
      have num := congrArg BitVec.toNat eq
      unfold wordAddr dst at num
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 8*((a+j)/8)<2^64),
        Nat.mod_eq_of_lt (by omega : 4294971392+8*i<2^64)] at num
      unfold dst at separate;omega
    rw [byte_at,byte_at s,p.outside _ diff]

private def header : List Setup.Op := [.lui .x6 256,.addiw .x6 .x6 1,.slli .x6 .x6 12]

private theorem checked_header : Setup.Verified 150118 header := by
    intro j u pos
    change Fin 3 at j
    fin_cases j
    · exact CommitSetup.fetch_at 150118 (.base (.LUI .x6 256)) rfl u pos
    · exact CommitSetup.fetch_at 150119 (.base (.ADDIW .x6 .x6 1)) rfl u pos
    · exact CommitSetup.fetch_at 150120 (.base (.SLLI .x6 .x6 12)) rfl u pos

private theorem load_destination (o : Oracle) (s : MachineState) (pc : s.pc=CommitBlocks.addr 150118)
    (input : s.getReg .x12=BitVec.ofNat 64 src) :
    ∃ a, Segment o CommitSetup.im 3 s a ∧ a.mem=s.mem ∧ a.pc=CommitBlocks.addr 150121 ∧
      a.getReg .x12=BitVec.ofNat 64 src ∧ a.getReg .x6=BitVec.ofNat 64 dst := by
  let v : Reg→Option Word := fun r=>if r=.x12 then some (BitVec.ofNat 64 src) else none
  have agree : Setup.Agrees s v := by
    intro r w h
    dsimp [v] at h
    split at h <;> simp_all
  have val6 : (header.foldl Setup.knownStep v) .x6=some (BitVec.ofNat 64 dst) := by dsimp only [v];decide
  have val12 : (header.foldl Setup.knownStep v) .x12=some (BitVec.ofNat 64 src) := by dsimp only [v];decide
  obtain ⟨sg,mem,p,regs⟩ := Setup.run o s 150118 header v agree pc checked_header
  exact ⟨Setup.after s header,sg,mem,p,regs _ _ val12,regs _ _ val6⟩

private theorem four (o : Oracle) (s : MachineState) (p : s.pc=CommitBlocks.addr 150121)
    (ax : s.getReg .x12=BitVec.ofNat 64 src) (dx : s.getReg .x6=BitVec.ofNat 64 dst) :
    ∃ t, Segment o CommitSetup.im 8 s t ∧ t.pc=CommitBlocks.addr 150129 ∧
      cell t dst=cell s src ∧ Frame dst s t := by
  obtain ⟨cop,tail,_,_,made⟩ := copy_loop o s p ax dx 4 (by decide)
  exact ⟨copies 4 s,cop,tail,contents made⟩

theorem copy_root (o : Oracle) (s : MachineState) (pc : s.pc=CommitBlocks.addr 150118)
    (input : s.getReg .x12=BitVec.ofNat 64 src) :
    ∃ t, Segment o CommitSetup.im 11 s t ∧ t.pc=CommitBlocks.addr 150129 ∧
      cell t dst=cell s src ∧ Frame dst s t := by
  obtain ⟨a,sg,mem,p,ax,dx⟩ := load_destination o s pc input
  obtain ⟨t,cop,tail,r,ext⟩ := four o a p ax dx
  exact ⟨t,compose sg cop,tail,r.trans (cell_congr mem _),
    fun a n h sep=>(ext a n h sep).trans (read_buffer_memory_congr _ _ mem _ _)⟩

end CommitGolfCandidate.Reconstruction.CommitParents.RootCopy
