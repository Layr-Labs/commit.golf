import CommitGolfCandidate.S4LeafOps
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest Salt pcAt)
abbrev SmallRegs (r : Reg) := r∉[Reg.x6,.x10,.x12,.x14,.x15]
structure LeafEffect (o : Oracle) (s t : MachineState) (steps q : Nat) : Prop where
  run : CheckRuns o s t steps q
  frame : SameOutside s t 256 352
  keep : ∀ r,SmallRegs r → t.getReg r=s.getReg r

theorem LeafEffect.next {o : Oracle} {s t u : MachineState} {n m a b : Nat} (x : LeafEffect o s t n a)
    (y : LeafEffect o t u m b) : LeafEffect o s u (n+m) (a+b):=
  ⟨x.run.trans y.run,bothScratch x.frame y.frame,fun r hr=>(y.keep r hr).trans (x.keep r hr)⟩

theorem hashEffect {o : Oracle} {s t : MachineState} {pc src dst : Nat} (h : HashResult o s t pc src dst false)
    (lo : 256≤dst) (hi : dst+32≤608) : LeafEffect o s t 3 1:=by
  refine ⟨h.run,protectedBytes h.outside lo hi,?_⟩
  intro r hr;exact h.keep r (by intro e;subst r;exact hr (by decide)) (by intro e;subst r;exact hr (by decide))

private theorem middleCopyRun (o : Oracle) (s : MachineState) (b : Bool) (a : Nat)
    (pc : s.pc=pcAt (rowStart b+54)) (pointer : s.getReg .x9=W a) (al : a%8=0)
    (low : 32768≤a) (bound : a+256≤MEMORY_BYTES) :
    ∃ t,LeafEffect o s t 17 0 ∧ t.pc=pcAt (rowStart b+71) ∧ Moved s t (a+96) 544 64 := by
  let n:=rowStart b+54;let u:=execInstrBr s (ptrCode .x14 512)
  have cap : rowStart b+140≤Code.check.count:=by cases b <;> decide
  have code := (leafSites b).copyMid
  have start := stepAdd .check s n .x14 .x0 512 (by dsimp [n];omega) pc code.head
  have addr : u.getReg .x14=W 512:=rfl
  have copy:=dwordBlock .check u .x9 .x14 (n+1) a 512 96 32 8 (by decide) (by decide) (addPC _ _ _ pc)
    (by dsimp [n];omega) code.tail ((keepAdd s .x14 .x0 .x9 512 (by decide)).trans pointer) addr
    (by omega) (by decide) (by decide) (by decide) (by omega) (by decide) (Or.inr (by omega))
  let t:=copyBlock .x9 .x14 96 32 (dwords 8) u
  have m : Moved s t (a+96) 544 64:=copy.bytes.congr rfl rfl
  refine ⟨t,⟨ofRuns o (start.trans copy.run),protectedBytes m.frame (by decide) (by decide),?_⟩,
    copy.endPC.trans (congrArg pcAt (by dsimp [n] <;> omega)),m⟩
  intro r hr
  exact (copy.regs r (by intro e;subst r;exact hr (by decide))).trans
    (keepAdd s .x14 .x0 r 512 (by intro e;subst r;exact hr (by decide)))

structure Prehashed (o : Oracle) (s t : MachineState) (b : Bool) (salt : Salt) (e : Entry) : Prop where
  effect : LeafEffect o s t 26 3
  pc : t.pc=pcAt (rowStart b+77)
  first : readBuffer t 352 32=o.compression (Late.middleBlock e (o.compression (Late.firstBlock e)))
  second : readBuffer t 384 32=o.compression (Late.lastBlock e)
  salt : readBuffer t 416 24=salt

theorem prehashRun (o : Oracle) (s : MachineState) (b : Bool) (a : Nat) (e : Entry) (salt : Salt)
    (pc : s.pc=pcAt (rowStart b+51)) (ptr : s.getReg .x9=W a) (al : a%8=0) (low : 32768≤a)
    (bound : a+256≤MEMORY_BYTES) (value : readBuffer s a 256=e) (salted : readBuffer s 416 24=salt)
    (mode : s.getReg .x5=0) (kind : s.getReg .x13=0) (len : s.getReg .x11=96) :
    ∃ t,Prehashed o s t b salt e := by
  let n:=rowStart b
  have cap : n+140≤Code.check.count:=by cases b <;> decide
  have code:=leafSites b
  have fst : readBuffer s a 96=Late.firstBlock e:=by
    rw [←value];exact (read_buffer_slice s a 256 0 96 (by decide)).symm
  have remainder : readBuffer s (a+96) 64=e.extractLsb' 768 512:=by
    rw [←value];exact (read_buffer_slice s a 256 96 64 (by decide)).symm
  have last : readBuffer s (a+160) 96=Late.lastBlock e:=by
    rw [←value];exact (read_buffer_slice s a 256 160 96 (by decide)).symm
  let s1:=compressed o.compression s (n+51) .x9 0 a 512 false
  have h1:=compressRun o s (n+51) .x9 0 a 512 false (by intro e;cases e) (by change n+51+3≤_;omega) pc code.first mode kind len
    ((BitVec.add_zero _).trans ptr) rfl ⟨al,by omega⟩ ⟨by decide,by decide⟩
  have f1:=hashEffect h1 (by decide) (by decide)
  obtain ⟨s2,f2,pc2,cp⟩:=middleCopyRun o s1 b a h1.pc ((f1.keep _ (by decide)).trans ptr) al low bound
  have f12:=f1.next f2
  have high : readBuffer s2 544 64=e.extractLsb' 768 512:=(cp.read (by decide)).trans
    ((h1.outside.read (by unfold MEMORY_BYTES at bound;omega) (Or.inr (by omega))).trans remainder)
  have floor : readBuffer s2 512 32=o.compression (Late.firstBlock e):=(cp.away (by decide) (Or.inl (by decide))).trans
    (h1.value.trans (congrArg o.compression fst))
  have joined : readBuffer s2 512 96=Late.middleBlock e (o.compression (Late.firstBlock e)):=by
    have h:=Late.read_join s2 512 32 64
    change readBuffer s2 544 64 ++ readBuffer s2 512 32=(readBuffer s2 512 96).extractLsb' 0 768 at h
    rw [high,floor,BitVec.extractLsb'_eq_self] at h;exact h.symm
  let s3:=compressed o.compression s2 (n+71) .x0 512 512 352 false
  have h3:=compressRun o s2 (n+71) .x0 512 512 352 false (by intro e;cases e) (by change n+71+3≤_;omega) pc2 code.mid
    ((f12.keep _ (by decide)).trans mode) ((f12.keep _ (by decide)).trans kind) ((f12.keep _ (by decide)).trans len)
    rfl rfl ⟨by decide,by decide⟩ ⟨by decide,by decide⟩
  have f123:=f12.next (hashEffect h3 (by decide) (by decide))
  have inLast : readBuffer s3 (a+160) 96=Late.lastBlock e:=(f123.frame.read (by unfold MEMORY_BYTES at bound;omega) (Or.inr (by omega))).trans last
  have pointer3 : s3.getReg .x9+signExtend12 160=W (a+160):=by
    rw [show s3.getReg .x9=W a from (f123.keep _ (by decide)).trans ptr];exact (BitVec.ofNat_add ..).symm
  have h4:=compressRun o s3 (n+74) .x9 160 (a+160) 384 false (by intro e;cases e) (by change n+74+3≤_;omega) h3.pc code.last
    ((f123.keep _ (by decide)).trans mode) ((f123.keep _ (by decide)).trans kind) ((f123.keep _ (by decide)).trans len)
    pointer3 rfl ⟨by omega,by omega⟩ ⟨by decide,by decide⟩
  have aa := h3.value.trans (congrArg o.compression joined)
  refine ⟨_,⟨f123.next (hashEffect h4 (by decide) (by decide)),h4.pc,?_,h4.value.trans (congrArg o.compression inLast),?_⟩⟩
  · exact (h4.outside.read (b:=352) (m:=32) (by decide) (Or.inl (by decide))).trans aa
  · exact (h4.outside.read (by decide) (Or.inr (by decide))).trans ((h3.outside.read (by decide) (Or.inr (by decide))).trans
      ((cp.away (by decide) (Or.inl (by decide))).trans ((h1.outside.read (by decide) (Or.inl (by decide))).trans salted)))
end CommitGolfCandidate.S4.Machine
