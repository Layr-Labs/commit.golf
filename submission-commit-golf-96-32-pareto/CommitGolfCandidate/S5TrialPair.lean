import CommitGolfCandidate.S5TrialPairSingle
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
namespace TrialPair

private def headOps : List Sym.Calc :=
  [.lui .x4 26,.addi .x4 .x4 4064,.bor .x6 .x21 .x22]

private theorem head_regs (s : MachineState) (r : Reg) (ok : r ∈ capRegs) :
    ((headOps.foldl Sym.bump Sym.original) r).eval s = s.getReg r := by
  cases r <;> first | rfl | (exfalso; revert ok; decide)

private theorem head (o : Oracle) (s : MachineState) (a b : Option Late.Digest)
    (pc : s.pc = pcAt 1128) (l : s.getReg .x21 = markedWord a) (r : s.getReg .x22 = markedWord b) :
    ∃ t, Flow o s t 4 0 ∧ t.pc = pcAt (if touched a b then 1141 else 1132) ∧
      t.getReg .x4 = W (nodeAt 0 170) ∧ CapKeeps s t ∧ t.mem = s.mem := by
  obtain ⟨runHead,regs,mem,ip⟩ := Sym.compiled o headOps 1128 s pc (by decide +kernel)
    (by change ∀ e∈([] : List (Sym.Expr×Nat)),_; simp)
  let u := Sym.evaluated headOps s
  have flag : u.getReg .x6 = markedWord a ||| markedWord b := by
    apply (regs .x6).trans
    change s.getReg .x21 ||| s.getReg .x22 = _
    rw [l,r]
  have cond : Rel.ne.test (u.getReg .x6) (u.getReg .x0) = touched a b := by
    change (u.getReg .x6 != 0#64) = _
    rw [flag]
    cases a <;> cases b <;> simp [markedWord, markBit, touched] <;> decide
  have br := branch o u 1131 1141 .ne .x6 .x0 (by decide +kernel) ip _ cond
  exact ⟨_,runHead.trans br,rfl,MachineState.getReg_setPC.trans (regs .x4),
    fun k ok => MachineState.getReg_setPC.trans ((regs k).trans (head_regs s k ok)),mem⟩

private def emptyCopy : CopySpec := ⟨.x7,.x9,.x4,0,0⟩
private theorem empty_pair (o : Oracle) (s : MachineState) (slot : Late.Digest)
    (pc : s.pc = pcAt 1132) (ptr : s.getReg .x9 = W (slotAddr 170)) (dst : s.getReg .x4 = W (nodeAt 0 170))
    (read : readBuffer s (slotAddr 170) 32 = slot) :
    ∃ t, Flow o s t 9 0 ∧ t.pc = pcAt 1197 ∧ readBuffer t (nodeAt 0 170) 32 = slot ∧
      CapKeeps s t ∧ ChainOutside s t (nodeAt 0 170) := by
  obtain ⟨u,copy⟩ := copy_words o s 1132 (slotAddr 170) (nodeAt 0 170) 4 emptyCopy (by unfold CopySites; decide +kernel)
    (by decide) (by decide) pc ptr dst ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ (Or.inl (by decide))
  have j := jump o u 1140 1197 .x0 (by decide +kernel) copy.pc
  let t := u.setPC (pcAt 1197)
  have eq : readBuffer t (nodeAt 0 170) 32 = slot :=
    (read_buffer_memory_congr t u rfl _ _).trans ((copied_read (a:=slotAddr 170) (b:=nodeAt 0 170) (n:=4)
      copy.data (by decide) (by decide)).trans read)
  exact ⟨t,copy.run.trans j,rfl,eq,fun k ok => MachineState.getReg_setPC.trans (copy.keep k (by
    cases k <;> simp_all [capRegs,emptyCopy])),(ChainOutside.output copy.data.outside).trans (ChainOutside.same rfl)⟩

attribute [local irreducible] readBuffer
private theorem body (o : Oracle) (s : MachineState) (a b : Option Late.Digest) (slot : Late.Digest)
    (pc : s.pc = pcAt (if touched a b then 1141 else 1132))
    (dst : s.getReg .x4 = W (nodeAt 0 170)) (ptr : s.getReg .x9 = W (slotAddr 170))
    (rp : s.getReg .x25 = W rowBuf) (scratch : s.getReg .x26 = W chainBuf)
    (l : s.getReg .x21 = markedWord a) (singleMark : a = none ∨ b = none)
    (slotRead : readBuffer s (slotAddr 170) 32 = slot)
    (lRead : ∀ v, a = some v → readBuffer s (bucketAddress 340) 32 = v)
    (rRead : ∀ v, b = some v → readBuffer s (bucketAddress 341) 32 = v) :
    ∃ t n c, n ≤ 214 ∧ c ≤ 16 ∧ Flow o s t n c ∧ t.pc = pcAt 1197 ∧
      readBuffer t (nodeAt 0 170) 32 = pairValue o.compression a b slot ∧
      CapKeeps s t ∧ ChainOutside s t (nodeAt 0 170) := by
  cases a with
  | none =>
    cases b with
    | none =>
      obtain ⟨t,run,ip,out,keep,frame⟩ := empty_pair o s slot pc ptr dst slotRead
      exact ⟨t,9,0,by decide,by decide,run,ip,out,keep,frame⟩
    | some v =>
      obtain ⟨t,n,lim,run,ip,out,keep,frame⟩ := single o s false slot v pc dst ptr rp scratch
        (by change (s.getReg .x21 == 0#64) = true; rw [l]; rfl) slotRead (rRead _ rfl)
      exact ⟨t,n,16,lim,by decide,run,ip,out,keep,frame⟩
  | some v =>
    cases b with
    | none =>
      obtain ⟨t,n,lim,run,ip,out,keep,frame⟩ := single o s true v slot pc dst ptr rp scratch
        (by change (s.getReg .x21 == 0#64) = false; rw [l]; rfl) (lRead _ rfl) slotRead
      exact ⟨t,n,16,lim,by decide,run,ip,out,keep,frame⟩
    | some w => simp at singleMark

private theorem model (H : Compression) (x : CheckInput) (q : Fin 4) :
    pairValue H (lookup H x 128 340) (lookup H x 128 341) (slotValue x q 170) = capVal H x q 0 170 := by
  unfold capVal
  rw [S5.Auth.upper,if_pos (by decide : 170<171)]
  exact pair_model H x q 170

end TrialPair

attribute [local irreducible] readBuffer lookup slotValue capVal
theorem trial_pair (o : Oracle) (x : CheckInput) (q : Fin 4) (s : MachineState)
    (pc : s.pc = pcAt 1128) (env : CapEnv x s) (e : Evidence o.compression x q s)
    (ptr : s.getReg .x9 = W (slotAddr 170))
    (left : s.getReg .x21 = markedWord (lookup o.compression x 128 340))
    (right : s.getReg .x22 = markedWord (lookup o.compression x 128 341))
    (singleMark : lookup o.compression x 128 340 = none ∨ lookup o.compression x 128 341 = none) :
    ∃ t n calls, n ≤ 250 ∧ calls ≤ 16 ∧ Flow o s t n calls ∧ t.pc = pcAt 1197 ∧
      readBuffer t (nodeAt 0 170) 32 = capVal o.compression x q 0 170 ∧
      CapKeeps s t ∧ ChainOutside s t (nodeAt 0 170) := by
  obtain ⟨u,h,ip,dst,regs,mem⟩ := TrialPair.head o s _ _ pc left right
  have entries := e.same mem
  obtain ⟨t,n,c,lim,cl,run,ep,out,keep,frame⟩ := TrialPair.body o u _ _ (slotValue x q 170) ip dst
    ((regs _ (by decide)).trans ptr) ((regs _ (by decide)).trans env.row) ((regs _ (by decide)).trans env.chain)
    ((regs _ (by decide)).trans left) singleMark (entries.slot 170 (by decide))
    (entries.computed 340 (by decide)) (entries.computed 341 (by decide))
  exact ⟨t,4+n,c,by omega,cl,by simpa only [Nat.zero_add] using h.trans run,ep,
    out.trans (TrialPair.model _ _ _),regs.trans keep,(ChainOutside.same mem).trans frame⟩
end CommitGolfCandidate.S5Machine.Check
