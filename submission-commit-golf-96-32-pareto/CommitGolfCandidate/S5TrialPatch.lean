import CommitGolfCandidate.S5TrialPatchBits
import CommitGolfCandidate.S5TrialPatchSetup
import CommitGolfCandidate.S5UpperArgs

namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside wordAt)

attribute [local irreducible] readBuffer slotValue lookup

private theorem patched_slot {x s t} (old new : Fin 4)
    (before : readBuffer s (slotAddr 170) 32=slotValue x old 170)
    (top : wordAt t (slotAddr 170+24)=(slotValue x new 170).extractLsb' 192 64)
    (frame : Outside s t (slotAddr 170+24) 8) : readBuffer t (slotAddr 170) 32=slotValue x new 170 := by
  let a:=slotAddr 170
  let dst:=slotValue x new 170
  let w:=writeBits s (W a) dst
  apply (read_digest_congr t w a (by decide) ?_).trans (store_read s a dst)
  intro j hj
  apply Eq.trans _ (output_word s a j dst (by decide) hj).symm
  by_cases third : j=3
  · subst j;exact top
  · have oldWord:=read_digest_word s a j (by decide) hj
    change readBuffer s a 32=slotValue x old 170 at before
    rw [before] at oldWord
    exact (frame (a+8*j) (by dsimp [a,slotAddr,slotBase,MEMORY_BYTES];omega)
      (by dsimp [a,slotAddr,slotBase];omega) (Or.inl (by dsimp [a];omega))).trans
      (oldWord.symm.trans (last_slot_low x old new j (by omega)))

private theorem patch_evidence {H x old new s t} (ev : Evidence H x old s)
    (frame : Outside s t (slotAddr 170+24) 8)
    (finalSlot : readBuffer t (slotAddr 170) 32=slotValue x new 170) : Evidence H x new t := by
  constructor
  · intro j h
    apply (Open.outside_byte frame (by decide) (by decide) (by dsimp [marksBuf,MEMORY_BYTES];omega)
      (Or.inl (by dsimp [marksBuf,slotAddr,slotBase];omega))).trans (ev.mark j h)
  · intro j h v e
    apply (Open.outside_read frame (by decide) (by decide) (bucketAddress j) 32
      (by dsimp [bucketAddress,compBase,MEMORY_BYTES];omega)
      (Or.inl (by dsimp [bucketAddress,compBase,slotAddr,slotBase];omega))).trans (ev.computed j h v e)
  · intro j h
    by_cases last : j=170
    · subst j;exact finalSlot
    · have small : j<170:=by omega
      have same : slotValue x old j=slotValue x new j:=by
        unfold slotValue
        exact (S5.trial_slot x old j small).trans (S5.trial_slot x new j small).symm
      exact (Open.outside_read frame (by decide) (by decide) (slotAddr j) 32
        (by dsimp [slotAddr,slotBase,MEMORY_BYTES];omega)
        (Or.inl (by dsimp [slotAddr,slotBase];omega))).trans ((ev.slot j h).trans same)
  · exact (Open.outside_read frame (by decide) (by decide) rootBase 32 (by decide) (Or.inr (by decide))).trans ev.root

private theorem patch_cache {s t v} (cache : Cache s v) (frame : Outside s t (slotAddr 170+24) 8) : Cache t v := by
  have read (a : Nat) (lo : capBase≤a) (hi : a+32≤saltBuf) : readBuffer t a 32=readBuffer s a 32 :=
    Open.outside_read frame (by decide) (by decide) a 32 (hi.trans (by decide))
      (Or.inr ((by decide : slotAddr 170+24+8≤capBase).trans lo))
  constructor
  · intro d hd j hj;obtain ⟨lo,hi,_⟩:=node_range d j hd hj
    have g:=cap_geometry ⟨d,hd⟩
    exact (read _ (g.1.trans lo) (hi.trans g.2.1)).trans (cache.node d hd j hj)
  · intro d hd j hj;obtain ⟨lo,hi,_⟩:=gap_range d j hd hj
    have g:=cap_geometry ⟨d,by omega⟩
    exact (read _ (g.1.trans lo) (hi.trans g.2.1)).trans (cache.gap d hd j hj)

private def patchOps : List Sym.Calc := [.slli .x6 .x19 36,.bor .x6 .x18 .x6]

set_option maxHeartbeats 2000000 in
private theorem patch_listed : Sym.Listed patchOps 1125 := by decide +kernel

private theorem patch_writers : writers patchOps [.x6] := by decide

private theorem cap_avoids_patch (r : Reg) (h : r ∈ capRegs) : r ∉ ([.x6] : List Reg) := by
  cases r <;> simp_all [capRegs]

private theorem stored_reg (s : MachineState) (a : Nat) (v ip : Word) (r : Reg) :
    ((store s a v).setPC ip).getReg r = s.getReg r := by
  rw [MachineState.getReg_setPC]
  cases r <;> rfl

theorem trial_patch (o : Oracle) (x : CheckInput) (old new : Fin 4) (s : MachineState) (v : Values)
    (pc : s.pc=pcAt 1125) (regs : TrialRegs o.compression x new s)
    (ev : Evidence o.compression x old s) (cache : Cache s v) :
    ∃ t,Flow o s t 3 0 ∧ t.pc=pcAt 1128 ∧ CapKeeps s t ∧ Evidence o.compression x new t ∧ Cache t v := by
  let u:=Sym.evaluated patchOps s
  obtain ⟨one,values,mem,ip⟩:=Sym.compiled o patchOps 1125 s pc patch_listed
    (by change ∀ a∈([] : List (Sym.Expr×Nat)),_;simp)
  let a:=slotAddr 170+24
  let value:=(slotValue x new 170).extractLsb' 192 64
  have dst : u.getReg .x9+signExtend12 24=W a := by
    have addr : u.getReg .x9=s.getReg .x9:=values .x9
    rw [addr,regs.addr];rfl
  have word : u.getReg .x6=value := by
    apply (values .x6).trans
    change s.getReg .x18 ||| (s.getReg .x19 <<< 36)=_
    rw [regs.baseWord,regs.trial];exact last_slot_patch_word x new
  let t:=(store u a value).setPC (pcAt 1128)
  have two:=store_step o u 1127 .x9 .x6 24 a value ip (known (by decide +kernel)) dst word (by decide) (by decide)
  have frame : Outside s t a 8:=by
    intro i hi al away
    exact (store_far u a value (by decide) i hi al away).trans (congrFun mem _)
  have data:=patched_slot old new (ev.slot 170 (by decide)) (t:=t) (store_word_read u a value) frame
  refine ⟨t,one.trans two,rfl,?_,patch_evidence ev frame data,patch_cache cache frame⟩
  intro r hr
  exact (stored_reg u a value (pcAt 1128) r).trans
    ((values r).trans (sym_keep s patchOps [.x6] patch_writers r (cap_avoids_patch r hr)))
end CommitGolfCandidate.S5Machine.Check
