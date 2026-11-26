import CommitGolfCandidate.ReconstructedCheckCapRead
import CommitGolfCandidate.ReconstructedCheckLowerWords

namespace CommitGolfCandidate.Reconstruction.CheckCapWords
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckValues CheckParentRun CheckStream
set_option maxRecDepth 14000
set_option maxHeartbeats 1150000
abbrev W := BitVec.ofNat 64

/-- Read one cap sibling at any bit displacement, including an unaligned final word. -/
theorem positive (o : Oracle) (s : MachineState) (g : Reader) (r : Fin 64) (stream w : Nat)
    (good : Placed g) (source : Source s g stream) (range : w=224 ∨ w=240)
    (pc : s.pc=CommitBlocks.addr 495) (cursor : s.getReg .x24=W (64*g.block+r.val)) (proof : s.getReg .x27=W g.proofBase)
    (head : s.getReg .x13=W (w-192)) (mask : s.getReg .x14=W (2^(w-192)-1)) (lim : s.getReg .x1=65) :
    let c:=64*g.block+r.val
    ∃ t,CheckRecorded.Segment o (CheckCapRead.done r w).ticks s t [] ∧ t.pc=CommitBlocks.addr 484 ∧
      (t.getReg .x5).toNat=HonestStream.get stream c 64 ∧ (t.getReg .x7).toNat=HonestStream.get stream (c+64) 64 ∧
      (t.getReg .x28).toNat=HonestStream.get stream (c+128) 64 ∧
      (t.getReg .x29 &&& t.getReg .x14).toNat=HonestStream.get stream (c+192) (w-192) ∧
      (∀ p,t.getMem p=s.getMem p) ∧ Matches (env s g) (CheckCapRead.done r w).state t := by
  let e:=env s g
  have init : Matches e (CheckCapRead.start r w) s:=by
    refine ⟨pc,?_,fun _=>rfl⟩;intro reg;cases reg <;> try rfl
    · exact lim
    · exact head
    · exact mask
    · change s.getReg .x24=physical (env s g) (loc 1 r.val);rw [point];exact cursor
    · change s.getReg .x27=physical (env s g) (loc 4 0);rw [point];exact proof
  obtain ⟨t,seg,hm,pos,lo,mi,hi,top,mk,mem,_⟩:=CheckCapRead.positive o e (context s g (block_bound g good))
    (header_layout s g good) r w range s init
  have src:=input s g stream source
  refine ⟨t,seg,pos,?_,?_,?_,?_,?_,hm⟩
  · rw [hm.regs,lo];exact CheckLowerWords.low e stream _ r src
  · rw [hm.regs,mi];exact CheckLowerWords.mid e stream _ r 1 (by decide) src
  · rw [hm.regs,hi];exact CheckLowerWords.mid e stream _ r 2 (by decide) src
  · rw [hm.regs .x29,hm.regs .x14,top,mk];exact CheckLowerWords.high e stream _ r w (by omega) src
  · intro p;rw [hm.mem,mem];rfl

end CommitGolfCandidate.Reconstruction.CheckCapWords
