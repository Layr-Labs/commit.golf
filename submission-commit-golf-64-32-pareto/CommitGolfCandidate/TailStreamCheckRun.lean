import CommitGolfCandidate.TailStreamCheckPhases

namespace TwoPermutationPrototype.Packed.Checker.TailRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open ProofCodec.HeadStreamSeven
set_option maxRecDepth 8192

def restoreSteps (k L : Nat) : Nat := 39+26*k+∑ i∈Finset.range (L-k),bodySteps k i
def restoreCycles (k L : Nat) : Nat := 42+32*k+∑ i∈Finset.range (L-k),bodyCycles k i

set_option maxHeartbeats 1000000 in
theorem Reach.low_kept {s t : MachineState} (reach : Reach s t) (r : Reg)
    (h17 : r≠.x17) (ht : r∉restoredTemps) : t.getReg r=s.getReg r := by
  apply reach.keep r
  have all : ∀ n : Fin 75,writes (instrAt n.val) r=false := by
    cases r <;> simp_all [restoredTemps] <;> decide
  intro n hn
  exact all ⟨n,hn⟩

set_option maxHeartbeats 1000000 in
theorem restore_run (k L B : Nat) (Q : Proof) (s : MachineState)
    (pc : s.pc=pcOf 0) (x15 : s.getReg .x15=BitVec.ofNat 64 B)
    (x16 : s.getReg .x16=BitVec.ofNat 64 k) (x17 : s.getReg .x17=BitVec.ofNat 64 Q.length)
    (len : Q.length+k/8=L) (kb : k≤2^24) (capacity : L≤8355061248)
    (records : 480*k≤L) (room : B+2^34≤2^36)
    (source : ∀ j<2^34,s.getByte (BitVec.ofNat 64 (B+j))=Q.getD j 0)
    (zero : ∀ q : Word,B+2^33≤q.toNat ∧ q.toNat<B+2^33+k → s.getByte q=0) :
    ∃ t,t.pc=pcOf 74 ∧ t.getReg .x17=BitVec.ofNat 64 L ∧
      (∀ r∈restoredTemps,t.getReg r=0) ∧
      (∀ r,r≠.x17 → r∉restoredTemps → t.getReg r=s.getReg r) ∧
      (∀ a,t.getByte a=if B≤a.toNat ∧ a.toNat<B+L then expandedByte k Q (a.toNat-B) else s.getByte a) ∧
      Hop s t (restoreSteps k L) (restoreCycles k L) ∧ Reach s t := by
  obtain ⟨regs,ipc,icounter,ibytes,ihop,ireach⟩ := initialize_run k Q.length B s pc x15 x16 x17 kb
    (by omega) (by omega) (by omega)
  rw [len] at regs
  have first : Heads k L B Q s 0 (run s setupPath) := by
    refine ⟨regs,ipc,icounter,Nat.zero_le _,?_⟩
    intro a
    rw [prefix_zero]
    exact ibytes a
  obtain ⟨sh,heads,hhop,hreach⟩ := heads_count k L B k 0 Q s (run s setupPath) first
    (by omega) len kb capacity records room source
  obtain ⟨body,bhop,breach⟩ := heads_to_body k L B Q s sh heads records
  have front : ∀ j<L-k,sh.getByte (BitVec.ofNat 64 (B+j))=Q.getD j 0 := by
    intro j hj
    exact Heads.read_front k L B j Q s sh heads (by omega) room source
  obtain ⟨sb,body',bchop,bcreach⟩ := body_count k L B (L-k) Q sh (run sh bodyEnter) body capacity records room front
  obtain ⟨insert,ehop,ereach⟩ := body_to_insert k L B Q sh sb body'
  have scratch : ∀ j<k,sb.getByte (BitVec.ofNat 64 (B+2^33+j))=BitVec.ofNat 8 (restoredHead k Q j) := by
    intro j hj
    exact (Body.read_scratch k L B j Q sh sb body' (by omega) capacity room).trans
      (Heads.read_scratch k L B j Q s sh heads kb hj room)
  obtain ⟨si,insert',ishop,isreach⟩ := insert_count k L B k 0 Q sb (run sb insertEnter) insert
    (by omega) capacity records room scratch
  obtain ⟨endpc,cleared,kept,bytes,chop,creach⟩ := cleanup_run k L B Q sb si insert'
  have fullreach := ireach.trans (hreach.trans (breach.trans (bcreach.trans (ereach.trans (isreach.trans creach)))))
  have fullhop := ((((ihop.thenDo hhop).thenDo bhop).thenDo bchop).thenDo ehop).thenDo ishop |>.thenDo chop
  refine ⟨run si cleanupPath,endpc,(kept .x17 (by decide)).trans insert'.regs.x17,cleared,
    (fun r h17 ht => fullreach.low_kept r h17 ht),?_,
    fullhop.cast (by unfold restoreSteps;omega) (by unfold restoreCycles;omega),fullreach⟩
  intro a
  rw [bytes,insert'.mem]
  have bodyMem : sb.getByte=bodyByte k L B Q sh.getByte 0 := funext body'.mem
  have headMem : sh.getByte=prefixByte (B+2^33) k (fun j => BitVec.ofNat 8 (restoredHead k Q j)) s.getByte := funext heads.mem
  rw [bodyMem,headMem]
  exact restored_memory k L B Q s.getByte a records capacity zero

theorem restore_steps_bound (k L : Nat) : restoreSteps k L≤39+26*k+12*(L-k) := by
  have := body_steps_bound k (L-k)
  unfold restoreSteps
  omega

theorem restore_cycles_bound (k L : Nat) : restoreCycles k L≤42+32*k+15*(L-k) := by
  have := body_cycles_bound k (L-k)
  unfold restoreCycles
  omega

end TwoPermutationPrototype.Packed.Checker.TailRestore
