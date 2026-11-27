import CommitGolfCandidate.Stage3cCheckPickPeer
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
def peerLimit (p : RowSite):=p.peerOps.length+(if p.batch then 438 else 9)
def afterPeer (p : RowSite) (k : Nat):=if k+1<p.radix-1 then p.peerPC (k+1) else p.hashPC
structure FetchedPeer (o : Oracle) (x : CheckInput) (p : RowSite) (s t : MachineState) (k old bit off steps : Nat) : Prop where
  run : Flow o s t steps 0
  pc : t.pc=pcAt (afterPeer p k)
  cursor : WireCursor p.batch x t (bit+Pw.bits p.height.val) (off+32)
  digit : t.getReg .x4=W ((old+1)%p.radix)
  parent : t.getReg .x14=s.getReg .x14
  data : readBuffer t (rowCell ((old+1)%p.radix)) 32=wireValue p.batch x bit off (Pw.bits p.height.val)
  mem : Outside s t (rowCell ((old+1)%p.radix)) 32
  keep : RowKeeps s t

private theorem pull_peer (o : Oracle) (x : CheckInput) (s : MachineState) (p : RowSite) (k : Fin 2)
    (bit off digit : Nat) (allowed : p.allowed=true) (needed : k.val<p.radix-1) (bound : digit<3)
    (pc : s.pc=pcAt (p.peerPC k.val+p.peerOps.length)) (ptr : s.getReg (peerTarget p.batch)=W (rowCell digit))
    (c : WireCursor p.batch x s bit off) (high : HighInput x s)
    (space : p.batch=true → bit+Pw.bits p.height.val≤8*67840)
    (room : p.batch=false → proofBase+off+32≤MEMORY_BYTES) (align : off%8=0) :
    ∃ t steps,steps≤(if p.batch then 438 else 9) ∧ PeerRead o p.batch x s t (p.peerPC k.val+p.peerOps.length)
      (afterPeer p k.val) (rowCell digit) bit off (Pw.bits p.height.val) steps := by
  let n:=p.peerPC k.val+p.peerOps.length
  let dst:=rowCell digit
  have lim : dst+32≤proofBase:=by dsimp [dst,rowCell,rowBuf,proofBase];omega
  have al : dst%8=0:=by dsimp [dst,rowCell,rowBuf];omega
  obtain ⟨_,sites,ep⟩:=(row_sites p allowed).2.2.2.2.2.2 k needed
  have amount : Pw.bits p.height.val≤256:= (by decide +kernel : ∀ j : Fin 24,Pw.bits j.val≤256) p.height
  cases b : p.batch
  · simp only [b,Bool.false_eq_true,ite_false] at sites ep c ptr ⊢
    obtain ⟨t,read⟩:=peer_normal o x s n dst bit off _ pc ptr c high lim al (room b) align sites.1 sites.2
    refine ⟨t,9,le_rfl,?_⟩
    rw [←show n+9=afterPeer p k.val from ep];exact read
  · simp only [b,ite_true] at sites ep c ptr ⊢
    have back : n+2<2147:= (by decide +kernel : ∀ q : RowSite,∀ i : Fin 2,q.peerPC i.val+q.peerOps.length+2<2147) p k
    obtain ⟨t,steps,sz,read⟩:=peer_packed o x s n dst bit off _ pc ptr c amount (space b) lim al back
      (kernel_immediates p.height).2.2.2 sites.1 sites.2
    refine ⟨t,steps,sz,?_⟩
    rw [←show n+2=afterPeer p k.val from ep];exact read

theorem fetch_peer (o : Oracle) (x : CheckInput) (s : MachineState) (p : RowSite) (k : Fin 2) (bit off digit : Nat)
    (allowed : p.allowed=true) (needed : k.val<p.radix-1) (bound : digit<p.radix)
    (pc : s.pc=pcAt (p.peerPC k.val)) (old : s.getReg .x4=W digit) (gp : s.getReg .x3=3) (row : s.getReg .x25=W rowBuf)
    (c : WireCursor p.batch x s bit off) (high : HighInput x s) (space : p.batch=true → bit+Pw.bits p.height.val≤8*67840)
    (room : p.batch=false → proofBase+off+32≤MEMORY_BYTES) (align : off%8=0) :
    ∃ t steps,steps≤peerLimit p ∧ FetchedPeer o x p s t k.val digit bit off steps := by
  obtain ⟨u,chosen⟩:=pick_peer o s p k digit allowed needed bound pc old gp row
  have cur:=c.same chosen.mem (chosen.keep _ (by decide)) (chosen.keep _ (by decide)) (chosen.keep _ (by decide)) (chosen.keep _ (by decide))
  have small : (digit+1)%p.radix<3:=by unfold RowSite.radix Geo.radix;omega
  obtain ⟨t,n,lim,read⟩:=pull_peer o x u p k bit off ((digit+1)%p.radix) allowed needed small chosen.pc chosen.address cur
    (high.same chosen.mem) space room align
  refine ⟨t,p.peerOps.length+n,Nat.add_le_add_left lim _,⟨chosen.run.trans read.run,read.pc,read.cursor,
    (read.keep .x4 (Or.inr (Or.inl rfl))).trans chosen.lane,
    (read.keep .x14 (Or.inr (Or.inr rfl))).trans (chosen.keep _ (by decide)),read.data,
    fun q h al e=>(read.mem q h al e).trans (congrFun chosen.mem _),?_⟩⟩
  intro q h;apply (read.keep q (Or.inl h)).trans;apply chosen.keep;cases q <;> simp_all [rowRegs]
end CommitGolfCandidate.Chained.BinaryMachine.Check
