import CommitGolfCandidate.Layout2BitLoop
import CommitGolfCandidate.Layout2EffectsCopy
import CommitGolfCandidate.Layout2Touched
namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Layout2Helpers (access_ok)
set_option maxHeartbeats 2000000
def byteScratch : List Reg := [.x5,.x6,.x19,.x28,.x29,.x30]

structure ByteCursor (τ : Tables) (r p tb B : Nat) (source : Nat→Byte) (s m : MachineState) (j : Nat) : Prop where
  next : m.pc=if j=B then pc 785 else pc 768
  dst : m.getReg .x5=addr (p+j)
  table : m.getReg .x19=addr (tb+2*(8*j))
  wrote : Writes s m p j (gather τ r source)
  kept : Kept byteScratch s m

theorem byte_loop {I τ r p tb B} (program : Program I) (cfg : Span τ r p tb B)
    (s : MachineState) (source : Nat→Byte) (here : s.pc=pc 767) (base : s.getReg .x8=addr p)
    (endReg : s.getReg .x7=addr (p+B)) (tab : s.getReg .x19=addr tb)
    (scratch : s.getReg .x10=addr scratchBase) (eight : s.getReg .x21=8)
    (table : SpanTable τ r tb B s) (copied : ∀ q, q<B → byte s (scratchBase+q)=source q) :
    ∃ t, Runs I s t (1+101*(B)) (1+101*(B)) ∧ ByteCursor τ r p tb B source s t (B) := by
  let m0:=after .writeHead s
  obtain ⟨hr,hm,hp,ha⟩:=effects_writeHead s here
  have headRun : Runs I s m0 1 1 := runBlock program .writeHead s here (ha.mpr trivial)
  have init : ByteCursor τ r p tb B source s m0 0 := by
    have n:=cfg.nonempty
    refine ⟨by simpa [m0,pcOut,show 0≠B by omega] using hp,?_,?_,(writes_zero s _ _).move rfl hm,?_⟩
    · rw [hr];simpa [regOut] using base
    · rw [hr];simpa [regOut] using tab
    · apply (kept_of_regs hr).weaken; intro q h;cases q <;> simp_all [clobbers,byteScratch]
  obtain ⟨t,ran,done⟩:=loop (B) 101 101 (fun j m=>ByteCursor τ r p tb B source s m j) m0 init (by
    intro j inside m h
    have pcM : m.pc=pc 768 := by simpa [show j≠B by omega] using h.next
    let u:=after .byteHead m
    obtain ⟨headRegs,headMem,headPC,headOK⟩:=effects_byteHead m pcM
    have r0 : Runs I m u 2 2 := runBlock program .byteHead m pcM (headOK.mpr trivial)
    have fixed (q : Reg) (a : q≠.x6) (b : q≠.x28) : u.getReg q=m.getReg q := by
      rw [headRegs];simp [regOut,Ne.symm a,Ne.symm b]
    have sep:=cfg.separated;have later:=cfg.tableAfter;have room:=cfg.room
    have ram : MEMORY_BYTES<2^64 := by decide
    have tabU : SpanTable τ r tb B u := (table.writes cfg h.wrote (by omega)).mem headMem
    have mm : u.mem=m.mem := headMem
    have buf (k : Nat) (small : k<B) : byte u (scratchBase+k)=source k := by
      have cm:=h.wrote.outside (scratchBase+k) (by omega) (Or.inl (by omega))
      simpa only [byte,MachineState.getByte,MachineState.getMem,mm] using cm.trans (copied k small)
    obtain ⟨v,r1,bit⟩:=bit_loop program cfg u j source inside headPC
      ((fixed _ (by decide) (by decide)).trans ((h.kept _ (by decide)).trans scratch))
      ((fixed _ (by decide) (by decide)).trans ((h.kept _ (by decide)).trans eight))
      ((fixed _ (by decide) (by decide)).trans h.table) (by rw [headRegs];rfl) (by rw [headRegs];rfl)
      tabU buf
    have pcV : v.pc=pc 782 := by simpa using bit.next
    obtain ⟨outRegs,outMem,outPC,outOK⟩:=effects_emitByte v pcV
    have ptr : v.getReg .x5=addr (p+j) := (bit.kept _ (by decide)).trans ((fixed _ (by decide) (by decide)).trans h.dst)
    have stop : v.getReg .x7=addr (p+B) := (bit.kept _ (by decide)).trans
      ((fixed _ (by decide) (by decide)).trans ((h.kept _ (by decide)).trans endReg))
    have r2 : Runs I v (after .emitByte v) 3 3 := runBlock program .emitByte v pcV (outOK.mpr (by
      change accessValid (v.getReg .x5) 1=true;rw [ptr];exact access_ok _ 1 (by omega) (by omega)))
    refine ⟨after .emitByte v,(r0.thenDo r1).thenDo r2,?_,?_,?_,?_,?_⟩
    · rw [outPC]
      simp only [pcOut,ptr,stop,show addr (p+j)+1#64=addr (p+j+1) from addr_add _ _]
      by_cases e : j+1=B
      · simp [Nat.add_assoc,e]
      · have diff : addr (p+j+1)≠addr (p+B) := (addr_ne (by omega) (by omega)).2 (by omega)
        simp [e,diff]
    · rw [outRegs];simp [regOut,ptr,show addr (p+j)+1#64=addr (p+j+1) from addr_add _ _,Nat.add_assoc]
    · rw [outRegs];simp [regOut,bit.table,show 8*j+8=8*(j+1) by omega]
    · have unchanged : v.mem=m.mem := bit.memory.trans headMem
      have storeMem : (after .emitByte v).mem=(m.setByte (addr (p+j)) (gather τ r source j)).mem := by
        rw [outMem]
        simp only [memOut,ptr,bit.value,gather,MachineState.setByte,MachineState.setMem,MachineState.getMem,unchanged]
      exact (h.wrote.store _ rfl (by omega)).move rfl storeMem
    · apply h.kept.trans
      apply ((kept_of_regs headRegs).weaken (b:=byteScratch) (by intro q hh;cases q <;> simp_all [clobbers,byteScratch])).trans
      apply (bit.kept.weaken (b:=byteScratch) (by intro q hh;cases q <;> simp_all [bitScratch,byteScratch])).trans
      apply (kept_of_regs outRegs).weaken; intro q hh;cases q <;> simp_all [clobbers,byteScratch])
  exact ⟨t,headRun.thenDo ran,done⟩

end CommitGolfCandidate.Layout2
