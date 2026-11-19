import CommitGolfCandidate.HeadStreamEmit

namespace TwoPermutationPrototype.PackedOpening.HeadStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
open CommitGolfCandidate.ProofCodec.HeadStream
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

def groups (k : Nat) : Nat := (k+3)/4

structure Heads (k L base H : Nat) (Q : Proof) (s0 : MachineState) (g : Nat) (s : MachineState) : Prop where
  regs : Regs k L base H s
  pc : s.pc=pcOf 169
  x22 : s.getReg .x22=BitVec.ofNat 64 g
  x26 : s.getReg .x26=BitVec.ofNat 64 (base+(L-k)+3*g)
  bound : g≤groups k
  mem : ∀ a : Word, s.getByte a=
    if base≤a.toNat ∧ a.toNat<base+(L-k)+3*g then convertedByte k Q (a.toNat-base) else s0.getByte a

structure Partial (k L base H : Nat) (Q : Proof) (s0 : MachineState) (g m : Nat) (s : MachineState) : Prop where
  regs : Regs k L base H s
  pc : s.pc=pcOf (174+7*m)
  x22 : s.getReg .x22=BitVec.ofNat 64 g
  x26 : s.getReg .x26=BitVec.ofNat 64 (base+(L-k)+3*g)
  x28 : s.getReg .x28=BitVec.ofNat 64 (H+4*g)
  x23 : s.getReg .x23=BitVec.ofNat 64 (head k Q (4*g+m))
  mem : ∀ a : Word, s.getByte a=
    if base≤a.toNat ∧ a.toNat<base+(L-k)+3*g+m then convertedByte k Q (a.toNat-base) else s0.getByte a

theorem emit_reg_keep (m : Nat) (hm : m<3) (r : Reg)
    (hr : r∈([.x5,.x10,.x11,.x16,.x20,.x27,.x18,.x9,.x7,.x28,.x26,.x22] : List Reg)) :
    writesAny (emitPath m) r=false := by
  have h := List.all_eq_true.mp (emit_keeps m hm) r hr
  simpa using h

theorem emit_common {k L base H : Nat} {s : MachineState} (regs : Regs k L base H s)
    (m : Nat) (hm : m<3) : Regs k L base H (run s (emitPath m)) := by
  apply regs.keep
  apply List.all_eq_true.mpr
  intro r hr
  have mem : r∈([.x5,.x10,.x11,.x16,.x20,.x27,.x18,.x9,.x7,.x28,.x26,.x22] : List Reg) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    tauto
  simp [emit_reg_keep m hm r mem]

set_option maxHeartbeats 1000000 in
theorem partial_iter (k L base H : Nat) (Q : Proof) (s0 s : MachineState) (g m : Nat)
    (inv : Partial k L base H Q s0 g m s) (len : Q.length=L) (records : 481*k≤L)
    (small : L+7≤2^33) (gap : base+2^33≤H) (room : base+2^34≤2^36)
    (hroom : H+4*groups k≤base+2^34) (hg : g<groups k) (hm : m<3)
    (headers : ∀ r<4*groups k, (s0.getByte (BitVec.ofNat 64 (H+r))).toNat%64=head k Q r) :
    ∃ s', Partial k L base H Q s0 g (m+1) s' ∧ Runs s s' 7 7 := by
  have gdef : groups k=(k+3)/4 := rfl
  have hr : 4*g+m+1<4*groups k := by omega
  have load : (s.getByte (BitVec.ofNat 64 ((H+4*g)+(m+1)))).toNat%64=head k Q (4*g+m+1) := by
    rw [inv.mem,toNat_w _ (by omega),if_neg (by omega)]
    simpa only [Nat.add_assoc] using headers (4*g+m+1) hr
  obtain ⟨ok,pc,next,mem,runs⟩ := emit_one m (head k Q (4*g+m)) (head k Q (4*g+m+1))
    (H+4*g) (base+(L-k)+3*g) hm (head_lt _ _ _) (head_lt _ _ _) s inv.pc inv.x28 inv.x26 inv.x23
    (by omega) (by omega) load
  refine ⟨run s (emitPath m),⟨emit_common inv.regs m hm,pc,?_,?_,?_,?_,?_⟩,runs⟩
  · exact (run_keeps _ _ s (emit_reg_keep m hm .x22 (by decide))).trans inv.x22
  · exact (run_keeps _ _ s (emit_reg_keep m hm .x26 (by decide))).trans inv.x26
  · exact (run_keeps _ _ s (emit_reg_keep m hm .x28 (by decide))).trans inv.x28
  · simpa only [Nat.add_assoc] using next
  · have value : BitVec.ofNat 8 (head k Q (4*g+m)/2^(2*m)+head k Q (4*g+m+1)*2^(6-2*m))=
        convertedByte k Q (L-k+3*g+m) := by
      rw [convertedByte,len,if_neg (by omega),show L-k+3*g+m-(L-k)=3*g+m by omega,
        head_group_byte k Q g m hm]
    have frame : ∀ a, s.getByte a=
        if base≤a.toNat ∧ a.toNat<base+(L-k+3*g+m) then convertedByte k Q (a.toNat-base)
        else s0.getByte a := by simpa only [Nat.add_assoc] using inv.mem
    have store : ∀ a, (run s (emitPath m)).getByte a=
        if a=BitVec.ofNat 64 (base+(L-k+3*g+m)) then
          BitVec.ofNat 8 (head k Q (4*g+m)/2^(2*m)+head k Q (4*g+m+1)*2^(6-2*m)) else s.getByte a := by
      simpa only [Nat.add_assoc] using mem
    have result := extend_region _ _ base (L-k+3*g+m) (convertedByte k Q) s0.getByte _
      (by omega) frame store value
    simpa only [Nat.add_assoc] using result

def headEnter : List Nat := [169,170,171,172,173]
def headTail : List Nat := [195,223,224,225]

@[simp] theorem head_skip : pcOf 195+signExtend21 112#21=pcOf 223 := by decide

@[simp] theorem head_branch : pcOf 169+signExtend13 228#13=pcOf 226 := by decide
@[simp] theorem head_jump : pcOf 225+signExtend21 2096928#21=pcOf 169 := by decide

end TwoPermutationPrototype.PackedOpening.HeadStream
