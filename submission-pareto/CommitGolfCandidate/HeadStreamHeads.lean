import CommitGolfCandidate.HeadStreamEmit

namespace TwoPermutationPrototype.PackedOpening.HeadStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
open CommitGolfCandidate.ProofCodec.HeadStreamThree
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def groups (k : Nat) : Nat := (k+7)/8

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
  pc : s.pc=pcOf (174+16*m)
  x22 : s.getReg .x22=BitVec.ofNat 64 g
  x26 : s.getReg .x26=BitVec.ofNat 64 (base+(L-k)+3*g)
  x28 : s.getReg .x28=BitVec.ofNat 64 (H+8*g)
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

theorem ignored_fourth (a b c d e m : Nat) (hm : m<3) (middle : m≠1) :
    BitVec.ofNat 8 (a/2^(8*m%3)+b*2^(3-8*m%3)+c*2^(6-8*m%3)+d*2^(9-8*m%3))=
      BitVec.ofNat 8 (a/2^(8*m%3)+b*2^(3-8*m%3)+c*2^(6-8*m%3)+e*2^(9-8*m%3)) := by
  apply BitVec.eq_of_toNat_eq
  interval_cases m <;> simp only [BitVec.toNat_ofNat] <;> norm_num at * <;> omega

theorem partial_iter (k L base H : Nat) (Q : Proof) (s0 s : MachineState) (g m : Nat)
    (inv : Partial k L base H Q s0 g m s) (len : Q.length=L) (records : 481*k≤L)
    (small : L+7≤2^33) (gap : base+2^33≤H) (room : base+2^34≤2^36)
    (hroom : H+8*groups k+1≤base+2^34) (hg : g<groups k) (hm : m<3)
    (headers : ∀ r<8*groups k, (s0.getByte (BitVec.ofNat 64 (H+r))).toNat%8=head k Q r) :
    ∃ s', Partial k L base H Q s0 g (m+1) s' ∧ Runs s s' 16 16 := by
  have gdef : groups k=(k+7)/8 := rfl
  have hr : 8*g+8*m/3+1<8*groups k := by omega
  have load₀ : (s.getByte (BitVec.ofNat 64 ((H+8*g)+8*m/3))).toNat%8=head k Q (8*g+8*m/3) := by
    rw [inv.mem,toNat_w _ (by omega),if_neg (by omega)]
    simpa only [Nat.add_assoc] using headers (8*g+8*m/3) (by omega)
  have load₁ : (s.getByte (BitVec.ofNat 64 ((H+8*g)+(8*m/3+1)))).toNat%8=head k Q (8*g+8*m/3+1) := by
    rw [inv.mem,toNat_w _ (by omega),if_neg (by omega)]
    simpa only [Nat.add_assoc] using headers (8*g+8*m/3+1) hr
  have load₂ : (s.getByte (BitVec.ofNat 64 ((H+8*g)+(8*m/3+2)))).toNat%8=head k Q (8*g+8*m/3+2) := by
    rw [inv.mem,toNat_w _ (by omega),if_neg (by omega)]
    simpa only [Nat.add_assoc] using headers (8*g+8*m/3+2) (by omega)
  let d := (s.getByte (BitVec.ofNat 64 ((H+8*g)+(8*m/3+3)))).toNat%8
  obtain ⟨ok,pc,mem,runs⟩ := emit_one m (head k Q (8*g+8*m/3)) (head k Q (8*g+8*m/3+1))
    (head k Q (8*g+8*m/3+2)) d
    (H+8*g) (base+(L-k)+3*g) hm (head_lt _ _ _) (head_lt _ _ _) (head_lt _ _ _) (Nat.mod_lt _ (by decide))
    s inv.pc inv.x28 inv.x26 (by omega) (by omega) load₀ load₁ load₂ rfl
  refine ⟨run s (emitPath m),⟨emit_common inv.regs m hm,pc,?_,?_,?_,?_⟩,runs⟩
  · exact (run_keeps _ _ s (emit_reg_keep m hm .x22 (by decide))).trans inv.x22
  · exact (run_keeps _ _ s (emit_reg_keep m hm .x26 (by decide))).trans inv.x26
  · exact (run_keeps _ _ s (emit_reg_keep m hm .x28 (by decide))).trans inv.x28
  · have value : BitVec.ofNat 8 (head k Q (8*g+8*m/3)/2^(8*m%3)+
          head k Q (8*g+8*m/3+1)*2^(3-8*m%3)+head k Q (8*g+8*m/3+2)*2^(6-8*m%3)+d*2^(9-8*m%3))=
        convertedByte k Q (L-k+3*g+m) := by
      rw [convertedByte,len,if_neg (by omega),show L-k+3*g+m-(L-k)=3*g+m by omega,
        head_group_byte k Q g m hm]
      by_cases middle : m=1
      · have load₃ : d=head k Q (8*g+8*m/3+3) := by
          dsimp [d]
          rw [inv.mem,toNat_w _ (by omega),if_neg (by omega)]
          simpa only [Nat.add_assoc] using headers (8*g+8*m/3+3) (by omega)
        rw [load₃]
      · exact ignored_fourth _ _ _ d _ m hm middle
    have frame : ∀ a, s.getByte a=
        if base≤a.toNat ∧ a.toNat<base+(L-k+3*g+m) then convertedByte k Q (a.toNat-base)
        else s0.getByte a := by simpa only [Nat.add_assoc] using inv.mem
    have store : ∀ a, (run s (emitPath m)).getByte a=
        if a=BitVec.ofNat 64 (base+(L-k+3*g+m)) then
          BitVec.ofNat 8 (head k Q (8*g+8*m/3)/2^(8*m%3)+
            head k Q (8*g+8*m/3+1)*2^(3-8*m%3)+head k Q (8*g+8*m/3+2)*2^(6-8*m%3)+d*2^(9-8*m%3)) else s.getByte a := by
      simpa only [Nat.add_assoc] using mem
    have result := extend_region _ _ base (L-k+3*g+m) (convertedByte k Q) s0.getByte _
      (by omega) frame store value
    simpa only [Nat.add_assoc] using result

def headEnter : List Nat := [169,170,171,172,173]
def headTail : List Nat := [222,223,224,225,226,227,228,229,230,231,232,233,234,235,236]

@[simp] theorem head_branch : pcOf 169+signExtend13 272#13=pcOf 237 := by decide
@[simp] theorem head_jump : pcOf 236+signExtend21 2096884#21=pcOf 169 := by decide

end TwoPermutationPrototype.PackedOpening.HeadStream
