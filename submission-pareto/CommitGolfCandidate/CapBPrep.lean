import CommitGolfCandidate.CapBPrepCode
import CommitGolfCandidate.CapBExecute
import CommitGolfCandidate.CapBPrice
import RiscvZkvm.Rv64.Logic.MemRegionWrite
import CommitGolfCandidate.TwoPermutationOpeningMemory

namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Helpers TwoPermutationPrototype
open TwoPermutationPrototype.GroupedOpening (openingImage leafMask leafBit)
open TwoPermutationPrototype.Sampling (capIsMarked)
set_option maxHeartbeats 1600000
set_option maxRecDepth 14000
def markBase : Nat := 4096
def marksArea : Areas := ⟨markBase,markBase,64,0⟩
def ByteMarks (gs : List Nat) (s : MachineState) :=
  ∀ i,i<256 → gbyte s (markBase+256+i)=BitVec.ofNat 8 (capIsMarked gs (256+i) 0).toNat

def treeWord (gs : List Nat) (n : Nat) : Nat → Word
  | 0 => addr (leafMask gs n)
  | h+1 => treeWord gs (2*n) h ||| treeWord gs (2*n+1) h

private def pack (b : Fin 8 → Bool) : Word :=
  (BitVec.ofNat 8 (b 7).toNat)++(BitVec.ofNat 8 (b 6).toNat)++(BitVec.ofNat 8 (b 5).toNat)++
  (BitVec.ofNat 8 (b 4).toNat)++(BitVec.ofNat 8 (b 3).toNat)++(BitVec.ofNat 8 (b 2).toNat)++
  (BitVec.ofNat 8 (b 1).toNat)++(BitVec.ofNat 8 (b 0).toNat)

private def mask (b : Fin 8 → Bool) :=
  (b 0).toNat+2*(b 1).toNat+4*(b 2).toNat+8*(b 3).toNat+16*(b 4).toNat+32*(b 5).toNat+64*(b 6).toNat+128*(b 7).toNat
private def flags (a b c d e f g h : Bool) (i : Fin 8) : Bool :=
  match i.val with | 0=>a | 1=>b | 2=>c | 3=>d | 4=>e | 5=>f | 6=>g | _=>h
private theorem magic_ok : ∀ a b c d e f g h : Bool,
    let v:=flags a b c d e f g h
    ((pack v*0x0102040810204080#64) >>> (56:Nat))=addr (mask v) ∧
    ∀ j : Fin 8, extractByte (pack v) j.val=BitVec.ofNat 8 (v j).toNat := by decide +kernel

theorem compress_marks (b : Fin 8→Bool) : ((pack b*0x0102040810204080#64) >>> (56:Nat))=addr (mask b) ∧
    ∀ j : Fin 8, extractByte (pack b) j.val=BitVec.ofNat 8 (b j).toNat := by
  have h:=magic_ok (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7)
  have eq : flags (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7)=b := by funext j;fin_cases j <;> rfl
  simpa only [eq] using h

theorem one_mask (gs : List Nat) (s : MachineState) (marks : ByteMarks gs s) (c : Nat) (hc : c<32) :
    val s marksArea (markExpr c)=addr (leafMask gs (32+c)) := by
  let b : Fin 8→Bool:=fun j=>capIsMarked gs (8*(32+c)+j.val) 0
  have checked:=compress_marks b
  have wd : s.getMem (marksArea.key .dst (32+c))=pack b := by
    apply eq_of_forall_extractByte
    intro j hj
    have inputByte:=marks (8*c+j) (by omega)
    have atB:=byte_at s (markBase+8*(32+c)) j (by unfold markBase;omega) hj (by unfold markBase;omega)
    have loc : markBase+8*(32+c)+j=markBase+256+(8*c+j) := by omega
    rw [loc] at atB
    change _=extractByte (pack b) j
    have emitted:=checked.2 ⟨j,hj⟩
    rw [emitted]
    exact atB.symm.trans (inputByte.trans (by dsimp [b];rw [show 256+(8*c+j)=8*(32+c)+j by omega]))

  have mg : val s marksArea magic=0x0102040810204080#64 := by simp only [magic,val];decide +kernel
  change (s.getMem (marksArea.key .dst (32+c))*val s marksArea magic) >>> (56:Nat)=_
  rw [wd,mg,checked.1];rfl

theorem tree_value (gs : List Nat) (s : MachineState) (marks : ByteMarks gs s) (n h : Nat)
    (lo : 32≤n*2^h) (hi : (n+1)*2^h≤64) : val s marksArea (treeExpr n h)=treeWord gs n h := by
  induction h generalizing n with
  | zero =>
    simp only [pow_zero,Nat.mul_one] at lo hi
    simpa [treeExpr,treeWord,show 32+(n-32)=n by omega] using one_mask gs s marks (n-32) (by omega)
  | succ h ih =>
    simp only [pow_succ] at lo hi
    simp only [treeExpr,treeWord,val]
    rw [ih (2*n) (by nlinarith [Nat.one_le_two_pow (n:=h)]) (by nlinarith [Nat.one_le_two_pow (n:=h)]),ih (2*n+1) (by nlinarith [Nat.one_le_two_pow (n:=h)]) (by nlinarith [Nat.one_le_two_pow (n:=h)])]

theorem prep_done (s : MachineState) (gs : List Nat) (pcS : s.pc=pc 6960)
    (base : s.getReg .x26=addr markBase) (marks : ByteMarks gs s) :
    ∃ t,Run openingImage s t 195 291 ∧ t.pc=pc 7155 ∧
      (∀ n,1≤n → n<64 → t.getMem (addr (markBase+8*n))=treeWord gs n (height n)) ∧
      (∀ r,r∉[.x5,.x6,.x7,.x28,.x29,.x30,.x31,.x10,.x11,.x12,.x13] → t.getReg r=s.getReg r) ∧
      (∀ w : Word,w.toNat<markBase ∨ markBase+512≤w.toNat → t.getMem w=s.getMem w) := by
  obtain ⟨ok,len,cycles,out,regs⟩:=prep_valid
  have safe : Safe marksArea := by refine ⟨?_,?_,?_⟩ <;> first | (intro b;cases b <;> decide) | decide
  obtain ⟨t,ran,endPC,model⟩:=run (a:=marksArea) (l:=prepLayout) safe (by intro r;cases r <;> exact base)
    (by intro r;cases r <;> rfl) prepRows 6960 s initial (track_zero ..) pcS (by rw [len];decide) (slice_code prep_code) ok
  rw [len,cycles] at ran;rw [len] at endPC
  refine ⟨t,ran,endPC,?_,?_,?_⟩
  · intro n lo hi
    have h:=model.out n hi
    change _=val s marksArea (prepModel.out n) at h
    rw [out ⟨n,hi⟩,if_neg (by simpa using (by omega : n≠0))] at h
    apply h.trans
    have geo : ∀ x : Fin 64,1≤x.val → 32≤x.val*2^(height x.val) ∧ (x.val+1)*2^(height x.val)≤64 := by decide +kernel
    exact tree_value gs s marks n (height n) (geo ⟨n,hi⟩ lo).1 (geo ⟨n,hi⟩ lo).2
  · intro r free;have h:=model.reg r;change _=val s marksArea (prepModel.reg r) at h;rw [regs r free] at h;exact h
  · intro w away;apply model.frame
    intro j hj eq
    rw [eq] at away
    change j<64 at hj
    simp only [Areas.key,Areas.start,marksArea,markBase,addr,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 4096+8*j<2^64 by omega)] at away
    omega
end CommitGolfCandidate.CapB
