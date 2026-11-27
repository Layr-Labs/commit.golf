import CommitGolfCandidate.Stage3cWritePrefix
import CommitGolfCandidate.Stage3cFieldCall
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (wordAt W)
def SourceWords (s : MachineState) (a : Nat) (v : Nat) : List Nat→Prop
  | []=>True
  | w::ws=>(wordAt s a).toNat=v%2^w ∧ SourceWords s (a+8) (v/2^w) ws

def Below (s t : MachineState) (base : Nat) := ∀ j<base,wordAt t j=wordAt s j
theorem source_below {s t : MachineState} (base a v : Nat) (ws : List Nat)
    (input : SourceWords s a v ws) (away : Below s t base) (lt : a+8*ws.length≤base) : SourceWords t a v ws := by
  induction ws generalizing a v with
  | nil=>trivial
  | cons w ws ih=>
    simp only [List.length_cons] at lt
    exact ⟨(congrArg BitVec.toNat (away _ (by omega))).trans input.1,ih _ _ input.2 (by omega)⟩

def preserved (r : Reg) := [Reg.x0,.x10,.x11,.x19,.x23,.x24,.x28,.x29,.x30,.x31].contains r=false
private theorem fetch_frame (short : Bool) (used : Nat) (r : Reg) (good : preserved r) :
    (chunkCode short used).all fun x=>keepsReg r x.2 := by
  unfold chunkCode
  simp only [List.all_append]
  have small : ∀ b : Bool,(fetchWord b).all fun x=>keepsReg r x.2 := by
    intro b;cases b <;> cases r <;> first | decide | simp [preserved] at good
  have joined : mix.all fun x=>keepsReg r x.2 := by cases r <;> first | decide | simp [preserved] at good
  have full : ∀ b : Bool,(spill b).all fun x=>keepsReg r x.2 := by
    intro b;cases b <;> cases r <;> first | decide | simp [preserved] at good
  rw [small,joined];split <;> first | rfl | simp [full]

theorem field_framed (n k : Nat) (s : MachineState) (r : Reg) (h : preserved r) :
    (pathEnd s (fieldCode n k)).getReg r=s.getReg r := by
  apply path_keeps_reg
  have part (ws : List Nat) (j : Nat) : (stream ws j).all fun x=>keepsReg r x.2 := by
    induction ws generalizing j with
    | nil=>rfl
    | cons w ws ih=>simp only [stream,List.all_append,fetch_frame _ _ _ h,ih,Bool.true_and]
  simp only [fieldCode,List.all_append,part,Bool.true_and]
  cases r <;> first | decide | simp [preserved] at h

private theorem below_chunk {s t : MachineState} {base n v k w : Nat} (old : PackedPrefix s base n v)
    (effect : ChunkPayload s t k w) (bounds : base+8*(n/64)<2^64) : Below s t base := by
  intro j hj
  by_cases low : k+w<64
  · exact congrFun (effect.memory.trans (if_pos low)) _
  · have mem:=effect.memory.trans (if_neg low)
    have ne : W j≠s.getReg .x19 := by
      rw [old.ptr];intro eq;have e:=congrArg BitVec.toNat eq
      simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bounds,Nat.mod_eq_of_lt (by omega : j<2^64)] at e
      omega
    exact (congrFun mem _).trans (MachineState.getMem_setMem_ne ne)

theorem stream_payload (s : MachineState) (ws : List Nat) (base n v a x : Nat)
    (old : PackedPrefix s base n v) (source : SourceWords s a x ws) (proper : Proper ws) (small : ws.sum≤256)
    (xFits : x<2^ws.sum) (pc : s.pc=pcAt 21) (remaining : s.getReg .x11=W ws.sum)
    (src : s.getReg .x10=W a) (threshold : s.getReg .x27=64)
    (align : base%8=0) (aa : a%8=0) (apart : a+8*ws.length≤base) (space : base+8*((n+ws.sum)/64)+32≤MEMORY_BYTES) :
    let t:=pathEnd s (stream ws (n%64))
    PackedPrefix t base (n+ws.sum) (pushBits v n x) ∧ Below s t base := by
  induction ws generalizing s n v a x with
  | nil=>
    have zero : x=0 := by change x<1 at xFits;omega
    simp only [List.sum_nil,Nat.add_zero,zero,pushBits,Nat.mul_zero,stream,pathEnd]
    exact ⟨old,fun _ _=>rfl⟩
  | cons w ws ih=>
    obtain ⟨positive,width,full,rest⟩:=proper
    let rem:=w+ws.sum
    let k:=n%64
    have part : min rem 64=w := by
      cases ws with
      | nil=>simp [rem,min_eq_left width]
      | cons z zs=>have f:=full (by simp);simp [rem,f]
    have short : decide (rem<64)=decide (w<64) := by
      rw [←part];by_cases h : rem<64 <;> simp [h] <;> omega
    have room := space
    change base+8*((n+rem)/64)+32≤2^36 at room
    have kBound : k<64:=Nat.mod_lt _ (by decide)
    have aValid : accessValid (s.getReg .x10) 8=true := by rw [src];apply access_ok <;> first | omega | (change _≤2^36;simp only [List.length_cons] at apart;omega)
    have dValid : accessValid (s.getReg .x19) 8=true := by rw [old.ptr];apply access_ok <;> first | omega | (change _≤2^36;omega)
    have enough : 0<rem :=by dsimp [rem];omega
    have effect:=chunk_payload s rem k enough small kBound pc remaining old.bits threshold aValid dValid
    obtain ⟨_,_,advance⟩:=chunk_run s pc rem k enough small kBound remaining old.bits threshold aValid dValid
    let u:=pathEnd s (chunkCode (w<64) (k+w))
    have word : (s.getMem (s.getReg .x10)).toNat=x%2^w := by rw [src];exact source.1
    have fit : (s.getMem (s.getReg .x10)).toNat<2^(min rem 64) := by rw [part,word];exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have bounds : base+8*(n/64)<2^64:=by omega
    have next:=push_prefix old advance effect bounds fit
    rw [part,short,word] at next
    rw [part,short] at effect
    have frame : Below s u base:=below_chunk old effect bounds
    have r0:=advance.remaining;have r1:=advance.source;have ip:=advance.pc
    rw [part,short] at r0 r1 ip
    have clipped : rem-w=ws.sum := by dsimp [rem];omega
    have src1 : u.getReg .x10=W (a+8):=r1.trans ((congrArg (·+8) src).trans (BitVec.ofNat_add a 8).symm)
    have restFit : x/2^w<2^ws.sum := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos w)).mpr (by rw [Nat.mul_comm,←pow_add];exact xFits)
    have restSpace : base+8*((n+w+ws.sum)/64)+32≤MEMORY_BYTES := by change _≤2^36;dsimp [rem] at room;omega
    have sumK : (k+w)%64=(n+w)%64 :=by dsimp [k];omega
    have nextThreshold : u.getReg .x27=64 := (path_keeps_reg _ s _ (fetch_frame _ _ .x27 (by simp [preserved]))).trans threshold
    have len : a+8+8*ws.length≤base := by simp only [List.length_cons] at apart;omega
    have recur:=ih u (n+w) _ (a+8) (x/2^w) next (source_below _ _ _ _ source.2 frame len) rest (by change w+ws.sum≤256 at small;omega)
      restFit ip (r0.trans (congrArg W clipped)) src1 nextThreshold (by omega) len restSpace
    have number : pushBits (pushBits v n (x%2^w)) (n+w) (x/2^w)=pushBits v n x := by
      unfold pushBits;rw [pow_add,Nat.add_assoc,Nat.mul_assoc,←Nat.mul_add,Nat.mod_add_div]
    rw [number,show n+w+ws.sum=n+(w::ws).sum by simp;omega] at recur
    simp only [stream,end_append]
    change PackedPrefix (pathEnd u (stream ws ((k+w)%64))) _ _ _ ∧ Below s (pathEnd u (stream ws ((k+w)%64))) base
    rw [sumK]
    exact ⟨recur.1,fun j hj=>(recur.2 j hj).trans (frame j hj)⟩
end CommitGolfCandidate.Chained.BinaryMachine.Writer
