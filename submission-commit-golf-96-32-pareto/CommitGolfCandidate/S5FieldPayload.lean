import CommitGolfCandidate.S5StreamPayload
import CommitGolfCandidate.S5InputBlock
namespace CommitGolfCandidate.S5Machine.Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W wordAt)
open Reader (window)

private theorem source_windows (s : MachineState) (a x : Nat) (ws : List Nat) (ok : Proper ws) (fit : x<2^ws.sum)
    (read : ∀ j<ws.length,(wordAt s (a+8*j)).toNat=window x (64*j) 64) : SourceWords s a x ws := by
  induction ws generalizing a x with
  | nil=>trivial
  | cons w ws ih=>
    obtain ⟨pos,wlim,full,rest⟩:=ok
    have first : (wordAt s a).toNat=x%2^64 := by simpa only [Nat.mul_zero,Nat.add_zero,window,pow_zero,Nat.div_one] using read 0 (by simp)
    cases ws with
    | nil=>
      change x<2^(w+0) at fit;rw [Nat.add_zero] at fit
      have f : x<2^64:=fit.trans_le (Nat.pow_le_pow_right (by decide) wlim)
      exact ⟨first.trans ((Nat.mod_eq_of_lt f).trans (Nat.mod_eq_of_lt fit).symm),True.intro⟩
    | cons z zs=>
      obtain rfl : w=64:=full (by simp)
      have cap : x/2^64<2^(z::zs).sum := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
        (by rw [Nat.mul_comm,←pow_add];exact fit)
      refine ⟨first,ih (a+8) (x/2^64) rest cap ?_⟩
      intro j hj
      have orig:=read (j+1) (by simp only [List.length_cons] at *;omega)
      rw [show a+8+8*j=a+8*(j+1) by omega,orig]
      unfold window;rw [Nat.div_div_eq_div_mul,←pow_add,show 64*(j+1)=64+64*j by omega]

theorem source_field (s : MachineState) (a width bytes : Nat) (v : BitVec (8*bytes)) (read : readBuffer s a bytes=v)
    (fit : v.toNat<2^width) (room : 8*(parts width).length≤bytes) (aligned : a%8=0) :
    SourceWords s a v.toNat (parts width) := by
  obtain ⟨proper,total⟩:=parts_valid width
  apply source_windows _ _ _ _ proper (by rw [total];exact fit)
  intro j hj
  have slice:=read_buffer_slice s a bytes (8*j) 8 (by omega)
  rw [read,read_word _ _ (by omega)] at slice
  change (s.getMem (BitVec.ofNat 64 (a+8*j))).toNat=_
  rw [←slice,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  unfold window;rw [show 8*(8*j)=64*j by omega]

theorem field_payload (s : MachineState) (width base n v a x : Nat) (old : PackedPrefix s base n v)
    (source : SourceWords s a x (parts width)) (small : width≤256) (fit : x<2^width) (pc : s.pc=pcAt 21)
    (size : s.getReg .x11=W width) (src : s.getReg .x10=W a) (threshold : s.getReg .x27=64)
    (aligned : base%8=0) (aa : a%8=0) (apart : a+32≤base) (space : base+8*((n+width)/64)+32≤MEMORY_BYTES) :
    let t:=pathEnd s (fieldCode width (n%64))
    PackedPrefix t base (n+width) (pushBits v n x) ∧ Below s t base := by
  let ws:=parts width
  let u:=pathEnd s (stream ws (n%64))
  obtain ⟨proper,total⟩:=parts_valid width
  have count : ws.length≤4 := by simp only [ws,parts,List.length_append,List.length_replicate];split <;> simp <;> omega
  obtain ⟨prefixOK,low⟩:=stream_payload s ws base n v a x old source proper (total ▸ small) (total ▸ fit) pc (total ▸ size) src threshold aligned aa (by omega) (total ▸ space)
  have sa : a+8*ws.length≤MEMORY_BYTES:=by omega
  have da : base+8*(n/64)+8*ws.length≤MEMORY_BYTES:=by omega
  obtain ⟨_,ip,zero,_,_⟩:=stream_run s ws (n%64) a (base+8*(n/64)) proper (total ▸ small) (Nat.mod_lt _ (by decide))
    pc (total ▸ size) old.bits threshold src old.ptr aa (by omega) sa da
  obtain ⟨_,_,mem,regs⟩:=finished u ip zero
  have sameReg (r : Reg) : (pathEnd u finish).getReg r=u.getReg r := by cases r <;> first | rfl | exact congrFun regs _
  have sameWord (j : Nat) : wordAt (pathEnd u finish) j=wordAt u j := congrFun mem _
  simp only [fieldCode,end_append]
  change PackedPrefix (pathEnd u finish) _ _ _ ∧ Below s (pathEnd u finish) base
  rw [show n+width=n+ws.sum from congrArg (n+·) total.symm]
  exact ⟨⟨prefixOK.value,(sameReg _).trans prefixOK.ptr,(sameReg _).trans prefixOK.bits,
    (congrArg BitVec.toNat (sameReg _)).trans prefixOK.held,fun j hj=>(congrArg BitVec.toNat (sameWord _)).trans (prefixOK.words j hj)⟩,
    fun j hj=>(sameWord _).trans (low j hj)⟩
end CommitGolfCandidate.S5Machine.Writer
