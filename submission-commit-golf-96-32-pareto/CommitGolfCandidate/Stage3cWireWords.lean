import CommitGolfCandidate.Stage3cChunkPayload
import CommitGolfCandidate.Stage3cReadWindow
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W wordAt)
open Reader (window)

def pushBits (v n x : Nat) :=v+2^n*x
def completedBits (n : Nat) :=64*(n/64)
def heldValue (v n : Nat) :=v/2^(completedBits n)

theorem completed_add (n w : Nat) (small : w≤64) :
    (n+w)/64=n/64+(n%64+w)/64 ∧ n%64+w<128 := by omega

theorem word_at_end (v n x : Nat) :
    heldValue (pushBits v n x) n=heldValue v n+2^(n%64)*x := by
  have pn : 2^n=2^(completedBits n)*2^(n%64) := by rw [←pow_add];apply congrArg (fun k : Nat=>2^k);dsimp [completedBits];omega
  unfold heldValue pushBits
  rw [pn,Nat.mul_assoc,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]

theorem earlier_word (v n x j : Nat) (small : j<n/64) :
    window (pushBits v n x) (64*j) 64=window v (64*j) 64 := by
  let e:=64*j+64
  have enough : e≤n := by dsimp [e];omega
  have eqn : 2^n=2^e*2^(n-e) := by rw [←pow_add];congr 1;omega
  have low : pushBits v n x%2^e=v%2^e := by unfold pushBits;rw [eqn,Nat.mul_assoc,Nat.add_mul_mod_self_left]
  have part (a : Nat) : window a (64*j) 64 = (a%2^e)/2^(64*j) := by
    unfold window;dsimp [e];rw [pow_add,Nat.mod_mul_right_div_self] <;> rfl
  rw [part,part,low]

theorem new_prefix_bound {v n x w : Nat} (old : v<2^n) (source : x<2^w) :
    pushBits v n x<2^(n+w) := by
  have step:=Nat.mul_le_mul_left (2^n) (show x+1≤2^w from source)
  rw [Nat.mul_add,Nat.mul_one] at step;unfold pushBits;rw [pow_add];omega

theorem held_fits {v n : Nat} (bound : v<2^n) : heldValue v n<2^(n%64) := by
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
  rw [←pow_add,show n%64+completedBits n=n by dsimp [completedBits];omega];exact bound

structure PackedPrefix (s : MachineState) (base n v : Nat) : Prop where
  value : v<2^n
  ptr : s.getReg .x19=W (base+8*(n/64))
  bits : s.getReg .x24=W (n%64)
  held : (s.getReg .x23).toNat=heldValue v n
  words : ∀ j<n/64, (wordAt s (base+8*j)).toNat=window v (64*j) 64

theorem prefix_zero (s : MachineState) (base : Nat) (ptr : s.getReg .x19=W base) (bits : s.getReg .x24=0)
    (held : s.getReg .x23=0) : PackedPrefix s base 0 0 := by
  exact ⟨by decide,by simpa using ptr,bits,by rw [held];rfl,fun _ small=>by omega⟩

theorem next_held {s t : MachineState} {base n v w : Nat} (p : PackedPrefix s base n v)
    (wlim : w≤64) (data : ChunkPayload s t (n%64) w)
    (fits : (s.getMem (s.getReg .x10)).toNat<2^w) :
    (t.getReg .x23).toNat=heldValue (pushBits v n (s.getMem (s.getReg .x10)).toNat) (n+w) := by
  let x:=s.getMem (s.getReg .x10)
  let k:=n%64
  have h:=held_fits p.value
  have sum:=word_at_end v n x.toNat
  have kept : (s.getReg .x23).toNat<2^k:=p.held ▸ h
  have joined : appendedWord s k=W (heldValue (pushBits v n x.toNat) n) := by
    rw [appendedWord,joined_word _ _ _ kept,p.held,sum];rfl
  have cap:=new_prefix_bound p.value fits
  by_cases noStore : k+w<64
  · have same : completedBits (n+w)=completedBits n := by dsimp [completedBits,k] at *;omega
    rw [data.held,if_pos noStore,joined,W,BitVec.toNat_ofNat]
    unfold heldValue
    rw [same,Nat.mod_eq_of_lt]
    have hv := held_fits cap
    unfold heldValue at hv;rw [same] at hv
    exact hv.trans_le (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_lt (Nat.mod_lt _ (by decide))))
  · have endCount : completedBits (n+w)=completedBits n+64 := by dsimp [completedBits,k] at *;omega
    have hiPart : heldValue (pushBits v n x.toNat) (n+w)=heldValue (pushBits v n x.toNat) n/2^64 := by
      unfold heldValue;rw [endCount,pow_add,Nat.div_div_eq_div_mul]
    rw [data.held,if_neg noStore,hiPart,sum,←p.held]
    by_cases exactFit : k+w=64
    · rw [if_pos exactFit]
      have bound:=new_prefix_bound kept fits
      rw [exactFit] at bound
      exact (Nat.div_eq_of_lt bound).symm
    · rw [if_neg exactFit]
      exact joined_carry _ x k (Nat.le_of_lt (Nat.mod_lt _ (by decide))) kept
end CommitGolfCandidate.Chained.BinaryMachine.Writer
