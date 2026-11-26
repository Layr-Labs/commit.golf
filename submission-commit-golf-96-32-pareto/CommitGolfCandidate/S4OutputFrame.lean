import CommitGolfCandidate.S4RawProof
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Trapdoor Digest)
open Machine (W byte Moved Wrote proofBase)

def Contains (s : MachineState) (a : Nat) (p : Proof) := ∀ j (b : j<p.length),byte s (a+j)=p[j]

theorem containsEmpty (s : MachineState) (a : Nat) : Contains s a []:=fun j h=>False.elim (Nat.not_lt_zero j h)

theorem Contains.mem {s t : MachineState} {a : Nat} {p : Proof} (known : Contains s a p) (eqv : t.mem=s.mem) :
    Contains t a p:=by intro j b;simpa only [byte,MachineState.getByte,MachineState.getMem,eqv] using known j b

theorem Contains.scratch {s t : MachineState} {a : Nat} {p : Proof} {v : Nat→Byte} (known : Contains s proofBase p)
    (w : Wrote s t a 1 v) (low : a+1≤proofBase) (bound : proofBase+p.length≤2^64) : Contains t proofBase p:=by
  intro j bj;exact (w _ (by omega)).trans ((if_neg (by omega)).trans (known _ bj))

theorem Contains.copy {s t : MachineState} {a src n : Nat} {xs ys : Proof} (known : Contains s a xs)
    (fromSource : Contains s src ys) (length : ys.length=n) (m : Moved s t src (a+xs.length) n)
    (bound : a+xs.length+n≤2^64) : Contains t a (xs++ys) := by
  intro j bj;have total:=bj;rw [List.length_append,length] at total
  rw [m (a+j) (by omega)]
  by_cases left : j<xs.length
  · rw [List.getElem_append_left left,if_neg (by omega)];exact known j left
  · rw [List.getElem_append_right (by omega),if_pos (by omega),show a+j-(a+xs.length)=j-xs.length by omega]
    exact fromSource _ (by omega)

theorem fieldRead {s : MachineState} {src n : Nat} {v : Digest} (nbytes : n≤32)
    (read : readBuffer s src 32=v) : Contains s src (mainBytes (8*n,v)) := by
  intro j bj
  have length : (mainBytes (8*n,v)).length=n:=by simp [mainBytes]
  have lim : j<n:=length ▸ bj
  rw [show (mainBytes (8*n,v))[j]=v.extractLsb' (8*j) 8 by simp only [mainBytes,List.getElem_map,List.getElem_range]]
  exact (read_buffer_byte s src 32 j (by omega)).symm.trans (congrArg (fun x : Digest=>x.extractLsb' (8*j) 8) read)

theorem saltRead {s : MachineState} {src : Nat} {v : Late.Salt}
    (read : readBuffer s src 24=v) : Contains s src (mainBytes (192,v.setWidth 256)) := by
  intro j bj
  have lim : j<24:=by simpa only [mainBytes,List.length_map,List.length_range] using bj
  rw [show (mainBytes (192,v.setWidth 256))[j]=(v.setWidth 256).extractLsb' (8*j) 8 by
    simp only [mainBytes,List.getElem_map,List.getElem_range],BitVec.extractLsb'_setWidth_of_le (by omega)]
  exact (read_buffer_byte s src 24 j lim).symm.trans (congrArg (fun x : Late.Salt=>x.extractLsb' (8*j) 8) read)

theorem reportBytes (s : MachineState) (p : Proof) (steps : Nat) (len : s.getReg .x11=W p.length)
    (bound : p.length≤Late.submission.sizes.proof) (written : Contains s proofBase p) :
    Late.submission.readProof ⟨.success,s,steps,0⟩=p := by
  have limit : p.length<2^64:=by change p.length≤17179869184 at bound;omega
  have raw : (s.getReg .x11).toNat=p.length:=by rw [len,BitVec.toNat_ofNat,Nat.mod_eq_of_lt limit]
  have success : Late.submission.openingSucceeded ⟨.success,s,steps,0⟩=true := by
    change true && decide ((s.getReg .x11).toNat≤Late.submission.sizes.proof)=true;rw [raw,decide_eq_true bound];rfl
  rw [Submission.readProof,if_pos success];simp only [raw]
  apply List.ext_getElem
  · simp
  · intro j bj bp;simp only [List.getElem_map,List.getElem_range];exact written j bp
end CommitGolfCandidate.S4.Open
