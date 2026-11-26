import CommitGolfCandidate.ReconstructedCheckParentCall

namespace CommitGolfCandidate.Reconstruction.CheckParentWords
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckValues CheckParentRun CheckParentFirst CheckParentPlan CheckParentCall
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def digWord (x : Binding.Digest) (i : Nat) := (pack x).extractLsb' (64*i) 64

theorem high (x : Binding.Digest) : digWord x 3=x.2 :=
  BitVec.extractLsb'_append_eq_left

theorem low (x : Binding.Digest) (i : Nat) (h : i<3) : digWord x i=x.1.extractLsb' (64*i) 64 :=
  BitVec.extractLsb'_append_eq_of_add_le (by omega)

theorem keyHalf (k : Key) (i : Fin 8) :
    (encodeKey k).extractLsb' (64*i.val) 64=digWord (if i.val<4 then k.1 else k.2) (i.val%4) := by
  by_cases h : i.val<4
  · rw [ite_eq_left h,Nat.mod_eq_of_lt h,encodeKey,BitVec.extractLsb'_append_eq_of_add_le (by omega)]
    rfl
  · rw [ite_eq_right h,encodeKey,BitVec.extractLsb'_append_eq_of_le (by omega)]
    change _=(pack k.2).extractLsb' _ 64
    congr 1;have:=i.isLt;omega

def Source (env : Env) (l r : Binding.Digest) :=
  ∀ i : Fin 8, (dataWord i).val env=digWord (if i.val<4 then l else r) (i.val%4)

def Answers (env : Env) (o : Oracle) (seed : Key) (d : Nat) :=
  ∀ q<work d, ∀ i<4, env.answer q i=(result o seed q).extractLsb' (64*i) 64

theorem first_key (env : Env) (d : Nat) (l r : Binding.Digest) (source : Source env l r) (i : Fin 8) :
    (keyWord d i).val env=(encodeKey (pairKey (d+1) l r)).extractLsb' (64*i.val) 64 := by
  rw [keyHalf]
  have s := source i
  by_cases isLo : i.val%4<3
  · have n3 : i.val≠3 := by omega
    have n7 : i.val≠7 := by omega
    rw [keyWord,ite_eq_right (by simp [n3,n7]),s,low _ _ isLo,low _ _ isLo]
    split <;> rfl
  · have three : i.val%4=3 := by omega
    rw [three,high] at s ⊢
    by_cases left : i.val<4
    · have li : i.val=3 := by omega
      simp only [left,ite_true] at s ⊢
      simp only [pairKey,marked,li,keyWord,true_or,ite_true] at s ⊢
      by_cases modded : modulus (d+1)=0
      · simp [modded,Term.val,Bin.run,s,BitVec.or_comm]
      · simp [modded,childMask,s]
    · have ri : i.val=7 := by have:=i.isLt;omega
      simp only [left,ite_false] at s ⊢
      simp only [pairKey,marked,ri,keyWord,or_true,ite_true] at s ⊢
      by_cases modded : modulus (d+1)=0
      · simp [modded,Term.val,Bin.run,s,childMask,BitVec.or_comm]
      · simp [modded,Term.val,Bin.run,s]

theorem row_word (o : Oracle) (env : Env) (d : Nat) (l r : Binding.Digest) (source : Source env l r)
    (answers : Answers env o (pairKey (d+1) l r) d) (q : Nat) (bound : q<work d) (i : Fin 8) :
    (rowWord d q i).val env = (encodeKey (key o (pairKey (d+1) l r) q)).extractLsb' (64*i.val) 64 := by
  cases q with
  | zero => exact first_key env d l r source i
  | succ n =>
    rw [keyHalf]
    by_cases lower : i.val<4
    · rw [ite_eq_left lower,Nat.mod_eq_of_lt lower]
      simp only [rowWord,Nat.succ_ne_zero,ite_false,lower,ite_true,Nat.add_sub_cancel,Term.val]
      rw [answers n (by omega) i lower]
      exact (congrArg (fun v : BitVec 256 => v.extractLsb' (64*i.val) 64)
        (Binding.pack_unpack (result o (pairKey (d+1) l r) n))).symm
    · rw [ite_eq_right lower]
      simp only [rowWord,Nat.succ_ne_zero,ite_false,lower,Term.val]
      change 0=digWord zeroDigest (i.val%4)
      rw [digWord,show pack zeroDigest=0#256 by rfl]
      simp

theorem output_word (o : Oracle) (env : Env) (d : Fin 24) (l r : Binding.Digest)
    (answers : Answers env o (pairKey (d.val+1) l r) d) (i : Fin 4) :
    (finalWord d i).val env = digWord (parent (oracleCompression o) d l r) i := by
  let seed := pairKey (d.val+1) l r
  let y := result o seed (work d-1)
  have raw : env.answer (work d-1) i=y.extractLsb' (64*i.val) 64 :=
    answers _ (by have h : 1≤work d:=Nat.le_max_left ..;omega) i i.isLt
  have par : parent (oracleCompression o) d l r = project d (unpack y) := rfl
  rw [par]
  by_cases last : i.val=3
  · rw [last,high]
    rw [last] at raw
    have hi : (unpack y).2=y.extractLsb' (64*3) 64 := rfl
    by_cases root : d.val=0
    · simp only [finalWord,root,or_true,ite_true,Term.val,raw]
      rw [project_of_canonical 0 (unpack y) (show Canonical 0 (unpack y) from (unpack y).2.isLt),hi]
      simpa only [root] using raw
    · simp only [finalWord,ne_eq,not_true_eq_false,false_or,root,ite_false]
      have range := ranges d (by have:=d.isLt;omega)
      by_cases modded : modulus d=0
      · have canon : (project d (unpack y)).2=(unpack y).2 &&& BitVec.ofNat 64 (2^(width d-192)-1) := by
          apply BitVec.eq_of_toNat_eq
          rw [project_hi,BitVec.toNat_and,BitVec.toNat_ofNat]
          have p := Nat.pow_le_pow_right (n:=2) (by decide) (show width d-192≤64 by omega)
          rw [Nat.mod_eq_of_lt (show 2^(width d-192)-1<2^64 by have:=Nat.two_pow_pos (width d-192);omega),
            Nat.and_two_pow_sub_one_eq_mod]
          simp [radix,modded]
        simp [modded,Term.val,Bin.run,raw,canon,hi,BitVec.and_comm]
      · have small : ∀ j : Fin 24, modulus j<2^64 := by decide
        have nz : BitVec.ofNat 64 (modulus d) ≠ 0 := by
          intro eq;have n:=congrArg BitVec.toNat eq
          simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (small d)] at n
          exact modded n
        have nz' : BitVec.ofNat 64 (modulus d) ≠ 0#64 := nz
        simp [modded,Term.val,Bin.run,rv64_remu,nz,nz',raw]
        apply BitVec.eq_of_toNat_eq
        rw [project_hi,BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (small d),hi]
        simp [radix,modded]
  · have lt : i.val<3 := by have := i.isLt;omega
    rw [finalWord,ite_eq_left (Or.inl last),Term.val,raw,low _ _ lt]
    change _=(unpack y).1.extractLsb' (64*i.val) 64
    have same := low (unpack y) i lt
    exact (congrArg (fun v : BitVec 256 => v.extractLsb' (64*i.val) 64) (Binding.pack_unpack y)).symm.trans same

end CommitGolfCandidate.Reconstruction.CheckParentWords
