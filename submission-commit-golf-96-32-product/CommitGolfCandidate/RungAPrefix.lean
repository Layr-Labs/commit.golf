import CommitGolfCandidate.R4CommitLeaf
import CommitGolfCandidate.R4LaneCode
import CommitGolfCandidate.RungAInterface
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 R4
open Late (pcAt sharedSaltAddr)
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1400000

structure Inputs (o : Oracle) (m : Message) (r : Tape) (s : MachineState) : Prop where
  rows : ∀ i : Index, readBuffer s (finalRowAddress i.val) 96=finalRow o m r i
  salts : ∀ i : Index, readBuffer s (sharedSaltAddr i.val) 24=pairSalts r i
  fresh : ∀ a, a<MEMORY_BYTES → (a<C_MSG ∨ a≥C_TD ∧ (a<C_ROW ∨ C_ROW+1543503872≤a)) → s.getByte (Z a)=0

theorem prefixRun (oracle : Oracle) (msg : Message) (rand : Tape) (s0 : MachineState) (sd : AfterDraw msg rand s0) :
    ∃ s2, MRun oracle s0 151001104 s2 503322640 50331648 ∧
      s2.pc=pcAt 131123 ∧ Env s2 ∧ Inputs oracle msg rand s2 := by
  have cm : C_MSG=4096:=rfl
  have td0 : C_TD=4294971424:=rfl
  have row0 : C_ROW=5905584160:=rfl
  have lr : Late.rowBase=5905584160:=rfl
  have ln : LENGTH=16777216:=rfl
  have mb : MEMORY_BYTES=68719476736:=rfl
  have h768 : COMPRESSION_INPUT_LENGTH=768:=rfl
  have hpc:=sd.pc
  have hx2:=sd.db
  have hx5:=sd.mode
  have hx8:=sd.msg
  have hx9:=sd.td
  have hx10:=sd.cursor
  have hx11:=sd.width
  have hx13:=sd.kind
  have hx18:=sd.row
  have hx19:=sd.stop
  have hx26:=sd.root
  have hmsg0 (i : Index) (j : Nat) (hj : j<256) : s0.getByte (Z (C_MSG+256*i.val+j))=(msg i).extractLsb' (8*j) 8:=by
    have hi : i.val<16777216:=i.isLt
    rw [sd.frame _ (by omega) (fun _ _=>Or.inl (by omega))]
    exact commit_initial_msg_byte msg i j hj 
  have zero (q : Nat) (lo : C_TD≤q) (hi : q<C_ROW) : s0.getByte (Z q)=0:=by
    rw [sd.frame _ (by omega) (fun _ _=>Or.inl (by omega))]
    apply commit_initial_zero_byte;omega
  have empty (j : Fin (LENGTH/2)) (off : Nat) (ofst : off=64 ∨ off=112) : readBuffer s0 (C_ROW+184*j.val+off) 8=0:=by
    have bd : j.val<8388608:=j.isLt
    apply readBuffer_zero_of_bytes;intro k hk
    rw [sd.frame _ (by rcases ofst with rfl|rfl <;> omega) (fun p _=>by by_cases e:p=j.val <;> rcases ofst with rfl|rfl <;> omega)]
    apply commit_initial_zero_byte;rcases ofst with rfl|rfl <;> omega
  have hsalt0 (j : Fin (LENGTH/2)) := And.intro (sd.even j) (sd.odd j)
  have hgap0 (j : Fin (LENGTH/2)) := And.intro (empty j 64 (Or.inl rfl)) (empty j 112 (Or.inr rfl))
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_ROW : C_ROW = 5905584160 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hlb1 : levelBase 1 = 536870912 := by decide
  have htd := trapdoorBytes_eq
  have hro := rowOff_eq
  obtain ⟨s1, hr1A, hpc1, hx2_1, hx5_1, _, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1,
    hx18_1, hx19_1, hx26_1, h1A, hp1A⟩ :=
    commit_phase1A h768 oracle msg s0 hpc hx2 hx5 hx8 hx9 hx10 hx11 hx13 hx18 hx19 hx26 hmsg0
  obtain ⟨s2, hr1B, hpc2, hx2_2, hx5_2, hx9_2, hx10_2, hx11_2, hx12_2, hx13_2,
    _, hx19_2, hx26_2, h1B, hp1B⟩ :=
    commit_phase1B h768 oracle msg s1 hpc1 hx2_1 hx5_1 hx9_1 hx10_1 hx11_1 hx12_1 hx13_1
      hx18_1 hx19_1 hx26_1 h1A
  have hrow2 : ∀ p : Fin (LENGTH / 2),
      readBuffer s2 (C_ROW + 184 * p.val) 32 =
        leafA (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val, by omega⟩) ∧
      readBuffer s2 (C_ROW + 184 * p.val + 32) 32 =
        leafB (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val, by omega⟩) ∧
      readBuffer s2 (C_ROW + 184 * p.val + 64) 8 = 0 ∧
      readBuffer s2 (C_ROW + 184 * p.val + 72) 24 = pairSaltEven (rand p) ∧
      readBuffer s2 (C_ROW + 184 * p.val + 88) 24 = pairSaltOdd (rand p) ∧
      readBuffer s2 (C_ROW + 184 * p.val + 112) 8 = 0 ∧
      readBuffer s2 (C_ROW + 184 * p.val + 120) 32 =
        leafA (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val + 1, by omega⟩) ∧
      readBuffer s2 (C_ROW + 184 * p.val + 152) 32 =
        leafB (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val + 1, by omega⟩) := by
    intro p; have hp := p.isLt
    obtain ⟨ha0, hb0, ha1, hb1⟩ := h1B p
    have hmid_pres : ∀ off n, 64 ≤ off → off + n ≤ 120 →
        readBuffer s2 (C_ROW + 184 * p.val + off) n = readBuffer s0 (C_ROW + 184 * p.val + off) n := by
      intro off n hlo hhi
      apply readBuffer_congr; intro j hj
      have h1 := hp1B (C_ROW + 184 * p.val + off + j) (by omega) (fun p' _ => by
        by_cases heq : p' = p.val
        · subst heq; omega
        · omega)
      have h0 := hp1A (C_ROW + 184 * p.val + off + j) (by omega) (by omega)
      exact h1.trans h0
    exact ⟨ha0, hb0,
      (hmid_pres 64 8 (by omega) (by omega)).trans (hgap0 p).1,
      (hmid_pres 72 24 (by omega) (by omega)).trans (hsalt0 p).1,
      (hmid_pres 88 24 (by omega) (by omega)).trans (hsalt0 p).2,
      (hmid_pres 112 8 (by omega) (by omega)).trans (hgap0 p).2,
      ha1, hb1⟩
  refine ⟨s2,hr1A.trans hr1B,hpc2,⟨hx5_2,hx13_2,hx11_2,hx26_2⟩,?_,?_,?_⟩
  · intro i
    have ib : i.val<16777216:=i.isLt
    let p : Fin (LENGTH/2):=⟨i.val/2,by change i.val/2<8388608;omega⟩
    obtain ⟨aa,bb,g0,se,so,g1,ac,bc⟩:=hrow2 p
    by_cases even : i.val%2=0
    · have id : (⟨2*p.val,by dsimp [p];omega⟩ : Index)=i:=Fin.ext (by dsimp [p];omega)
      rw [id] at aa bb
      have addr : finalRowAddress i.val=C_ROW+184*p.val:=by simp [finalRowAddress,p,even,Late.rowBase,C_ROW]
      have salt : pairSalts rand i=pairSaltEven (rand p):=by simp [pairSalts,even,p]
      have parity : i.val.testBit 0=false:=by simp [Nat.testBit_eq_decide_div_mod_eq,even]
      rw [addr,finalRow,parity,salt]
      exact Late.even_row _ _ _ _ _ aa bb g0 se
    · have odd : i.val%2=1:=by omega
      have id : (⟨2*p.val+1,by dsimp [p];omega⟩ : Index)=i:=Fin.ext (by dsimp [p];omega)
      rw [id] at ac bc
      have addr : finalRowAddress i.val=C_ROW+184*p.val+88:=by simp [finalRowAddress,p,odd,Late.rowBase,C_ROW]
      have salt : pairSalts rand i=pairSaltOdd (rand p):=by simp [pairSalts,even,p]
      have parity : i.val.testBit 0=true:=by simp [Nat.testBit_eq_decide_div_mod_eq,odd]
      rw [addr,finalRow,parity,salt]
      apply Late.odd_row _ _ _ _ _ so
      · simpa only [Nat.add_assoc] using g1
      · rw [show C_ROW+184*p.val+88+32=C_ROW+184*p.val+120 by omega]
        exact ac
      · rw [show C_ROW+184*p.val+88+64=C_ROW+184*p.val+152 by omega]
        exact bc
  · intro i
    let p : Fin (LENGTH/2):=⟨i.val/2,by have:=i.isLt;omega⟩
    by_cases h : i.val%2=0
    · have eqn : sharedSaltAddr i.val=C_ROW+184*p.val+72:=by unfold sharedSaltAddr;dsimp [p];omega
      have val : pairSalts rand i=pairSaltEven (rand p):=by unfold pairSalts;rw [if_pos h]
      rw [eqn,val];exact (hrow2 p).2.2.2.1
    · have odd : i.val%2=1:=by omega
      have eqn : sharedSaltAddr i.val=C_ROW+184*p.val+88:=by unfold sharedSaltAddr;dsimp [p];omega
      have val : pairSalts rand i=pairSaltOdd (rand p):=by unfold pairSalts;rw [if_neg h]
      rw [eqn,val];exact (hrow2 p).2.2.2.2.1
  · intro a ba region
    have bound : a<2^64:=by omega
    rw [hp1B a bound (by intro p hp;rcases region with l|⟨lo,l|l⟩ <;> dsimp [C_ROW,C_TD,C_MSG] at * <;> omega)]
    rw [hp1A a bound (by dsimp [C_MSG,C_TD] at *;omega)]
    rw [sd.frame a bound (by intro j hj;change j<8388608 at hj;dsimp [Late.rowBase,C_ROW,C_MSG] at *;omega)]
    apply commit_initial_zero_byte
    dsimp [C_MSG,C_TD] at *;omega
end CommitGolfCandidate.RungA
