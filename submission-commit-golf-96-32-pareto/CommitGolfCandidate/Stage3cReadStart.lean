import CommitGolfCandidate.Stage3cReadWord
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Reader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
open Check (Flow)
open Check.Sym (Calc compiled evaluated)
def startOps : List Calc:=[.sub .x13 .x13 .x31,.addi .x30 .x0 0,.addi .x29 .x0 0]
def wordKeep (q : Reg) := q≠.x13 ∧ q≠.x29 ∧ q≠.x30 ∧ q≠.x31

theorem start_word (o : Oracle) (s : MachineState) (n : Nat) (pos : 0<n) (bound : n≤256)
    (pc : s.pc=pcAt 27) (cnt : s.getReg .x13=W n) :
    let w:=min n 64
    ∃ t steps,steps≤7 ∧ Flow o s t steps 0 ∧ t.pc=pcAt 34 ∧ t.getReg .x31=W w ∧ t.getReg .x13=W (n-w) ∧
      t.getReg .x29=0 ∧ t.getReg .x30=0 ∧ t.mem=s.mem ∧ ∀ q,wordKeep q→t.getReg q=s.getReg q := by
  let w:=min n 64
  let short:=decide (n<64)
  let u:=pathEnd s (Select.code .word short)
  obtain ⟨head,ep,wsize,mem,regs⟩:=select_size o .word s n pos (by omega) pc cnt
  let t:=evaluated startOps u
  obtain ⟨run,out,tm,tp⟩:=compiled o startOps 31 u ep (by decide +kernel) (by change ∀ e∈([] : List (Check.Sym.Expr×Nat)),_;simp)
  let a:=if short then 4 else 3
  have lim : a≤4:=by dsimp [a];split <;> decide
  have ctr : u.getReg .x13=W n:=(regs _ (by decide)).trans cnt
  have sub : t.getReg .x13=W (n-w):=by
    apply (out .x13).trans;change u.getReg .x13-u.getReg .x31=_;rw [ctr,show u.getReg .x31=W w from wsize]
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by dsimp [w];omega) (Nat.min_le_left ..)
  refine ⟨t,a+3,by omega,head.trans run,tp,(out .x31).trans wsize,sub,out .x29,out .x30,tm.trans mem,?_⟩
  intro q good;apply (out q).trans;apply Eq.trans _ (regs q good.2.2.2)
  cases q <;> first | rfl | (simp [wordKeep] at good)

structure DecodedWord (o : Oracle) (s t : MachineState) (base bytes v bit n steps k : Nat) : Prop where
  run : Flow o s t steps 0
  pc : t.pc=pcAt 58
  cursor : Cursor t base bytes v (bit+min n 64) k
  word : (t.getReg .x30).toNat=window v bit (min n 64)
  rem : t.getReg .x13=W (n-min n 64)
  mem : t.mem=s.mem
  keep : ∀ q,readKeep q → q≠.x13 → t.getReg q=s.getReg q

theorem decode_word (o : Oracle) (s : MachineState) (base bytes v bit k n : Nat) (pos : 0<n) (bound : n≤256)
    (room : base+bytes≤MEMORY_BYTES) (space : bit+n≤8*bytes) (kmax : k<8) (pc : s.pc=pcAt 27)
    (rem : s.getReg .x13=W n) (c : Cursor s base bytes v bit k) :
    ∃ t steps buffered,steps≤104 ∧ buffered<8 ∧ DecodedWord o s t base bytes v bit n steps buffered := by
  let w:=min n 64
  obtain ⟨u,a,al,head,ep,ct,remaining,offset,empty,mem,regs⟩:=start_word o s n pos bound pc rem
  have cu:=c.same mem (regs _ (by simp [wordKeep])) (regs _ (by simp [wordKeep])) (regs _ (by simp [wordKeep])) (regs _ (by simp [wordKeep]))
  have low : (u.getReg .x30).toNat=window v bit 0:=by rw [empty];simp [window,Nat.mod_one]
  obtain ⟨t,b,nextK,bl,small,word⟩:=word_value o u base bytes v bit k 0 w ((w+31)/32) rfl kmax
    (by dsimp [w];omega) (by dsimp [w];omega) room ep (by simpa only [Nat.add_zero] using cu) offset ct low
  have bill : b≤97:=by dsimp [w] at bl;omega
  refine ⟨t,a+b,nextK,by omega,small,⟨head.trans word.run,word.pc,?_,?_,(word.keep .x13 (by simp [readKeep])).trans remaining,
    word.mem.trans mem,?_⟩⟩
  · simpa only [Nat.zero_add] using word.cursor
  · simpa only [Nat.zero_add] using word.value
  · intro q safe ne;apply (word.keep q safe).trans;apply regs
    refine ⟨ne,?_,?_,?_⟩ <;> intro e <;> subst q <;> apply safe <;> decide
end CommitGolfCandidate.Chained.BinaryMachine.Reader
