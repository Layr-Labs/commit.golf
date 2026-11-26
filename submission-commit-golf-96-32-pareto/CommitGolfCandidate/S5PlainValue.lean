import CommitGolfCandidate.S5ParentBuffers
namespace CommitGolfCandidate.S5Machine
open CommitGolf Chained CommitGolf.Riscv RiscvZkvm.Rv64

theorem full_mask {h : Height} (wide : wireWidth h=256) (v : Output) : storeReply h v=v := by
  rw [storeReply,wide,Nat.mod_eq_of_lt v.isLt,BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem read_three (s : MachineState) (a : Nat) : readBuffer s a 96 =
    readBuffer s (a+64) 32 ++ readBuffer s (a+32) 32 ++ readBuffer s a 32 := by
  have x:=read_join s (a+32) 32 32
  have y:=read_join s a 32 64
  rw [show a+32+32=a+64 by omega] at x
  change _=(readBuffer s (a+32) 64).extractLsb' 0 512 at x
  change _=(readBuffer s a 96).extractLsb' 0 768 at y
  rw [BitVec.extractLsb'_eq_self] at x y
  rw [←y,←x]

theorem plain_value (H : Compression) (h : Height) (s : MachineState) (p : Nat) (simple : ¬chained h)
    (inside : p<count h) (pad : gaps s) :
    storeReply h (H (readBuffer s (srcAddr h p) 96))=nodeHash H h.val (physicalChild s h.val p 0)
      (physicalChild s h.val p 1) (physicalChild s h.val p 2) := by
  by_cases bottom : h.val=0
  · have full : wireWidth h=256 := by simp [wireWidth,bottom]
    apply (full_mask full _).trans
    have target : nodeHash H h.val (physicalChild s h.val p 0) (physicalChild s h.val p 1) (physicalChild s h.val p 2) =
        H (physicalChild s h.val p 2 ++ physicalChild s h.val p 1 ++ physicalChild s h.val p 0) := if_pos bottom
    exact (congrArg (fun q : BitVec 768=>H q) (read_three s (srcAddr h p))).trans target.symm
  · have ghost:=gap_pad inside bottom
    obtain ⟨high,low⟩:=pad h.val p 2 ghost
    have zero:=low (by intro h';exact simple ⟨h'.1,h'.2.1⟩)
    let a:=srcAddr h p
    have raw : readBuffer s a 96=parentBlock (physicalChild s h.val p 0) (physicalChild s h.val p 1) 0 :=
      read_parent_block s a _ _ 0 rfl rfl zero high
    have step : calls h=1 := (by decide +kernel : ∀ d : Height,¬chained d→calls d=1) h simple
    have dh : S5.height h.val=h := Fin.ext (Nat.mod_eq_of_lt h.isLt)
    let l:=physicalChild s h.val p 0
    let r:=physicalChild s h.val p 1
    have target : nodeHash H h.val l r (physicalChild s h.val p 2)=parentDigest H (S5.height h.val) l r := if_neg bottom
    apply Eq.trans _ target.symm
    rw [dh]
    have single : parentDigest H h l r=storeReply h (H (pack (.inl (workClass h,r++l)))) := by
      rw [parentDigest,queries,step];rfl
    apply Eq.trans _ single.symm
    exact congrArg (fun q : BitVec 768=>storeReply h (H q)) (raw.trans (parentBlock_plain h l r simple))
end CommitGolfCandidate.S5Machine
