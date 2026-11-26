import CommitGolfCandidate.PairFill
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 200000

theorem safeStore (s : MachineState) (flagOK : accessValid (s.getReg .x22) 1)
    (src : ∀ j : Fin 4, accessValid (s.getReg .x21+BitVec.ofNat 64 (8*j.val)) 8)
    (dst : ∀ j : Fin 4, accessValid (s.getReg .x23+BitVec.ofNat 64 (0+8*j.val)) 8) :
    safeSteps storeOps s := by
  intro ⟨k,h⟩
  change k < 10 at h
  interval_cases k
  · rfl
  · change accessValid ((s.setReg .x7 1).getReg .x22 + 0#64) 1 = true
    simpa only [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7≠.x22),BitVec.add_zero] using flagOK
  · change accessValid ((stepPrefix storeOps s 2).getReg .x21 + signExtend12 0) 8 = true
    have ptr : (stepPrefix storeOps s 2).getReg .x21 = s.getReg .x21 := by
      simp [stepPrefix,storeOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨0,by decide⟩
  · change accessValid ((stepPrefix storeOps s 3).getReg .x23 + signExtend12 0) 8 = true
    have ptr : (stepPrefix storeOps s 3).getReg .x23 = s.getReg .x23 := by
      simp [stepPrefix,storeOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨0,by decide⟩
  · change accessValid ((stepPrefix storeOps s 4).getReg .x21 + signExtend12 8) 8 = true
    have ptr : (stepPrefix storeOps s 4).getReg .x21 = s.getReg .x21 := by
      simp [stepPrefix,storeOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨1,by decide⟩
  · change accessValid ((stepPrefix storeOps s 5).getReg .x23 + signExtend12 8) 8 = true
    have ptr : (stepPrefix storeOps s 5).getReg .x23 = s.getReg .x23 := by
      simp [stepPrefix,storeOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨1,by decide⟩
  · change accessValid ((stepPrefix storeOps s 6).getReg .x21 + signExtend12 16) 8 = true
    have ptr : (stepPrefix storeOps s 6).getReg .x21 = s.getReg .x21 := by
      simp [stepPrefix,storeOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨2,by decide⟩
  · change accessValid ((stepPrefix storeOps s 7).getReg .x23 + signExtend12 16) 8 = true
    have ptr : (stepPrefix storeOps s 7).getReg .x23 = s.getReg .x23 := by
      simp [stepPrefix,storeOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨2,by decide⟩
  · change accessValid ((stepPrefix storeOps s 8).getReg .x21 + signExtend12 24) 8 = true
    have ptr : (stepPrefix storeOps s 8).getReg .x21 = s.getReg .x21 := by
      simp [stepPrefix,storeOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨3,by decide⟩
  · change accessValid ((stepPrefix storeOps s 9).getReg .x23 + signExtend12 24) 8 = true
    have ptr : (stepPrefix storeOps s 9).getReg .x23 = s.getReg .x23 := by
      simp [stepPrefix,storeOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨3,by decide⟩

theorem safeFillright (s : MachineState) (src : ∀ j : Fin 4, accessValid (s.getReg .x19+BitVec.ofNat 64 (8*j.val)) 8)
    (dst : ∀ j : Fin 4, accessValid (s.getReg .x23+BitVec.ofNat 64 (32+8*j.val)) 8) :
    safeSteps fillRightOps s := by
  intro ⟨k,h⟩
  change k < 8 at h
  interval_cases k
  · change accessValid ((stepPrefix fillRightOps s 0).getReg .x19 + signExtend12 0) 8 = true
    have ptr : (stepPrefix fillRightOps s 0).getReg .x19 = s.getReg .x19 := by
      simp [stepPrefix,fillRightOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨0,by decide⟩
  · change accessValid ((stepPrefix fillRightOps s 1).getReg .x23 + signExtend12 32) 8 = true
    have ptr : (stepPrefix fillRightOps s 1).getReg .x23 = s.getReg .x23 := by
      simp [stepPrefix,fillRightOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨0,by decide⟩
  · change accessValid ((stepPrefix fillRightOps s 2).getReg .x19 + signExtend12 8) 8 = true
    have ptr : (stepPrefix fillRightOps s 2).getReg .x19 = s.getReg .x19 := by
      simp [stepPrefix,fillRightOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨1,by decide⟩
  · change accessValid ((stepPrefix fillRightOps s 3).getReg .x23 + signExtend12 40) 8 = true
    have ptr : (stepPrefix fillRightOps s 3).getReg .x23 = s.getReg .x23 := by
      simp [stepPrefix,fillRightOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨1,by decide⟩
  · change accessValid ((stepPrefix fillRightOps s 4).getReg .x19 + signExtend12 16) 8 = true
    have ptr : (stepPrefix fillRightOps s 4).getReg .x19 = s.getReg .x19 := by
      simp [stepPrefix,fillRightOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨2,by decide⟩
  · change accessValid ((stepPrefix fillRightOps s 5).getReg .x23 + signExtend12 48) 8 = true
    have ptr : (stepPrefix fillRightOps s 5).getReg .x23 = s.getReg .x23 := by
      simp [stepPrefix,fillRightOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨2,by decide⟩
  · change accessValid ((stepPrefix fillRightOps s 6).getReg .x19 + signExtend12 24) 8 = true
    have ptr : (stepPrefix fillRightOps s 6).getReg .x19 = s.getReg .x19 := by
      simp [stepPrefix,fillRightOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨3,by decide⟩
  · change accessValid ((stepPrefix fillRightOps s 7).getReg .x23 + signExtend12 56) 8 = true
    have ptr : (stepPrefix fillRightOps s 7).getReg .x23 = s.getReg .x23 := by
      simp [stepPrefix,fillRightOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨3,by decide⟩

theorem safeFillleft (s : MachineState) (src : ∀ j : Fin 4, accessValid (s.getReg .x19+BitVec.ofNat 64 (8*j.val)) 8)
    (dst : ∀ j : Fin 4, accessValid (s.getReg .x23+BitVec.ofNat 64 (0+8*j.val)) 8) :
    safeSteps fillLeftOps s := by
  intro ⟨k,h⟩
  change k < 8 at h
  interval_cases k
  · change accessValid ((stepPrefix fillLeftOps s 0).getReg .x19 + signExtend12 0) 8 = true
    have ptr : (stepPrefix fillLeftOps s 0).getReg .x19 = s.getReg .x19 := by
      simp [stepPrefix,fillLeftOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨0,by decide⟩
  · change accessValid ((stepPrefix fillLeftOps s 1).getReg .x23 + signExtend12 0) 8 = true
    have ptr : (stepPrefix fillLeftOps s 1).getReg .x23 = s.getReg .x23 := by
      simp [stepPrefix,fillLeftOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨0,by decide⟩
  · change accessValid ((stepPrefix fillLeftOps s 2).getReg .x19 + signExtend12 8) 8 = true
    have ptr : (stepPrefix fillLeftOps s 2).getReg .x19 = s.getReg .x19 := by
      simp [stepPrefix,fillLeftOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨1,by decide⟩
  · change accessValid ((stepPrefix fillLeftOps s 3).getReg .x23 + signExtend12 8) 8 = true
    have ptr : (stepPrefix fillLeftOps s 3).getReg .x23 = s.getReg .x23 := by
      simp [stepPrefix,fillLeftOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨1,by decide⟩
  · change accessValid ((stepPrefix fillLeftOps s 4).getReg .x19 + signExtend12 16) 8 = true
    have ptr : (stepPrefix fillLeftOps s 4).getReg .x19 = s.getReg .x19 := by
      simp [stepPrefix,fillLeftOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨2,by decide⟩
  · change accessValid ((stepPrefix fillLeftOps s 5).getReg .x23 + signExtend12 16) 8 = true
    have ptr : (stepPrefix fillLeftOps s 5).getReg .x23 = s.getReg .x23 := by
      simp [stepPrefix,fillLeftOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨2,by decide⟩
  · change accessValid ((stepPrefix fillLeftOps s 6).getReg .x19 + signExtend12 24) 8 = true
    have ptr : (stepPrefix fillLeftOps s 6).getReg .x19 = s.getReg .x19 := by
      simp [stepPrefix,fillLeftOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨3,by decide⟩
  · change accessValid ((stepPrefix fillLeftOps s 7).getReg .x23 + signExtend12 24) 8 = true
    have ptr : (stepPrefix fillLeftOps s 7).getReg .x23 = s.getReg .x23 := by
      simp [stepPrefix,fillLeftOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨3,by decide⟩

theorem safeUseparent (s : MachineState) (src : ∀ j : Fin 4, accessValid (s.getReg .x19+BitVec.ofNat 64 (8*j.val)) 8)
    (dst : ∀ j : Fin 4, accessValid (s.getReg .x24+BitVec.ofNat 64 (0+8*j.val)) 8) :
    safeSteps useParentOps s := by
  intro ⟨k,h⟩
  change k < 8 at h
  interval_cases k
  · change accessValid ((stepPrefix useParentOps s 0).getReg .x19 + signExtend12 0) 8 = true
    have ptr : (stepPrefix useParentOps s 0).getReg .x19 = s.getReg .x19 := by
      simp [stepPrefix,useParentOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨0,by decide⟩
  · change accessValid ((stepPrefix useParentOps s 1).getReg .x24 + signExtend12 0) 8 = true
    have ptr : (stepPrefix useParentOps s 1).getReg .x24 = s.getReg .x24 := by
      simp [stepPrefix,useParentOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨0,by decide⟩
  · change accessValid ((stepPrefix useParentOps s 2).getReg .x19 + signExtend12 8) 8 = true
    have ptr : (stepPrefix useParentOps s 2).getReg .x19 = s.getReg .x19 := by
      simp [stepPrefix,useParentOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨1,by decide⟩
  · change accessValid ((stepPrefix useParentOps s 3).getReg .x24 + signExtend12 8) 8 = true
    have ptr : (stepPrefix useParentOps s 3).getReg .x24 = s.getReg .x24 := by
      simp [stepPrefix,useParentOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨1,by decide⟩
  · change accessValid ((stepPrefix useParentOps s 4).getReg .x19 + signExtend12 16) 8 = true
    have ptr : (stepPrefix useParentOps s 4).getReg .x19 = s.getReg .x19 := by
      simp [stepPrefix,useParentOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨2,by decide⟩
  · change accessValid ((stepPrefix useParentOps s 5).getReg .x24 + signExtend12 16) 8 = true
    have ptr : (stepPrefix useParentOps s 5).getReg .x24 = s.getReg .x24 := by
      simp [stepPrefix,useParentOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨2,by decide⟩
  · change accessValid ((stepPrefix useParentOps s 6).getReg .x19 + signExtend12 24) 8 = true
    have ptr : (stepPrefix useParentOps s 6).getReg .x19 = s.getReg .x19 := by
      simp [stepPrefix,useParentOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact src ⟨3,by decide⟩
  · change accessValid ((stepPrefix useParentOps s 7).getReg .x24 + signExtend12 24) 8 = true
    have ptr : (stepPrefix useParentOps s 7).getReg .x24 = s.getReg .x24 := by
      simp [stepPrefix,useParentOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.setByte,signExtend12]
    rw [ptr];exact dst ⟨3,by decide⟩

end CommitGolfCandidate.PairCap.Batch
