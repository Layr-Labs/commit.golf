import CommitGolfCandidate.RungAProgram
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 6000
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open R4b (NRegs Agree number)
open S4.Machine (W indexBase proofBase valueBase)
open Late (levelCount nodeAddress rowAddress)
def original (k : Nat) : NRegs:=fun reg=>if reg=.x6 then some 128 else abi k reg
theorem setupOK (k : Nat) : okList (abi k) initOps := by
  simp [okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH,initOps]
theorem constantsOK (k : Nat) :
    let a:=finalRegs (abi k) initOps
    okList a constantsOps ∧ Includes (baseRegs k 0) (finalRegs a constantsOps) := by
  constructor
  · simp [okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH,constantsOps,initOps] <;> decide
  · intro reg n e;cases reg <;> simp_all [okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH,constantsOps,initOps]
theorem emptyOK : Includes (finishRegs 0) (finalRegs (abi 0) initOps) := by
  intro reg n e;cases reg <;> simp_all [okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH,initOps]
theorem testInit (k : Nat) : finalRegs (abi k) initOps .x18=some k := rfl
theorem nextOK (k r g : Nat) (br:r<k) :
    let v:=stageRegs k r g 3
    okList v updateOps ∧ Includes (baseRegs k (r+1)) (finalRegs v updateOps) := by
  constructor
  · simp [okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH,updateOps];omega
  · intro reg n e;cases reg <;> simp_all [okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH,updateOps] <;> omega
theorem lastOK (k : Nat) : Includes (finishRegs k) (baseRegs k k) := by
  intro reg n e;cases reg <;> simp_all [okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH]
theorem restoreOK (k : Nat) (bound:k≤16777216) :
    okList (finishRegs k) restoreOps ∧ Includes (original k) (finalRegs (finishRegs k) restoreOps) := by
  constructor
  · simp [okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH,restoreOps] <;> omega
  · intro reg n e;cases reg <;> simp_all [original,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH,restoreOps] <;> omega
end CommitGolfCandidate.RungA
