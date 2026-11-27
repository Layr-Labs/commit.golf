import CommitGolfCandidate.R1bOpenCount
namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitGolfCandidate R1b.Machine
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
private theorem countTile0 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*0+k.val))) := by decide +kernel
private theorem countTile1 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*1+k.val))) := by decide +kernel
private theorem countTile2 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*2+k.val))) := by decide +kernel
private theorem countTile3 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*3+k.val))) := by decide +kernel
private theorem countTile4 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*4+k.val))) := by decide +kernel
private theorem countTile5 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*5+k.val))) := by decide +kernel
private theorem countTile6 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*6+k.val))) := by decide +kernel
private theorem countTile7 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*7+k.val))) := by decide +kernel
private theorem countTile8 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*8+k.val))) := by decide +kernel
private theorem countTile9 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*9+k.val))) := by decide +kernel
private theorem countTile10 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*10+k.val))) := by decide +kernel
private theorem countTile11 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*11+k.val))) := by decide +kernel
private theorem countTile12 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*12+k.val))) := by decide +kernel
private theorem countTile13 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*13+k.val))) := by decide +kernel
private theorem countTile14 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*14+k.val))) := by decide +kernel
private theorem countTile15 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*15+k.val))) := by decide +kernel
private theorem countTile16 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*16+k.val))) := by decide +kernel
private theorem countTile17 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*17+k.val))) := by decide +kernel
private theorem countTile18 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*18+k.val))) := by decide +kernel
private theorem countTile19 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*19+k.val))) := by decide +kernel
private theorem countTile20 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*20+k.val))) := by decide +kernel
private theorem countTile21 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*21+k.val))) := by decide +kernel
private theorem countTile22 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*22+k.val))) := by decide +kernel
private theorem countTile23 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*23+k.val))) := by decide +kernel
private theorem countTile24 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*24+k.val))) := by decide +kernel
private theorem countTile25 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*25+k.val))) := by decide +kernel
private theorem countTile26 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*26+k.val))) := by decide +kernel
private theorem countTile27 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*27+k.val))) := by decide +kernel
private theorem countTile28 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*28+k.val))) := by decide +kernel
private theorem countTile29 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*29+k.val))) := by decide +kernel
private theorem countTile30 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*30+k.val))) := by decide +kernel
private theorem countTile31 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*31+k.val))) := by decide +kernel
private theorem countTile32 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*32+k.val))) := by decide +kernel
private theorem countTile33 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*33+k.val))) := by decide +kernel
private theorem countTile34 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*34+k.val))) := by decide +kernel
private theorem countTile35 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*35+k.val))) := by decide +kernel
private theorem countTile36 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*36+k.val))) := by decide +kernel
private theorem countTile37 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*37+k.val))) := by decide +kernel
private theorem countTile38 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*38+k.val))) := by decide +kernel
private theorem countTile39 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*39+k.val))) := by decide +kernel
private theorem countTile40 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*40+k.val))) := by decide +kernel
private theorem countTile41 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*41+k.val))) := by decide +kernel
private theorem countTile42 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*42+k.val))) := by decide +kernel
private theorem countTile43 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*43+k.val))) := by decide +kernel
private theorem countTile44 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*44+k.val))) := by decide +kernel
private theorem countTile45 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*45+k.val))) := by decide +kernel
private theorem countTile46 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*46+k.val))) := by decide +kernel
private theorem countTile47 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*47+k.val))) := by decide +kernel
private theorem countTile48 : ∀ k : Fin 256,keepsCount (decodeInstruction (Code.word .opening (256*48+k.val))) := by decide +kernel
private theorem countTile49 : ∀ k : Fin 153,keepsCount (decodeInstruction (Code.word .opening (256*49+k.val))) := by decide +kernel
theorem countAt (n : Nat) (hn : n<12697) : keepsCount (decodeInstruction (Code.word .opening n)) := by
  let j:=n/256
  have bound : j<50:=by dsimp [j];omega
  have split : n=256*j+n%256:=by dsimp [j];omega
  conv in Code.word .opening n => rw [split]
  interval_cases j
  · exact countTile0 ⟨n%256,by omega⟩
  · exact countTile1 ⟨n%256,by omega⟩
  · exact countTile2 ⟨n%256,by omega⟩
  · exact countTile3 ⟨n%256,by omega⟩
  · exact countTile4 ⟨n%256,by omega⟩
  · exact countTile5 ⟨n%256,by omega⟩
  · exact countTile6 ⟨n%256,by omega⟩
  · exact countTile7 ⟨n%256,by omega⟩
  · exact countTile8 ⟨n%256,by omega⟩
  · exact countTile9 ⟨n%256,by omega⟩
  · exact countTile10 ⟨n%256,by omega⟩
  · exact countTile11 ⟨n%256,by omega⟩
  · exact countTile12 ⟨n%256,by omega⟩
  · exact countTile13 ⟨n%256,by omega⟩
  · exact countTile14 ⟨n%256,by omega⟩
  · exact countTile15 ⟨n%256,by omega⟩
  · exact countTile16 ⟨n%256,by omega⟩
  · exact countTile17 ⟨n%256,by omega⟩
  · exact countTile18 ⟨n%256,by omega⟩
  · exact countTile19 ⟨n%256,by omega⟩
  · exact countTile20 ⟨n%256,by omega⟩
  · exact countTile21 ⟨n%256,by omega⟩
  · exact countTile22 ⟨n%256,by omega⟩
  · exact countTile23 ⟨n%256,by omega⟩
  · exact countTile24 ⟨n%256,by omega⟩
  · exact countTile25 ⟨n%256,by omega⟩
  · exact countTile26 ⟨n%256,by omega⟩
  · exact countTile27 ⟨n%256,by omega⟩
  · exact countTile28 ⟨n%256,by omega⟩
  · exact countTile29 ⟨n%256,by omega⟩
  · exact countTile30 ⟨n%256,by omega⟩
  · exact countTile31 ⟨n%256,by omega⟩
  · exact countTile32 ⟨n%256,by omega⟩
  · exact countTile33 ⟨n%256,by omega⟩
  · exact countTile34 ⟨n%256,by omega⟩
  · exact countTile35 ⟨n%256,by omega⟩
  · exact countTile36 ⟨n%256,by omega⟩
  · exact countTile37 ⟨n%256,by omega⟩
  · exact countTile38 ⟨n%256,by omega⟩
  · exact countTile39 ⟨n%256,by omega⟩
  · exact countTile40 ⟨n%256,by omega⟩
  · exact countTile41 ⟨n%256,by omega⟩
  · exact countTile42 ⟨n%256,by omega⟩
  · exact countTile43 ⟨n%256,by omega⟩
  · exact countTile44 ⟨n%256,by omega⟩
  · exact countTile45 ⟨n%256,by omega⟩
  · exact countTile46 ⟨n%256,by omega⟩
  · exact countTile47 ⟨n%256,by omega⟩
  · exact countTile48 ⟨n%256,by omega⟩
  · exact countTile49 ⟨n%256,by omega⟩
end TwoPermutationPrototype.PackedOpening
