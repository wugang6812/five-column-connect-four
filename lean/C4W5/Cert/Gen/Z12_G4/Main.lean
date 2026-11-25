import C4W5.CompactZone.Z12_G4.Check0
import C4W5.CompactZone.Z12_G4.Check1
import C4W5.CompactZone.Z12_G4.Check2
import C4W5.CompactZone.Z12_G4.Check3
import C4W5.CompactZone.Z12_G4.Check4
import C4W5.CompactZone.Z12_G4.Check5
import C4W5.CompactZone.Z12_G4.Check6

namespace C4W5.Z12_G4
open Connect4 (Player opponent)
open Connect4.NarrowBoards C4W5.PackedBank
open C4W5.CompactZone.Z12_G4
open C4W5.CompactZone.ClaimBank
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem ok : all fmt.radix (zcheckRowL 12 fmt t) t = true :=
  (all_branch (all_branch bank0_ok (all_branch bank1_ok bank2_ok)) (all_branch (all_branch bank3_ok bank4_ok) (all_branch bank5_ok bank6_ok)))

theorem safe (H : Nat) (hH : H % 2 = 0) (hKH : 12 + 2 ≤ H) : Safe H (playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1]) :=
  zone_safe_of_claim_bank (by decide) hH hKH fmt t [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1] ⟨0,426,5,0,0,0,9,3,1,0⟩
    (by decide +kernel) ok (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C4W5.Z12_G4.safe

end C4W5.Z12_G4
