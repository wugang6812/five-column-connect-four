import C4W5.CompactZone.Z8_side25.Check0

namespace C4W5.Z8_side25
open Connect4 (Player opponent)
open Connect4.NarrowBoards C4W5.PackedBank
open C4W5.CompactZone.Z8_side25
open C4W5.CompactZone.ClaimBank
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem ok : all fmt.radix (zcheckRowL 8 fmt t) t = true :=
  bank0_ok

theorem safe (H : Nat) (hH : H % 2 = 0) (hKH : 8 + 2 ≤ H) : Safe H (playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 4, 3]) :=
  zone_safe_of_claim_bank (by decide) hH hKH fmt t [2, 2, 2, 1, 1, 1, 1, 4, 3] ⟨0,10,5,1,0,0,4,3,1,1⟩
    (by decide +kernel) ok (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C4W5.Z8_side25.safe

end C4W5.Z8_side25
