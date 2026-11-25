import C4W5.Cert.StretchZoneC

namespace C4W5.QuickNorm
open C4W5

/-- A successful contraction stretches back across a clear cut. The cut is also clear
in the input, providing a cheap necessary condition before constructing the contracted board. -/
private theorem necessary {D H : Nat} {p q : Pos} {r : Nat} (hH : 2 ≤ H)
    (hc : clearM D (H-2) (q.LM (H-2)) r = true) (he : (stretchPos q r).beq p = true) :
    clearM D H (p.LM H) r = true := by
  have hcut := (clearM_iff D _ _ _).mp hc
  have old := (clear_stretch_low hcut (show r ≤ r by omega)).mpr hcut
  have hr := clearCut_bounds hcut
  have ep := Pos.eq_of_beq he
  rw [← (stretchPos_toBoard q r (by omega)), ep, show H-2+2=H by omega] at old
  exact (clearM_iff D _ _ _).mpr old

def checked {α : Sort _} (D H : Nat) (p : Pos) (x : Nat) (f : Nat → Pos → α) : α :=
  let r := p.ht x - D - 3
  if D < r && clearM D H (p.LM H) r then withNorm D H p x f else f H p

theorem checked_eq {α : Sort _} (D H : Nat) (p : Pos) (x : Nat) (f : Nat → Pos → α) :
    checked D H p x f = withNorm D H p x f := by
  simp only [checked]
  split
  · rfl
  · rename_i hn
    unfold withNorm; split
    · rename_i h; rw [forceP_eq]
      split
      · rename_i yes
        simp only [Bool.and_eq_true] at yes
        have hc := necessary h.2 yes.1.2 yes.2
        have hr := clearCut_bounds ((clearM_iff _ _ _ _).mp yes.1.2)
        simp [hc,show D < p.ht x-D-3 by omega] at hn
      · rfl
    · rfl

end C4W5.QuickNorm
