import LongThreatStretch

/-!
Source-only cap-transfer arithmetic pilot.

This file has not been elaborated or kernel-checked. It is isolated from the
accepted build graph and contains no admitted declarations. It reuses the
existing `C4W5.Claimed` and `C4W5.LongThreat.liftTarget` definitions unchanged.
Rows are zero based. No strategy or LeafSound result is asserted here.
-/

namespace C4W5.CapTransfer
open C4W5.LongThreat (liftTarget)

/-- The cap reply adds one stone to an even-height s column. A higher
    old-even-parity target becomes an odd-offset cover target. -/
theorem transfer_target_arithmetic {H h n a b : Nat}
    (hH : H % 2 = 0) (hh : h % 2 = 0)
    (hge : h ≤ n) (hpar : n % 2 = h % 2)
    (hna : n < a) (hab : a < b) (hbH : b < H)
    (hbpar : (b - h) % 2 = 0) :
    n + 1 ≤ a ∧ n + 1 < b ∧ n + 1 < H ∧
      (b - (n + 1)) % 2 = 1 ∧ (H - (n + 1)) % 2 = 1 := by
  omega

/-- The advertised post-switch band is an ordinary cover stripe from the
    actual new top k. This is the key phase-II-to-LongThreat inclusion. -/
theorem phase2_band_claimed {s : Fin 5} {h k a : Nat} {x y : Int}
    (hka : k ≤ a)
    (hkpar : ((k : Int) - (h : Int)) % 2 = 1)
    (hx : x = (s.val : Int))
    (hya : (a : Int) ≤ y)
    (hypar : (y - (h : Int)) % 2 = 0) :
    Claimed s k x y := by
  refine ⟨hx, ?_, ?_⟩ <;> omega

/-- When rebasing a protected even column, an old claimed square is either
    strictly below the new top (handled by alt) or still claimed at that top.
    Equality with the new top is ruled out, not silently discarded. -/
theorem claimed_rebase_split {q : Fin 5} {h n : Nat} {x y : Int}
    (_hge : h ≤ n) (hpar : n % 2 = h % 2)
    (hc : Claimed q h x y) :
    y < (n : Int) ∨ Claimed q n x y := by
  obtain ⟨hx, hy, hp⟩ := hc
  by_cases hlt : y < (n : Int)
  · exact Or.inl hlt
  · right
    refine ⟨hx, ?_, ?_⟩ <;> omega

/-- On an even-height board, the odd carrier's final White cap cannot be
    one of its original cover-Black stripe cells. -/
theorem capped_stripe_below_cap {H h : Nat} {t : Fin 5} {x y : Int}
    (hH : H % 2 = 0) (hh : h % 2 = 1)
    (hyH : y < (H : Int)) (hc : Claimed t h x y) :
    y < (H : Int) - 1 := by
  obtain ⟨hx, hy, hp⟩ := hc
  omega

/-- Targets must be transported independently; they need not lie on the
    same side of a clean cut. -/
theorem liftTarget_strictMono {u a b : Nat} (hab : a < b) :
    liftTarget u a < liftTarget u b := by
  unfold liftTarget
  split_ifs <;> omega

/-- Pure target-height arithmetic. The caller obtains the new column-height
    formula from stretch_length; clean-cut geometry is not smuggled in here. -/
theorem two_target_height_transport {H u h a b : Nat}
    (hha : h < a) (hab : a < b) (hbH : b < H)
    (haodd : (a - h) % 2 = 1) (hbeven : (b - h) % 2 = 0) :
    let h' := if u < h then h + 2 else h
    h' < liftTarget u a ∧ liftTarget u a < liftTarget u b ∧
      liftTarget u b < H + 2 ∧
      (liftTarget u a - h') % 2 = 1 ∧
      (liftTarget u b - h') % 2 = 0 := by
  dsimp only
  unfold liftTarget
  split_ifs <;> omega

/-- Low side phase-II guard transport, including b=y=u where the threshold
    changes into the post-switch stripe. The contradictory a=y=u parity
    case is handled by the same arithmetic. -/
theorem phase2_guard_stretch_low {u h a b : Nat} {y : Int}
    (hha : h < a) (hab : a < b)
    (haodd : (a - h) % 2 = 1) (hbeven : (b - h) % 2 = 0)
    (hy : y ≤ (u : Int))
    (hg : (b : Int) ≤ y ∨ ((a : Int) ≤ y ∧ (y - (h : Int)) % 2 = 0)) :
    let h' := if u < h then h + 2 else h
    (liftTarget u b : Int) ≤ y ∨
      ((liftTarget u a : Int) ≤ y ∧ (y - (h' : Int)) % 2 = 0) := by
  dsimp only
  rcases hg with hb | ⟨ha, hp⟩
  · unfold liftTarget
    split_ifs <;> omega
  · unfold liftTarget
    split_ifs <;> omega

/-- The high side shifts the member row by two. This arithmetic implication
    itself needs no clearance hypothesis; the geometric caller supplies it. -/
theorem phase2_guard_stretch_high {u h a b : Nat} {y : Int}
    (hg : (b : Int) ≤ y ∨ ((a : Int) ≤ y ∧ (y - (h : Int)) % 2 = 0)) :
    let h' := if u < h then h + 2 else h
    (liftTarget u b : Int) ≤ y + 2 ∨
      ((liftTarget u a : Int) ≤ y + 2 ∧ (y + 2 - (h' : Int)) % 2 = 0) := by
  dsimp only
  rcases hg with hb | ⟨ha, hp⟩
  · left
    unfold liftTarget
    split_ifs <;> omega
  · right
    constructor
    · unfold liftTarget
      split_ifs <;> omega
    · split_ifs <;> omega

end C4W5.CapTransfer
