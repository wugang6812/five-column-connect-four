import C4W5.Theory.StretchB
import C4W5.Cert.Real

/-!
# The stretch theorem (STRETCH_THEOREM.md §4), board level

`StretchCert D I`: `I` is a set of abstract positions (height, board), White to move, closed under
"any White move in any variant, then some Black move in every variant", up to stretch-equivalence.
Then Black does not lose from any real board that is a stretch of a member of `I`.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

/-- The positions that may arise from `A` by a move of colour `p` in column `c`, as base boards for
the real position (Lemma B): `A` moved, and — if the gap above the column is exactly `2D+2` —
`A` stretched once in that gap and then moved. -/
def Variant (D h : Nat) (A : Board 5) (c : Fin 5) (p : Player) (h₁ : Nat) (A₁ : Board 5) : Prop :=
  (h₁ = h ∧ A₁ = play A c p) ∨
  (ClearCut D h A ((A c).length + D + 1) ∧ ¬ ClearCut D h A ((A c).length + D + 2) ∧
    h₁ = h + 2 ∧ A₁ = play (stretch A ((A c).length + D + 1)) c p)

theorem exists_variant {D h h' : Nat} {A R : Board 5} (hs : SEq D h A h' R) (c : Fin 5) (p : Player) :
    ∃ h₁ A₁, Variant D h A c p h₁ A₁ ∧ SEq D h₁ A₁ h' (play R c p) := by
  rcases hs.play c p with h1 | ⟨c1, c2, h1⟩
  · exact ⟨h, _, Or.inl ⟨rfl, rfl⟩, h1⟩
  · exact ⟨h + 2, _, Or.inr ⟨c1, c2, rfl, rfl⟩, h1⟩

/-- Closure condition for a set of abstract positions. -/
def StretchCert (D : Nat) (I : Nat → Board 5 → Prop) : Prop :=
  ∀ h A, I h A → ∀ c, Legal h A c → ∀ h₁ A₁, Variant D h A c .white h₁ A₁ →
    ¬ HasFour h₁ A₁ .white ∧
    (BoardFull h₁ A₁ ∨ ∃ e, Legal h₁ A₁ e ∧ ∀ h₂ A₂, Variant D h₁ A₁ e .black h₂ A₂ →
      HasFour h₂ A₂ .black ∨ ∃ h₃ A₃, I h₃ A₃ ∧ SEq D h₃ A₃ h₂ A₂)

theorem stretch_safeFor {D : Nat} (hD : 2 ≤ D) {I : Nat → Board 5 → Prop} (hI : StretchCert D I) :
    ∀ k (H : Nat) (R : Board 5), toMove R = .white → ¬ HasFour H R .white →
      (∃ h A, I h A ∧ SEq D h A H R) → SafeFor H .black k R := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro H R htm hnw ⟨h, A, hA, hs⟩
    cases k with
    | zero => exact hnw
    | succ k =>
      refine ⟨hnw, Or.inr (Or.inr ?_)⟩
      have hne : ¬ toMove R = .black := by rw [htm]; decide
      rw [if_neg hne, htm]
      intro c hc
      obtain ⟨h₁, A₁, hv, hs1⟩ := exists_variant hs c .white
      obtain ⟨hnw1A, hrest⟩ := hI h A hA c ((hs.legal_iff c).mpr hc) h₁ A₁ hv
      have hnw1 : ¬ HasFour H (play R c .white) .white := fun hf => hnw1A ((hs1.hasFour_iff hD _).mpr hf)
      cases k with
      | zero => exact hnw1
      | succ k =>
        refine ⟨hnw1, ?_⟩
        rcases hrest with hfull | ⟨e, he, hrep⟩
        · exact Or.inr (Or.inl (hs1.full_iff.mp hfull))
        · refine Or.inr (Or.inr ?_)
          have htb : toMove (play R c .white) = .black := toMove_play_white htm c
          rw [if_pos htb, htb]
          refine ⟨e, (hs1.legal_iff e).mp he, ?_⟩
          obtain ⟨h₂, A₂, hv2, hs2⟩ := exists_variant hs1 e .black
          have hnw2 : ¬ HasFour H (play (play R c .white) e .black) .white :=
            fun hf => hnw1 (hasFour_play_other (by decide) hf)
          rcases hrep h₂ A₂ hv2 with hwin | ⟨h₃, A₃, hA3, hs3⟩
          · exact safeFor_of_blackFour hnw2 ((hs2.hasFour_iff hD _).mp hwin) k
          · exact ih k (by omega) H _ (toMove_play_black htb e) hnw2 ⟨h₃, A₃, hA3, hs3.trans hs2⟩

/-- **The stretch theorem.** -/
theorem stretch_safe {D : Nat} (hD : 2 ≤ D) {I : Nat → Board 5 → Prop} (hI : StretchCert D I)
    {H : Nat} {R : Board 5} (htm : toMove R = .white) (hnw : ¬ HasFour H R .white)
    {h : Nat} {A : Board 5} (hA : I h A) (hs : SEq D h A H R) : Safe H R :=
  fun k => stretch_safeFor hD hI k H R htm hnw ⟨h, A, hA, hs⟩

#print axioms stretch_safe

/-! ## With leaves

`L` is a set of abstract positions that are known to be safe in every stretch by another argument
(the endgame criteria).  Black's reply may lead into `I` or into `L`. -/

def StretchCertL (D : Nat) (L I : Nat → Board 5 → Prop) : Prop :=
  ∀ h A, I h A → ∀ c, Legal h A c → ∀ h₁ A₁, Variant D h A c .white h₁ A₁ →
    ¬ HasFour h₁ A₁ .white ∧
    (BoardFull h₁ A₁ ∨ ∃ e, Legal h₁ A₁ e ∧ ∀ h₂ A₂, Variant D h₁ A₁ e .black h₂ A₂ →
      HasFour h₂ A₂ .black ∨ ∃ h₃ A₃, (I h₃ A₃ ∨ L h₃ A₃) ∧ SEq D h₃ A₃ h₂ A₂)

/-- What a leaf set must provide. -/
def LeafSound (D : Nat) (L : Nat → Board 5 → Prop) : Prop :=
  ∀ h A H R, L h A → SEq D h A H R → toMove R = .white → ¬ HasFour H R .white →
    ¬ HasFour H R .black → Safe H R

theorem stretch_safeForL {D : Nat} (hD : 2 ≤ D) {L I : Nat → Board 5 → Prop}
    (hL : LeafSound D L) (hI : StretchCertL D L I) :
    ∀ k (H : Nat) (R : Board 5), toMove R = .white → ¬ HasFour H R .white →
      (∃ h A, I h A ∧ SEq D h A H R) → SafeFor H .black k R := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro H R htm hnw ⟨h, A, hA, hs⟩
    cases k with
    | zero => exact hnw
    | succ k =>
      refine ⟨hnw, Or.inr (Or.inr ?_)⟩
      have hne : ¬ toMove R = .black := by rw [htm]; decide
      rw [if_neg hne, htm]
      intro c hc
      obtain ⟨h₁, A₁, hv, hs1⟩ := exists_variant hs c .white
      obtain ⟨hnw1A, hrest⟩ := hI h A hA c ((hs.legal_iff c).mpr hc) h₁ A₁ hv
      have hnw1 : ¬ HasFour H (play R c .white) .white := fun hf => hnw1A ((hs1.hasFour_iff hD _).mpr hf)
      cases k with
      | zero => exact hnw1
      | succ k =>
        refine ⟨hnw1, ?_⟩
        rcases hrest with hfull | ⟨e, he, hrep⟩
        · exact Or.inr (Or.inl (hs1.full_iff.mp hfull))
        · refine Or.inr (Or.inr ?_)
          have htb : toMove (play R c .white) = .black := toMove_play_white htm c
          rw [if_pos htb, htb]
          refine ⟨e, (hs1.legal_iff e).mp he, ?_⟩
          obtain ⟨h₂, A₂, hv2, hs2⟩ := exists_variant hs1 e .black
          have hnw2 : ¬ HasFour H (play (play R c .white) e .black) .white :=
            fun hf => hnw1 (hasFour_play_other (by decide) hf)
          rcases hrep h₂ A₂ hv2 with hwin | ⟨h₃, A₃, hA3 | hA3, hs3⟩
          · exact safeFor_of_blackFour hnw2 ((hs2.hasFour_iff hD _).mp hwin) k
          · exact ih k (by omega) H _ (toMove_play_black htb e) hnw2 ⟨h₃, A₃, hA3, hs3.trans hs2⟩
          · by_cases hb : HasFour H (play (play R c .white) e .black) .black
            · exact safeFor_of_blackFour hnw2 hb k
            · exact hL h₃ A₃ H _ hA3 (hs3.trans hs2) (toMove_play_black htb e) hnw2 hb k

/-- **The stretch theorem with leaves.** -/
theorem stretch_safeL {D : Nat} (hD : 2 ≤ D) {L I : Nat → Board 5 → Prop} (hL : LeafSound D L)
    (hI : StretchCertL D L I) {H : Nat} {R : Board 5} (htm : toMove R = .white)
    (hnw : ¬ HasFour H R .white) {h : Nat} {A : Board 5} (hA : I h A) (hs : SEq D h A H R) :
    Safe H R :=
  fun k => stretch_safeForL hD hL hI k H R htm hnw ⟨h, A, hA, hs⟩

#print axioms stretch_safeL

end C4W5
