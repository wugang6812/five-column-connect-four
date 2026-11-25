import WindowFast
import ZoneEndChecked

namespace C4W5.WindowBank
open Connect4 (Player opponent)
open Connect4.NarrowBoards
set_option linter.deprecated false

abbrev ZEndGate := Nat → Pos → Lab5 → Bool

def memZoneEnds (F : SZFormat) (t : Bank) (leaf : ZEndGate) (k : Nat) (p : Pos) (l : Lab5) : Bool :=
  leaf k p l || szmem F t k p l

theorem memZoneEnds_sound {F : SZFormat} {t : Bank} {leaf : ZEndGate}
    (hl : ∀ k p l, leaf k p l = true → ZoneEnds.SZ.Extra k p.toBoard) :
    ∀ k p l, memZoneEnds F t leaf k p l = true →
        ZoneEnds.SZ.Join (szrel F t) k p.toBoard l.fn := by
  intro k p l h
  simp only [memZoneEnds, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inr (hl k p l h)
  · exact Or.inl (szmem_sound h)

def zoneEndsRow (D : Nat) (F : SZFormat) (t : Bank) (leaf : ZEndGate) (w : Nat) : Bool :=
  force w fun w => forceP (F.pos w) fun p =>
    ZoneFast.step D (memZoneEnds F t leaf) (F.height w) p (F.labels w) (w % F.repBase)

theorem zoneEndsCert {D : Nat} (hD : 2 ≤ D) (F : SZFormat) (t : Bank) (leaf : ZEndGate)
    (hl : ∀ k p l, leaf k p l = true → ZoneEnds.SZ.Extra k p.toBoard)
    (hall : all F.radix (zoneEndsRow D F t leaf) t = true) :
    ZoneEnds.SZ.SZCert D (szrel F t) := by
  rintro h A ls ⟨w, hw, rfl, rfl, rfl⟩
  have hc := all_sound hall hw
  simp only [zoneEndsRow, force_eq, forceP_eq] at hc
  exact ZoneEnds.SZ.fast_sound_extra hD (memZoneEnds_sound hl) hc

theorem g5_zone_ends (F : SZFormat) (t : Bank) (leaf : ZEndGate)
    (hl : ∀ k p l, leaf k p l = true → ZoneEnds.SZ.Extra k p.toBoard)
    (ok : all F.radix (zoneEndsRow 2 F t leaf) t = true)
    (root : szmem F t 14 g5p ⟨0, 0, 0, 0, 0⟩ = true) (m b : Nat) (hb : 5 ≤ b) (hbm : b + 3 ≤ m) :
    Safe (2 * m) (G b) := by
  have hlen : ∀ c, (G b c).length ≤ 2 * b + 4 := fun c => by
    have := G_len b (by omega) c; omega
  have hq : g5p.toBoard = G 5 := by
    funext c; obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c <;> rfl
  have hs : SEq 2 14 g5p.toBoard (2 * b + 4) (trunc (2 * b + 4) (G b)) := by
    rw [trunc_short hlen, hq]; exact seq_G_wall 4 (by omega) b hb
  have hs' : SEq 2 14 (G 5) (2 * b + 4) (G b) := seq_G_wall 4 (by omega) b hb
  have nf : ∀ p, ¬ HasFour 14 (G 5) p := by
    intro p hf
    rw [← G5_play] at hf
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
      (show (Pos.run 14 Pos.empty .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1]).isSome = true by decide)
    obtain ⟨e, hw, hb', -⟩ := root_of_run' hq
    rw [← e] at hf
    cases p
    · exact hb' hf
    · exact hw hf
  have nfb : ∀ p, ¬ HasFour (2 * m) (G b) p := fun p hf =>
    nf p ((hs'.hasFour_iff (by omega) p).mpr (hasFour_lower hlen hf))
  have hlab : (⟨0, 0, 0, 0, 0⟩ : Lab5).fn = labs (2 * m) (2 * b + 4) (G b) := by
    funext c
    have := hlen c
    simp only [labs, labOf]
    rw [if_pos this]
    obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c <;> rfl
  have hr := szmem_sound root
  rw [hlab] at hr
  exact ZoneEnds.SZ.sz_safe (by omega) (zoneEndsCert (by omega) F t leaf hl ok)
    (by omega) (by omega) (by omega) (toMove_G b) (nfb .white) (nfb .black)
    (G_discE b _ (by omega)) (G_tcol b _ _ (by omega) (by omega)) (fun c => by have := hlen c; omega) hr hs

#print axioms C4W5.WindowBank.g5_zone_ends
end C4W5.WindowBank
