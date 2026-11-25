import LongThreatStretch
import C4W5.Cert.ClaimC

/-! Reference witness-driven gate. Bounded finite reflection only; no optimized
    giant-bank integration or performance claim is made by this module. -/
namespace C4W5.LongThreat
open Connect4 (Player opponent)
open Connect4.NarrowBoards
set_option linter.deprecated false

def selected (mask : Nat) (q : Fin 5) : Prop := mask.testBit q.val = true
instance (mask : Nat) : DecidablePred (selected mask) := fun q => inferInstanceAs (Decidable (_ = _))

instance (t : Fin 5) (rho mask : Nat) (h0 : Fin 5 → Nat) (x y : Int) :
    Decidable (Guard t rho (selected mask) h0 x y) := by
  unfold Guard; infer_instance

instance (R : Board 5) (c : Fin 5) : Decidable (TopThree R c) := by
  unfold TopThree; infer_instance

def tripleCheck (H : Nat) (p : Pos) (t : Fin 5) (rho : Nat) (d : Fin 3) (i : Fin 4) : Prop :=
  ∀ j : Fin 4, j ≠ i →
    cellAtInt H p.toBoard ((t.val : Int) - (i : Int) * 1 + (j : Int) * 1)
      ((rho : Int) - (i : Int) * dyOf d.val + (j : Int) * dyOf d.val) = some .black
instance (H : Nat) (p : Pos) (t : Fin 5) (rho : Nat) (d : Fin 3) (i : Fin 4) :
    Decidable (tripleCheck H p t rho d i) := by unfold tripleCheck; infer_instance

def deadCheck (H : Nat) (p : Pos) (t : Fin 5) (rho mask : Nat) (c : Fin 5) (r : Nat) : Prop :=
  ∀ d : Fin 3, ∀ i : Fin 4, ∃ j : Fin 4,
    let x := (c.val : Int) - (i : Int) * 1 + (j : Int) * 1
    let y := (r : Int) - (i : Int) * dyOf d.val + (j : Int) * dyOf d.val
    cellAtInt H p.toBoard x y = some .black ∨
    Guard t rho (selected mask) (fun q => p.ht q.val) x y ∨
    ¬ (0 ≤ x ∧ x < 5 ∧ 0 ≤ y ∧ y < (H : Int))
instance (H : Nat) (p : Pos) (t : Fin 5) (rho mask : Nat) (c : Fin 5) (r : Nat) :
    Decidable (deadCheck H p t rho mask c r) := by unfold deadCheck; infer_instance

/-- All unbounded-looking row checks are restricted to the legal board height. -/
def CheckProp (H : Nat) (p : Pos) (t : Fin 5) (rho mask : Nat) (d : Fin 3) (i : Fin 4) : Prop :=
  H % 2 = 0 ∧ p.wfB H = true ∧ ¬ selected mask t ∧
  (H - p.ht t.val) % 2 = 1 ∧
  (∀ q : Fin 5, selected mask q → (H - p.ht q.val) % 2 = 0) ∧
  p.ht t.val < rho ∧ rho < H ∧ (rho - p.ht t.val) % 2 = 1 ∧
  (∀ c : Fin 5, p.ht c.val < H → ¬ TopThree p.toBoard c) ∧
  tripleCheck H p t rho d i ∧
  (∀ c : Fin 5, ∀ r : Fin (H + 1),
    excB p c.val r.val = true ∨ potB H p c.val r.val = true → deadCheck H p t rho mask c r.val)
instance (H : Nat) (p : Pos) (t : Fin 5) (rho mask : Nat) (d : Fin 3) (i : Fin 4) :
    Decidable (CheckProp H p t rho mask d i) := by unfold CheckProp; infer_instance

def check (H : Nat) (p : Pos) (t : Fin 5) (rho mask : Nat) (d : Fin 3) (i : Fin 4) : Bool :=
  decide (CheckProp H p t rho mask d i)

theorem tripleCheck_sound {H : Nat} {p : Pos} {t : Fin 5} {rho : Nat} {d : Fin 3} {i : Fin 4}
    (h : tripleCheck H p t rho d i) : Threat H p.toBoard t rho := by
  refine ⟨(t.val : Int) - (i : Int) * 1, (rho : Int) - (i : Int) * dyOf d.val,
    dyOf d.val, i, ?_, by omega, by omega, h⟩
  have hd := d.isLt
  have hc : d.val = 0 ∨ d.val = 1 ∨ d.val = 2 := by omega
  rcases hc with hc | hc | hc <;> simp [dyOf, hc]

theorem deadCheck_sound {H : Nat} {p : Pos} {t : Fin 5} {rho mask : Nat} {c : Fin 5} {r : Nat}
    (h : deadCheck H p t rho mask c r) :
    Dead H p.toBoard t rho (selected mask) (fun q => (p.toBoard q).length) c r := by
  intro dy hdy i
  obtain ⟨d, hd⟩ : ∃ d : Fin 3, dyOf d.val = dy := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hdy
    rcases hdy with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hp : (fun q => (p.toBoard q).length) = (fun q : Fin 5 => p.ht q.val) := by
    funext q; exact Pos.height p q
  rw [hp, ← hd]
  exact h d i

theorem check_sound {H : Nat} {p : Pos} {t : Fin 5} {rho mask : Nat} {d : Fin 3} {i : Fin 4}
    (h : check H p t rho mask d i = true) : Hyp H p.toBoard t rho (selected mask) := by
  have hh : CheckProp H p t rho mask d i := of_decide_eq_true h
  obtain ⟨he, hwf, hn, ho, hq, hgt, hlt, hp, hntr, htr, hd⟩ := hh
  have hw := Pos.wfB_sound hwf
  refine ⟨he, ?_, hn, ?_, ?_, ?_, hlt, ?_, ?_, tripleCheck_sound htr, ?_⟩
  · intro c; rw [Pos.height]; exact (hw c.val).2
  · simpa only [Pos.height] using ho
  · intro q hq'; simpa only [Pos.height] using hq q hq'
  · simpa only [Pos.height] using hgt
  · simpa only [Pos.height] using hp
  · intro c hc; apply hntr c; simpa only [Legal, Pos.height] using hc
  · intro c r hx
    have hr : r < H + 1 := by
      rcases hx with hx | hx
      · have hb := stone_bound _ _ _ hx.1
        rw [Pos.height] at hb
        have := (hw c.val).2; omega
      · obtain ⟨rfl, hh, _⟩ := hx; omega
    apply deadCheck_sound
    apply hd c ⟨r, hr⟩
    rcases hx with hx | hx
    · exact Or.inl (excB_complete hx)
    · exact Or.inr (potB_complete hx)

/-- Real SG5 row with a target three cover pairs away, at one-based row 9.
    This is D0.lean extraction index 238 in the deterministic source scan. -/
def examplePos : Pos := ⟨0, 426, 341, 342, 6, 0, 10, 10, 10, 3⟩
theorem exampleChecked : check 10 examplePos 4 8 1 0 3 = true := by decide +kernel

theorem exampleHyp : Hyp 10 examplePos.toBoard 4 8 (selected 1) := check_sound exampleChecked

#print axioms check_sound
#print axioms exampleHyp
end C4W5.LongThreat
