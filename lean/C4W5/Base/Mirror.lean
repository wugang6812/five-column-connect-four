import C4W5.Base.Steps

/-!
# Left-right mirror symmetry

`mirror b` reverses the order of the columns.  Safety is invariant under mirroring; this is what lets
the proof tree treat White's moves in columns 4 and 5 as the mirror images of columns 2 and 1.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

variable {w h : Nat}

set_option linter.deprecated false

def mirror (b : Board w) : Board w := fun c => b c.rev

@[simp] theorem mirror_apply (b : Board w) (c : Fin w) : mirror b c = b c.rev := rfl

@[simp] theorem mirror_mirror (b : Board w) : mirror (mirror b) = b := by
  funext c; simp [mirror]

theorem cellAtInt_mirror (b : Board w) (x y : Int) :
    cellAtInt h (mirror b) x y = cellAtInt h b ((w : Int) - 1 - x) y := by
  unfold cellAtInt
  by_cases hx : 0 ≤ x ∧ x < (w : Int)
  · have hx' : 0 ≤ (w : Int) - 1 - x ∧ (w : Int) - 1 - x < (w : Int) := by omega
    rw [dif_pos hx, dif_pos hx']
    have e : ∀ (p1 : x.toNat < w) (p2 : ((w : Int) - 1 - x).toNat < w),
        (Fin.rev ⟨x.toNat, p1⟩ : Fin w) = ⟨((w : Int) - 1 - x).toNat, p2⟩ := by
      intro p1 p2; apply Fin.ext; simp only [Fin.val_rev]; omega
    simp only [mirror]
    rw [e]
  · have hx' : ¬ (0 ≤ (w : Int) - 1 - x ∧ (w : Int) - 1 - x < (w : Int)) := by omega
    rw [dif_neg hx, dif_neg hx']

theorem hasFour_of_mirror {b : Board w} {p : Player} (hf : HasFour h (mirror b) p) :
    HasFour h b p := by
  have hrev : ∀ i : Fin 4, ((Fin.rev i : Fin 4) : Nat) + (i : Nat) = 3 := by
    intro i; have := i.isLt; simp only [Fin.val_rev]; omega
  rcases hf with ⟨x, y, hf⟩ | ⟨x, y, hf⟩ | ⟨x, y, hf⟩ | ⟨x, y, hf⟩
  · refine Or.inl ⟨(w : Int) - 1 - x, y, fun i => ?_⟩
    have := hf i
    rw [cellAtInt_mirror] at this
    have e : (w : Int) - 1 - (x + (i : Int) * 0) = (w : Int) - 1 - x + (i : Int) * 0 := by omega
    rw [e] at this; exact this
  · refine Or.inr (Or.inl ⟨(w : Int) - 4 - x, y, fun i => ?_⟩)
    have := hf i.rev
    have hr := hrev i
    rw [cellAtInt_mirror] at this
    have e1 : (w : Int) - 1 - (x + ((i.rev : Fin 4) : Int) * 1) = (w : Int) - 4 - x + (i : Int) * 1 := by omega
    have e2 : y + ((i.rev : Fin 4) : Int) * 0 = y + (i : Int) * 0 := by omega
    rw [e1, e2] at this; exact this
  · refine Or.inr (Or.inr (Or.inr ⟨(w : Int) - 4 - x, y + 3, fun i => ?_⟩))
    have := hf i.rev
    have hr := hrev i
    rw [cellAtInt_mirror] at this
    have e1 : (w : Int) - 1 - (x + ((i.rev : Fin 4) : Int) * 1) = (w : Int) - 4 - x + (i : Int) * 1 := by omega
    have e2 : y + ((i.rev : Fin 4) : Int) * 1 = y + 3 + (i : Int) * (-1) := by omega
    rw [e1, e2] at this; exact this
  · refine Or.inr (Or.inr (Or.inl ⟨(w : Int) - 4 - x, y - 3, fun i => ?_⟩))
    have := hf i.rev
    have hr := hrev i
    rw [cellAtInt_mirror] at this
    have e1 : (w : Int) - 1 - (x + ((i.rev : Fin 4) : Int) * 1) = (w : Int) - 4 - x + (i : Int) * 1 := by omega
    have e2 : y + ((i.rev : Fin 4) : Int) * (-1) = y - 3 + (i : Int) * 1 := by omega
    rw [e1, e2] at this; exact this

theorem hasFour_mirror_iff (b : Board w) (p : Player) : HasFour h (mirror b) p ↔ HasFour h b p :=
  ⟨hasFour_of_mirror, fun hf => hasFour_of_mirror (b := mirror b) (by rw [mirror_mirror]; exact hf)⟩

theorem totalStones_mirror (b : Board w) : totalStones (mirror b) = totalStones b := by
  unfold totalStones
  exact Equiv.sum_comp Fin.revPerm (fun c => (b c).length)

theorem toMove_mirror (b : Board w) : toMove (mirror b) = toMove b := by
  unfold toMove; rw [totalStones_mirror]

theorem play_mirror (b : Board w) (c : Fin w) (p : Player) :
    play (mirror b) c p = mirror (play b c.rev p) := by
  funext d
  by_cases hd : d = c
  · subst hd; simp [mirror, play]
  · have hne : d.rev ≠ c.rev := fun e => hd (Fin.rev_injective e)
    simp [mirror, play, Function.update, hd, hne]

theorem legal_mirror (b : Board w) (c : Fin w) : Legal h (mirror b) c ↔ Legal h b c.rev := Iff.rfl

theorem safeFor_mirror (p : Player) (k : Nat) :
    ∀ b : Board w, SafeFor h p k b → SafeFor h p k (mirror b) := by
  induction k with
  | zero => intro b hs; exact fun hf => hs ((hasFour_mirror_iff b _).mp hf)
  | succ k ih =>
    intro b hs
    obtain ⟨hn, hrest⟩ := hs
    refine ⟨fun hf => hn ((hasFour_mirror_iff b _).mp hf), ?_⟩
    rcases hrest with h1 | h2 | h3
    · exact Or.inl ((hasFour_mirror_iff b _).mpr h1)
    · exact Or.inr (Or.inl (fun c => h2 c.rev))
    · refine Or.inr (Or.inr ?_)
      rw [toMove_mirror]
      by_cases ht : toMove b = p
      · rw [if_pos ht] at h3 ⊢
        obtain ⟨c, hc, hs⟩ := h3
        refine ⟨c.rev, by simpa [Legal, mirror] using hc, ?_⟩
        rw [play_mirror, Fin.rev_rev]; exact ih _ hs
      · rw [if_neg ht] at h3 ⊢
        intro c hc
        rw [play_mirror]; exact ih _ (h3 c.rev hc)

theorem safe_mirror {b : Board w} (hs : Safe h b) : Safe h (mirror b) :=
  fun k => safeFor_mirror .black k b (hs k)

theorem safe_of_mirror {b : Board w} (hs : Safe h (mirror b)) : Safe h b := by
  have := safe_mirror hs; rwa [mirror_mirror] at this

#print axioms safe_mirror

end C4W5
