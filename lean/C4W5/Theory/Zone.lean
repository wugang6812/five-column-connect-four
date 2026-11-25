import C4W5.Theory.ShiftDown
import C4W5.Cert.Real

/-!
# The one-sided zone theorem (ZONE_THEOREM.md), board level

Rows `0 … K-1` are exact; a column that has grown above row `K` only carries a label.
The proof works with invariants of the real board (discipline `E`, `T`) and the truncation to `K` rows.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

/-! ## A generic two-ply invariant principle -/

theorem safe_of_inv2 {H : Nat} (Inv : Board 5 → Prop)
    (h0 : ∀ R, Inv R → toMove R = .white ∧ ¬ HasFour H R .white)
    (hstep : ∀ R, Inv R → ∀ c, Legal H R c →
      ¬ HasFour H (play R c .white) .white ∧
      (BoardFull H (play R c .white) ∨ ∃ e, Legal H (play R c .white) e ∧
        (HasFour H (play (play R c .white) e .black) .black ∨ Inv (play (play R c .white) e .black)))) :
    ∀ R, Inv R → Safe H R := by
  have key : ∀ k R, Inv R → SafeFor H .black k R := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro R hR
      obtain ⟨htm, hnw⟩ := h0 R hR
      cases k with
      | zero => exact hnw
      | succ k =>
        refine ⟨hnw, Or.inr (Or.inr ?_)⟩
        have hne : ¬ toMove R = .black := by rw [htm]; decide
        rw [if_neg hne, htm]
        intro c hc
        obtain ⟨hnw1, hrest⟩ := hstep R hR c hc
        cases k with
        | zero => exact hnw1
        | succ k =>
          refine ⟨hnw1, ?_⟩
          rcases hrest with hfull | ⟨e, he, hout⟩
          · exact Or.inr (Or.inl hfull)
          · refine Or.inr (Or.inr ?_)
            have htb : toMove (play R c .white) = .black := toMove_play_white htm c
            rw [if_pos htb, htb]
            refine ⟨e, he, ?_⟩
            have hnw2 : ¬ HasFour H (play (play R c .white) e .black) .white :=
              fun hf => hnw1 (hasFour_play_other (by decide) hf)
            rcases hout with hwin | hinv
            · exact safeFor_of_blackFour hnw2 hwin k
            · exact ih k (by omega) _ hinv
  exact fun R hR k => key k R hR

/-! ## Truncation to the bottom `K` rows -/

def trunc (K : Nat) (R : Board 5) : Board 5 := fun c => (R c).take K

theorem trunc_length (K : Nat) (R : Board 5) (c : Fin 5) : (trunc K R c).length = min K (R c).length := by
  simp [trunc]

theorem cell_trunc {K H : Nat} (hKH : K ≤ H) (R : Board 5) (x y : Int) (hy : y < (K : Int)) :
    cellAtInt K (trunc K R) x y = cellAtInt H R x y := by
  unfold cellAtInt
  by_cases hx : 0 ≤ x ∧ x < ((5 : Nat) : Int)
  · rw [dif_pos hx, dif_pos hx]
    by_cases hy0 : 0 ≤ y
    · rw [if_pos ⟨hy0, hy⟩, if_pos ⟨hy0, by omega⟩]
      exact stone_take _ K _ (by omega)
    · rw [if_neg (by omega), if_neg (by omega)]
  · rw [dif_neg hx, dif_neg hx]

theorem cell_trunc_some {K : Nat} {R : Board 5} {x y : Int} {p : Player}
    (hs : cellAtInt K (trunc K R) x y = some p) : y < (K : Int) := by
  obtain ⟨c, -, -, hyK, -⟩ := cellAtInt_some hs
  exact hyK

/-- A four of the truncated board is a four of the real board. -/
theorem hasFour_of_trunc {K H : Nat} (hKH : K ≤ H) {R : Board 5} {p : Player}
    (hf : HasFour K (trunc K R) p) : HasFour H R p := by
  obtain ⟨d, hd, x, y, hdir⟩ := exists_dir hf
  apply hasFour_of_dir d hd (x := x) (y := y)
  intro i
  rw [← cell_trunc hKH R _ _ (cell_trunc_some (hdir i))]
  exact hdir i

theorem trunc_play_low {K : Nat} {R : Board 5} {c : Fin 5} (p : Player) (hl : (R c).length < K) :
    trunc K (play R c p) = play (trunc K R) c p := by
  funext d
  by_cases hd : d = c
  · subst hd
    simp only [trunc, play_eq]
    rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by omega)]
  · simp only [trunc, play_ne _ _ _ _ hd]

theorem trunc_play_high {K : Nat} {R : Board 5} {c : Fin 5} (p : Player) (hl : K ≤ (R c).length) :
    trunc K (play R c p) = trunc K R := by
  funext d
  by_cases hd : d = c
  · subst hd
    simp only [trunc, play_eq]
    rw [List.take_append_of_le_length hl]
  · simp only [trunc, play_ne _ _ _ _ hd]

/-! ## Discipline -/

/-- `E`: every exceptional White stone lies in rows `≤ K-4` (0-based). -/
def DiscE (K : Nat) (R : Board 5) : Prop := ∀ c r, Exceptional R c r → r + 4 ≤ K

/-- `T` for one column: a non-full column that is empty or has a White top has height `≤ K-4`. -/
def TCol (K H : Nat) (R : Board 5) (c : Fin 5) : Prop :=
  (R c).length < H → ((R c).length = 0 ∨ stone (R c) ((R c).length - 1) = some .white) →
    (R c).length + 4 ≤ K

theorem exceptional_play {R : Board 5} {c d : Fin 5} {p : Player} {r : Nat}
    (he : Exceptional (play R c p) d r) :
    Exceptional R d r ∨ (d = c ∧ r = (R c).length ∧ p = .white ∧
      ((R c).length = 0 ∨ stone (R c) ((R c).length - 1) = some .white)) := by
  by_cases hd : d = c
  · subst hd
    obtain ⟨h1, h2⟩ := he
    rw [play_eq] at h1 h2
    have hlt := stone_bound _ _ _ h1
    simp only [List.length_append, List.length_cons, List.length_nil] at hlt
    by_cases hr : r < (R d).length
    · left
      rw [stone_append, if_pos hr] at h1
      refine ⟨h1, ?_⟩
      rcases h2 with h2 | h2
      · exact Or.inl h2
      · right; rwa [stone_append, if_pos (by omega)] at h2
    · right
      have hre : r = (R d).length := by omega
      rw [stone_append, if_neg hr, if_pos hre] at h1
      refine ⟨rfl, hre, (Option.some.inj h1), ?_⟩
      rcases h2 with h2 | h2
      · left; omega
      · by_cases h0 : (R d).length = 0
        · exact Or.inl h0
        · right
          rw [stone_append, if_pos (by omega)] at h2
          rw [← hre]; exact h2
  · left
    obtain ⟨h1, h2⟩ := he
    rw [play_ne _ _ _ _ hd] at h1 h2
    exact ⟨h1, h2⟩

theorem discE_play_black {K : Nat} {R : Board 5} (hE : DiscE K R) (e : Fin 5) :
    DiscE K (play R e .black) := by
  intro d r he
  rcases exceptional_play he with h | ⟨-, -, hp, -⟩
  · exact hE d r h
  · cases hp

theorem discE_play_white {K H : Nat} {R : Board 5} (hE : DiscE K R) (c : Fin 5)
    (hT : TCol K H R c) (hl : (R c).length < H) : DiscE K (play R c .white) := by
  intro d r he
  rcases exceptional_play he with h | ⟨-, hr, -, htop⟩
  · exact hE d r h
  · rw [hr]; exact hT hl htop

/-- **A White four lies inside the bottom `K` rows** (shift-down lemma + discipline `E`). -/
theorem whiteFour_low {K H : Nat} (hKH : K ≤ H) {R : Board 5} (hE : DiscE K R)
    (hnb : ¬ HasFour H R .black) (hf : HasFour H R .white) : HasFour K (trunc K R) .white := by
  obtain ⟨d, hd, x, y, hdir⟩ := exists_dir hf
  have hdirs : (dxI d = 0 ∧ dyI d = 1) ∨ (dxI d = 1 ∧ dyI d = 0) ∨ (dxI d = 1 ∧ dyI d = 1) ∨
      (dxI d = 1 ∧ dyI d = -1) := by
    have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases hd' with rfl | rfl | rfl | rfl <;> simp [dxI, dyI]
  obtain ⟨i, c, hx, hexc⟩ := exists_exceptional_in_line hdirs hnb hdir
  have hrow := hE c _ hexc
  obtain ⟨c', -, hy0, -, -⟩ := cellAtInt_some (hdir i)
  apply hasFour_of_dir d hd (x := x) (y := y)
  intro j
  have hi := i.isLt
  have hj := j.isLt
  obtain ⟨c'', -, hyj0, -, -⟩ := cellAtInt_some (hdir j)
  have hlow : y + (j : Int) * dyI d < (K : Int) := by
    have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases hd' with rfl | rfl | rfl | rfl <;> simp [dyI] at hy0 hrow hyj0 ⊢ <;> omega
  rw [cell_trunc hKH R _ _ hlow]
  exact hdir j

/-! ## Labels and the abstract zone game -/

inductive Lab where
  | low | odd | dead
  deriving DecidableEq

def labOf (H K : Nat) (l : List Player) : Lab :=
  if l.length ≤ K then .low else if (H - l.length) % 2 = 1 then .odd else .dead

def labs (H K : Nat) (R : Board 5) : Fin 5 → Lab := fun c => labOf H K (R c)

theorem labs_play (H K : Nat) (R : Board 5) (e : Fin 5) (p : Player) :
    labs H K (play R e p) = Function.update (labs H K R) e (labOf H K (R e ++ [p])) := by
  funext d
  by_cases hd : d = e
  · subst hd; simp [labs, play_eq]
  · simp [labs, play_ne _ _ _ _ hd, Function.update, hd]

/-- Black's move `e` in the abstract game leads back into `I`. -/
def BlackOut (K : Nat) (I : Board 5 → (Fin 5 → Lab) → Prop) (L : Board 5) (ℓ : Fin 5 → Lab)
    (e : Fin 5) : Prop :=
  (ℓ e = .low ∧ (L e).length < K ∧ I (play L e .black) ℓ) ∨
  (ℓ e = .low ∧ (L e).length = K ∧ I L (Function.update ℓ e .odd)) ∨
  (ℓ e = .odd ∧ I L (Function.update ℓ e .dead))

/-- Black wins at once inside the bottom zone. -/
def BlackWin (K : Nat) (L : Board 5) (ℓ : Fin 5 → Lab) : Prop :=
  ∃ e, ℓ e = .low ∧ (L e).length < K ∧ HasFour K (play L e .black) .black

/-- Closure condition of the zone game `G_K`. -/
def ZoneCert (K : Nat) (I : Board 5 → (Fin 5 → Lab) → Prop) : Prop :=
  ∀ L ℓ, I L ℓ → ∀ c : Fin 5,
    (ℓ c = .low → (L c).length < K →
      ¬ HasFour K (play L c .white) .white ∧
      (BlackWin K (play L c .white) ℓ ∨
        ∃ e, (e = c ∨ (L c).length + 5 ≤ K) ∧ BlackOut K I (play L c .white) ℓ e)) ∧
    (ℓ c = .low → (L c).length = K → I L (Function.update ℓ c .dead)) ∧
    (ℓ c = .odd → (∀ d, Function.update ℓ c .dead d = .dead) ∨ BlackWin K L (Function.update ℓ c .dead) ∨
      ∃ e, BlackOut K I L (Function.update ℓ c .dead) e)

/-- The invariant of the real board. -/
structure ZInv (K H : Nat) (I : Board 5 → (Fin 5 → Lab) → Prop) (R : Board 5) : Prop where
  tm : toMove R = .white
  nw : ¬ HasFour H R .white
  nb : ¬ HasFour H R .black
  dE : DiscE K R
  dT : ∀ c, TCol K H R c
  valid : Valid H R
  abs : I (trunc K R) (labs H K R) ∨ ∀ c : Fin 5, K < (R c).length

theorem tcol_play_self_black (K H : Nat) (R : Board 5) (e : Fin 5) : TCol K H (play R e .black) e := by
  intro _ htop
  rw [play_eq] at htop
  rcases htop with h | h
  · simp at h
  · rw [stone_append] at h
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel,
      lt_irrefl, if_false, if_true] at h
    cases h

theorem tcol_play_ne {K H : Nat} {R : Board 5} {e d : Fin 5} (p : Player) (hd : d ≠ e) :
    TCol K H (play R e p) d ↔ TCol K H R d := by
  unfold TCol; rw [play_ne _ _ _ _ hd]

theorem labOf_low {H K : Nat} {l : List Player} (h : labOf H K l = .low) : l.length ≤ K := by
  unfold labOf at h; by_contra hc; rw [if_neg hc] at h; split at h <;> cases h

theorem labOf_odd {H K : Nat} {l : List Player} (h : labOf H K l = .odd) :
    K < l.length ∧ (H - l.length) % 2 = 1 := by
  unfold labOf at h
  by_cases h1 : l.length ≤ K
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : (H - l.length) % 2 = 1
    · exact ⟨by omega, h2⟩
    · rw [if_neg h2] at h; cases h

theorem labOf_dead {H K : Nat} {l : List Player} (h : labOf H K l = .dead) : K < l.length := by
  unfold labOf at h
  by_cases h1 : l.length ≤ K
  · rw [if_pos h1] at h; cases h
  · omega

/-- Carrying out an abstract Black move on the real board. -/
theorem blackOut_real {K H : Nat} (hK : K % 2 = 0) (hH : H % 2 = 0) (hKH : K + 2 ≤ H)
    {I : Board 5 → (Fin 5 → Lab) → Prop} {R₁ : Board 5} {e : Fin 5}
    (ho : BlackOut K I (trunc K R₁) (labs H K R₁) e) :
    Legal H R₁ e ∧ I (trunc K (play R₁ e .black)) (labs H K (play R₁ e .black)) := by
  rcases ho with ⟨hl, hlen, hI⟩ | ⟨hl, hlen, hI⟩ | ⟨hl, hI⟩
  · have h1 := labOf_low hl
    rw [trunc_length] at hlen
    have hlt : (R₁ e).length < K := by omega
    refine ⟨by unfold Legal; omega, ?_⟩
    rw [trunc_play_low _ hlt, labs_play]
    have : labOf H K (R₁ e ++ [.black]) = labs H K R₁ e := by
      rw [hl]; unfold labOf; rw [if_pos (by simp; omega)]
    rw [this, Function.update_eq_self]; exact hI
  · have h1 := labOf_low hl
    rw [trunc_length] at hlen
    have hlt : (R₁ e).length = K := by omega
    refine ⟨by unfold Legal; omega, ?_⟩
    rw [trunc_play_high _ (by omega), labs_play]
    have : labOf H K (R₁ e ++ [.black]) = .odd := by
      unfold labOf
      rw [if_neg (by simp; omega), if_pos (by simp; omega)]
    rw [this]; exact hI
  · obtain ⟨h1, h2⟩ := labOf_odd hl
    refine ⟨by unfold Legal; omega, ?_⟩
    rw [trunc_play_high _ (by omega), labs_play]
    have : labOf H K (R₁ e ++ [.black]) = .dead := by
      unfold labOf
      rw [if_neg (by simp; omega), if_neg (by simp; omega)]
    rw [this]; exact hI

theorem blackWin_real {K H : Nat} (hKH : K + 2 ≤ H) {R₁ : Board 5}
    (hw : BlackWin K (trunc K R₁) (labs H K R₁)) :
    ∃ e, Legal H R₁ e ∧ HasFour H (play R₁ e .black) .black := by
  obtain ⟨e, hl, hlen, hf⟩ := hw
  have h1 := labOf_low hl
  rw [trunc_length] at hlen
  have hlt : (R₁ e).length < K := by omega
  refine ⟨e, by unfold Legal; omega, ?_⟩
  rw [← trunc_play_low _ hlt] at hf
  exact hasFour_of_trunc (by omega) hf

theorem play_len_self (R : Board 5) (c : Fin 5) (p : Player) : (play R c p c).length = (R c).length + 1 := by
  rw [play_eq]; simp

theorem play_len_ge (R : Board 5) (c d : Fin 5) (p : Player) : (R d).length ≤ (play R c p d).length := by
  by_cases hd : d = c
  · subst hd; rw [play_len_self]; omega
  · rw [play_ne _ _ _ _ hd]

/-- One round of the real game under the zone strategy. -/
theorem zone_step {K H : Nat} (hK : K % 2 = 0) (hH : H % 2 = 0) (hKH : K + 2 ≤ H)
    {I : Board 5 → (Fin 5 → Lab) → Prop} (hI : ZoneCert K I) {R : Board 5} (inv : ZInv K H I R)
    (c : Fin 5) (hc : Legal H R c) :
    ¬ HasFour H (play R c .white) .white ∧
    (BoardFull H (play R c .white) ∨ ∃ e, Legal H (play R c .white) e ∧
      (HasFour H (play (play R c .white) e .black) .black ∨
        ZInv K H I (play (play R c .white) e .black))) := by
  have hcl : (R c).length < H := hc
  have hE1 : DiscE K (play R c .white) := discE_play_white inv.dE c (inv.dT c) hc
  have hnb1 : ¬ HasFour H (play R c .white) .black := fun hf => inv.nb (hasFour_play_other (by decide) hf)
  have hv1 : Valid H (play R c .white) := play_valid inv.valid hc
  have nwOf : ¬ HasFour K (trunc K (play R c .white)) .white → ¬ HasFour H (play R c .white) .white :=
    fun hnt hf => hnt (whiteFour_low (by omega) hE1 hnb1 hf)
  have hTne : ∀ d, d ≠ c → TCol K H (play R c .white) d := fun d hd => (tcol_play_ne .white hd).mpr (inv.dT d)
  -- building the invariant after Black's reply
  have mk : ∀ e, ¬ HasFour H (play R c .white) .white → Legal H (play R c .white) e →
      (∀ d, d ≠ e → TCol K H (play R c .white) d) →
      (I (trunc K (play (play R c .white) e .black)) (labs H K (play (play R c .white) e .black)) ∨
        ∀ d : Fin 5, K < (play (play R c .white) e .black d).length) →
      HasFour H (play (play R c .white) e .black) .black ∨ ZInv K H I (play (play R c .white) e .black) := by
    intro e hnw1 he hT habs
    by_cases hb : HasFour H (play (play R c .white) e .black) .black
    · exact Or.inl hb
    · right
      exact
        { tm := toMove_play_black (toMove_play_white inv.tm c) e
          nw := fun hf => hnw1 (hasFour_play_other (by decide) hf)
          nb := hb
          dE := discE_play_black hE1 e
          dT := fun d => by
            by_cases hd : d = e
            · subst hd; exact tcol_play_self_black K H _ d
            · exact (tcol_play_ne .black hd).mpr (hT d hd)
          valid := play_valid hv1 he
          abs := habs }
  have tail : ¬ HasFour H (play R c .white) .white → (∀ d, TCol K H (play R c .white) d) →
      (∀ d : Fin 5, K < (play R c .white d).length) →
      BoardFull H (play R c .white) ∨ ∃ e, Legal H (play R c .white) e ∧
        (HasFour H (play (play R c .white) e .black) .black ∨
          ZInv K H I (play (play R c .white) e .black)) := by
    intro hnw1 hT hhigh
    by_cases hfull : BoardFull H (play R c .white)
    · exact Or.inl hfull
    · obtain ⟨d, hd⟩ := exists_legal hv1 hfull
      exact Or.inr ⟨d, hd, mk d hnw1 hd (fun d' _ => hT d') (Or.inr fun d' =>
        lt_of_lt_of_le (hhigh d') (play_len_ge _ _ _ _))⟩
  by_cases hlow : (R c).length < K
  · -- White plays inside the exact zone
    rcases inv.abs with hI0 | hhigh
    swap
    · have := hhigh c; omega
    have hlab : labs H K R c = .low := by simp only [labs, labOf]; rw [if_pos (by omega)]
    obtain ⟨hnf, hrest⟩ := (hI _ _ hI0 c).1 hlab (by rw [trunc_length]; omega)
    rw [← trunc_play_low _ hlow] at hnf hrest
    have hlabs1 : labs H K (play R c .white) = labs H K R := by
      rw [labs_play]
      have : labOf H K (R c ++ [.white]) = labs H K R c := by
        rw [hlab]; unfold labOf; rw [if_pos (by simp; omega)]
      rw [this, Function.update_eq_self]
    rw [← hlabs1] at hrest
    have hnw1 := nwOf hnf
    refine ⟨hnw1, Or.inr ?_⟩
    rcases hrest with hwin | ⟨e, hmust, hout⟩
    · obtain ⟨e, he, hf⟩ := blackWin_real hKH hwin
      exact ⟨e, he, Or.inl hf⟩
    · obtain ⟨he, hI2⟩ := blackOut_real hK hH hKH hout
      refine ⟨e, he, mk e hnw1 he (fun d hd => ?_) (Or.inl hI2)⟩
      by_cases hdc : d = c
      · subst hdc
        have : (R d).length + 5 ≤ K := by
          rcases hmust with h | h
          · exact absurd h.symm hd
          · rw [trunc_length] at h; omega
        intro _ _; rw [play_len_self]; omega
      · exact hTne d hdc
  · have hnt : ¬ HasFour K (trunc K (play R c .white)) .white := by
      rw [trunc_play_high _ (by omega)]
      exact fun hf => inv.nw (hasFour_of_trunc (by omega) hf)
    have hnw1 := nwOf hnt
    refine ⟨hnw1, ?_⟩
    have htr1 : trunc K (play R c .white) = trunc K R := trunc_play_high _ (by omega)
    by_cases hcap : (R c).length + 1 = H
    · -- White caps the column
      have hT1 : ∀ d, TCol K H (play R c .white) d := fun d => by
        by_cases hd : d = c
        · subst hd; intro hlt; rw [play_len_self] at hlt; omega
        · exact hTne d hd
      rcases inv.abs with hI0 | hhigh
      · have hlab : labs H K R c = .odd := by
          simp only [labs, labOf]; rw [if_neg (by omega), if_pos (by omega)]
        have hlabs1 : labs H K (play R c .white) = Function.update (labs H K R) c .dead := by
          rw [labs_play]
          have : labOf H K (R c ++ [.white]) = .dead := by
            unfold labOf; rw [if_neg (by simp; omega), if_neg (by simp; omega)]
          rw [this]
        have hcert := (hI _ _ hI0 c).2.2 hlab
        rw [← hlabs1, ← htr1] at hcert
        rcases hcert with hall | hwin | ⟨e, hout⟩
        · exact tail hnw1 hT1 (fun d => labOf_dead (hall d))
        · obtain ⟨e, he, hf⟩ := blackWin_real hKH hwin
          exact Or.inr ⟨e, he, Or.inl hf⟩
        · obtain ⟨he, hI2⟩ := blackOut_real hK hH hKH hout
          exact Or.inr ⟨e, he, mk e hnw1 he (fun d _ => hT1 d) (Or.inl hI2)⟩
      · exact tail hnw1 hT1 (fun d => lt_of_lt_of_le (hhigh d) (play_len_ge _ _ _ _))
    · -- Black covers
      have he : Legal H (play R c .white) c := by unfold Legal; rw [play_len_self]; omega
      refine Or.inr ⟨c, he, mk c hnw1 he (fun d hd => hTne d hd) ?_⟩
      rcases inv.abs with hI0 | hhigh
      · left
        have htr2 : trunc K (play (play R c .white) c .black) = trunc K R := by
          rw [trunc_play_high _ (by rw [play_len_self]; omega), htr1]
        have hlabs2 : labs H K (play (play R c .white) c .black) =
            Function.update (labs H K R) c (labOf H K (play R c .white c ++ [.black])) := by
          rw [labs_play, labs_play, Function.update_idem]
        rw [htr2, hlabs2]
        have hlen2 : (play R c .white c ++ [Player.black]).length = (R c).length + 2 := by
          rw [play_eq]; simp
        by_cases hKc : (R c).length = K
        · have hlab : labs H K R c = .low := by simp only [labs, labOf]; rw [if_pos (by omega)]
          have : labOf H K (play R c .white c ++ [.black]) = .dead := by
            unfold labOf; rw [hlen2, if_neg (by omega), if_neg (by omega)]
          rw [this]
          exact (hI _ _ hI0 c).2.1 hlab (by rw [trunc_length]; omega)
        · have : labOf H K (play R c .white c ++ [.black]) = labs H K R c := by
            have hpar : (H - ((R c).length + 2)) % 2 = (H - (R c).length) % 2 := by omega
            simp only [labs, labOf]
            rw [hlen2, if_neg (show ¬ (R c).length + 2 ≤ K by omega),
              if_neg (show ¬ (R c).length ≤ K by omega), hpar]
          rw [this, Function.update_eq_self]; exact hI0
      · exact Or.inr fun d => lt_of_lt_of_le (lt_of_lt_of_le (hhigh d) (play_len_ge _ _ _ _)) (play_len_ge _ _ _ _)

/-- **The one-sided zone theorem.**  If the abstract positions `I` are closed under the zone game
`G_K`, Black does not lose from any real board (of any even height `H ≥ K + 2`) satisfying the
invariant. -/
theorem zone_safe {K H : Nat} (hK : K % 2 = 0) (hH : H % 2 = 0) (hKH : K + 2 ≤ H)
    {I : Board 5 → (Fin 5 → Lab) → Prop} (hI : ZoneCert K I) {R : Board 5} (inv : ZInv K H I R) :
    Safe H R :=
  safe_of_inv2 (ZInv K H I) (fun _ h => ⟨h.tm, h.nw⟩)
    (fun _ h c hc => zone_step hK hH hKH hI h c hc) R inv

#print axioms zone_safe

end C4W5
