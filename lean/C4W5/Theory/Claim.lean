import C4W5.Theory.Zone

/-!
# The claim criterion (ENDGAME_CRITERIA.md, criteria Z and ZC), board level

White to move.  Black *claims* a column `q` with an odd number of empty cells: he only covers there,
so he gets every cell `(q, r)` with `r - h₀` odd above the present height `h₀` (0-based rows).
If every non-vertical line through an exceptional or potentially exceptional cell contains a Black
stone or a claimed cell, Black does not lose by covering (after a cap: any column other than `q`).
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

/-- The next cell of a non-full column that is empty or has a White top. -/
def PotExc (H : Nat) (R : Board 5) (c : Fin 5) (r : Nat) : Prop :=
  r = (R c).length ∧ (R c).length < H ∧
    ((R c).length = 0 ∨ stone (R c) ((R c).length - 1) = some .white)

def Claimed (q : Fin 5) (h0 : Nat) (x y : Int) : Prop :=
  x = (q.val : Int) ∧ (h0 : Int) < y ∧ (y - h0) % 2 = 1

instance (q : Fin 5) (h0 : Nat) (x y : Int) : Decidable (Claimed q h0 x y) := by
  unfold Claimed; infer_instance

/-- The line from `(x, y)` in direction `(1, dy)` can never become a White four. -/
def LineOK (H : Nat) (R : Board 5) (q : Fin 5) (h0 : Nat) (x y dy : Int) : Prop :=
  ∃ j : Fin 4, cellAtInt H R (x + (j : Int) * 1) (y + (j : Int) * dy) = some .black ∨
    Claimed q h0 (x + (j : Int) * 1) (y + (j : Int) * dy) ∨
    ¬ (0 ≤ x + (j : Int) * 1 ∧ x + (j : Int) * 1 < 5 ∧ 0 ≤ y + (j : Int) * dy ∧
      y + (j : Int) * dy < (H : Int))

/-- All non-vertical lines through the cell `(c, r)` are dead. -/
def LinesDead (H : Nat) (R : Board 5) (q : Fin 5) (h0 : Nat) (c : Fin 5) (r : Nat) : Prop :=
  ∀ dy ∈ ([0, 1, -1] : List Int), ∀ i : Fin 4,
    LineOK H R q h0 ((c.val : Int) - (i : Int) * 1) ((r : Int) - (i : Int) * dy) dy

def TopThree (R : Board 5) (c : Fin 5) : Prop :=
  3 ≤ (R c).length ∧ stone (R c) ((R c).length - 1) = some .white ∧
    stone (R c) ((R c).length - 2) = some .white ∧ stone (R c) ((R c).length - 3) = some .white

theorem cell_play_mono {H : Nat} {R : Board 5} {x y : Int} {p : Player}
    (hs : cellAtInt H R x y = some p) (c : Fin 5) (p' : Player) :
    cellAtInt H (play R c p') x y = some p := by
  obtain ⟨c2, hx, hy0, hyh, hst⟩ := cellAtInt_some hs
  rw [hx, cellAtInt_fin _ c2 _ hy0 hyh]
  by_cases hc : c2 = c
  · subst hc
    rw [play_eq, stone_append, if_pos (stone_bound _ _ _ hst)]; exact hst
  · rw [play_ne _ _ _ _ hc]; exact hst

theorem lineOK_play {H : Nat} {R : Board 5} {q : Fin 5} {h0 : Nat} {x y dy : Int}
    (h : LineOK H R q h0 x y dy) (c : Fin 5) (p : Player) : LineOK H (play R c p) q h0 x y dy := by
  obtain ⟨j, hj | hj | hj⟩ := h
  · exact ⟨j, Or.inl (cell_play_mono hj c p)⟩
  · exact ⟨j, Or.inr (Or.inl hj)⟩
  · exact ⟨j, Or.inr (Or.inr hj)⟩

theorem linesDead_play {H : Nat} {R : Board 5} {q : Fin 5} {h0 : Nat} {c : Fin 5} {r : Nat}
    (h : LinesDead H R q h0 c r) (e : Fin 5) (p : Player) : LinesDead H (play R e p) q h0 c r :=
  fun dy hdy i => lineOK_play (h dy hdy i) e p

/-- A dead line is not a White four in any later board. -/
theorem no_white_line {H : Nat} {R R' : Board 5} {q : Fin 5} {h0 : Nat} {x y dy : Int}
    (hok : LineOK H R q h0 x y dy)
    (hblack : ∀ x y, cellAtInt H R x y = some .black → cellAtInt H R' x y = some .black)
    (hcl : ∀ x y, Claimed q h0 x y → cellAtInt H R' x y ≠ some .white) :
    ¬ HasFourDir H R' .white x y 1 dy := by
  intro hf
  obtain ⟨j, hj | hj | hj⟩ := hok
  · have := hf j
    rw [hblack _ _ hj] at this
    cases this
  · exact hcl _ _ hj (hf j)
  · obtain ⟨c, hx, hy0, hyh, -⟩ := cellAtInt_some (hf j)
    have := c.isLt
    exact hj ⟨by omega, by omega, hy0, hyh⟩

/-- The invariant. -/
structure CInv (H : Nat) (q : Fin 5) (h0 : Nat) (R : Board 5) : Prop where
  tm : toMove R = .white
  nw : ¬ HasFour H R .white
  nb : ¬ HasFour H R .black
  valid : Valid H R
  ge : h0 ≤ (R q).length
  par : (R q).length < H → (R q).length % 2 = h0 % 2
  alt : ∀ r, h0 < r → r < (R q).length → (r - h0) % 2 = 1 → stone (R q) r = some .black
  ntr : ∀ c, (R c).length < H → ¬ TopThree R c
  dead : ∀ c r, Exceptional R c r ∨ PotExc H R c r → LinesDead H R q h0 c r

theorem cell_play_old {H : Nat} {R : Board 5} {c : Fin 5} {p p' : Player} {x y : Int}
    (hs : cellAtInt H (play R c p) x y = some p')
    (hne : ¬ (x = (c.val : Int) ∧ y = ((R c).length : Int))) : cellAtInt H R x y = some p' := by
  rw [cellAtInt_play_ne R c p x y hne] at hs; exact hs

theorem claimed_not_white {H : Nat} {q : Fin 5} {h0 : Nat} {R : Board 5} (inv : CInv H q h0 R)
    (c : Fin 5) (hl : Legal H R c) (x y : Int) (hc : Claimed q h0 x y) :
    cellAtInt H (play R c .white) x y ≠ some .white := by
  intro hw
  obtain ⟨hx, hlt, hodd⟩ := hc
  obtain ⟨c2, hx2, hy0, hyh, hst⟩ := cellAtInt_some hw
  have hc2 : c2 = q := Fin.ext (by omega)
  subst hc2
  have h1 : h0 < y.toNat := by omega
  have h2 : (y.toNat - h0) % 2 = 1 := by omega
  by_cases hcq : c2 = c
  · subst hcq
    rw [play_eq, stone_append] at hst
    by_cases h3 : y.toNat < (R c2).length
    · rw [if_pos h3, inv.alt _ h1 h3 h2] at hst; cases hst
    · rw [if_neg h3] at hst
      by_cases h4 : y.toNat = (R c2).length
      · have := inv.par hl
        omega
      · rw [if_neg h4] at hst; cases hst
  · rw [play_ne _ _ _ _ hcq] at hst
    rw [inv.alt _ h1 (stone_bound _ _ _ hst) h2] at hst; cases hst

/-- White's move does not make a four. -/
theorem cinv_white {H : Nat} {q : Fin 5} {h0 : Nat} {R : Board 5} (inv : CInv H q h0 R)
    (c : Fin 5) (hl : Legal H R c) : ¬ HasFour H (play R c .white) .white := by
  intro hf
  obtain ⟨d, hd, x, y, hdir⟩ := exists_dir hf
  have hnb1 : ¬ HasFour H (play R c .white) .black :=
    fun h => inv.nb (hasFour_play_other (by decide) h)
  by_cases hd0 : d = 0
  · -- vertical
    subst hd0
    have hdir' : ∀ i : Fin 4, cellAtInt H (play R c .white) x (y + (i.val : Int)) = some .white := by
      intro i; have := hdir i; simpa [dxI, dyI] using this
    have hy00 : 0 ≤ y := by
      obtain ⟨_, -, h, -, -⟩ := cellAtInt_some (hdir' 0); simpa using h
    by_cases hnew : x = (c.val : Int) ∧ y + 3 = ((R c).length : Int)
    · obtain ⟨hx, hy⟩ := hnew
      have hc := inv.ntr c hl
      apply hc
      have get : ∀ i : Fin 4, i.val < 3 → stone (R c) (y.toNat + i.val) = some .white := by
        intro i hi
        have h1 := hdir' i
        obtain ⟨c2, hx2, hy0, hyh, hst⟩ := cellAtInt_some h1
        have : c2 = c := Fin.ext (by omega)
        subst this
        rw [play_eq, stone_append] at hst
        have e : (y + (i.val : Int)).toNat = y.toNat + i.val := by omega
        rw [if_pos (by omega)] at hst
        rw [← e]; exact hst
      have g0 := get 0 (by decide)
      have g1 := get 1 (by decide)
      have g2 := get 2 (by decide)
      simp only [Fin.val_zero, add_zero, Fin.val_one, Fin.val_two] at g0 g1 g2
      have e1 : (R c).length - 1 = y.toNat + 2 := by omega
      have e2 : (R c).length - 2 = y.toNat + 1 := by omega
      have e3 : (R c).length - 3 = y.toNat := by omega
      exact ⟨by omega, by rw [e1]; exact g2, by rw [e2]; exact g1, by rw [e3]; exact g0⟩
    · apply inv.nw
      apply hasFour_of_dir 0 (by omega) (x := x) (y := y)
      intro i
      have hgoal : cellAtInt H R x (y + (i.val : Int)) = some .white := by
        apply cell_play_old (hdir' i)
        rintro ⟨hx, hy⟩
        have hi := i.isLt
        -- the new stone is the top one, so the line ends there
        have h3 := hdir' 3
        obtain ⟨c2, hx2, hy0, hyh, hst⟩ := cellAtInt_some h3
        have : c2 = c := Fin.ext (by omega)
        subst this
        have hb := stone_bound _ _ _ hst
        rw [play_eq] at hb
        simp only [List.length_append, List.length_cons, List.length_nil] at hb
        have : ((3 : Fin 4).val : Int) = 3 := rfl
        apply hnew
        refine ⟨hx, ?_⟩
        omega
      simpa [dxI, dyI] using hgoal
  · have hdx : dxI d = 1 := by simp [dxI, hd0]
    have hdy : dyI d = 0 ∨ dyI d = 1 ∨ dyI d = -1 := by
      have hd' : d = 1 ∨ d = 2 ∨ d = 3 := by omega
      rcases hd' with rfl | rfl | rfl <;> simp [dyI]
    have hdirs : (dxI d = 0 ∧ dyI d = 1) ∨ (dxI d = 1 ∧ dyI d = 0) ∨ (dxI d = 1 ∧ dyI d = 1) ∨
        (dxI d = 1 ∧ dyI d = -1) := by
      rcases hdy with h | h | h
      · exact Or.inr (Or.inl ⟨hdx, h⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hdx, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hdx, h⟩))
    obtain ⟨i, c', hx, hexc⟩ := exists_exceptional_in_line hdirs hnb1 hdir
    obtain ⟨c2, -, hy0, -, -⟩ := cellAtInt_some (hdir i)
    have hcell : Exceptional R c' (y + (i : Int) * dyI d).toNat ∨
        PotExc H R c' (y + (i : Int) * dyI d).toNat := by
      rcases exceptional_play hexc with h | ⟨rfl, hr, -, htop⟩
      · exact Or.inl h
      · exact Or.inr ⟨hr, hl, htop⟩
    have hdead := inv.dead c' _ hcell (dyI d) (by
      rcases hdy with h | h | h <;> rw [h] <;> simp) i
    have ex : (c'.val : Int) - (i : Int) * 1 = x := by rw [hdx] at hx; omega
    have ey : (((y + (i : Int) * dyI d).toNat : Nat) : Int) - (i : Int) * dyI d = y := by
      rw [Int.toNat_of_nonneg hy0]; exact Int.add_sub_cancel _ _
    rw [ex, ey] at hdead
    rw [hdx] at hdir
    exact no_white_line hdead (fun x y h => cell_play_mono h c .white)
      (claimed_not_white inv c hl) hdir

theorem play_len (R : Board 5) (c d : Fin 5) (p : Player) :
    (play R c p d).length = (R d).length + (if d = c then 1 else 0) := by
  by_cases h : d = c
  · subst h; simp [play_eq]
  · simp [play_ne _ _ _ _ h, h]

theorem not_exc_top_black {R : Board 5} {e : Fin 5} {H r : Nat} :
    ¬ PotExc H (play R e .black) e r := by
  rintro ⟨-, -, h | h⟩
  · rw [play_eq] at h; simp at h
  · rw [play_eq, stone_append] at h
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel,
      lt_irrefl, if_false, if_true] at h
    cases h

/-- After White's move `c` and Black's reply `e` (cover, or any column but `q` after a cap) the
invariant holds again. -/
theorem cinv_step {H : Nat} {q : Fin 5} {h0 : Nat} {R : Board 5} (inv : CInv H q h0 R)
    (c : Fin 5) (hl : Legal H R c) (e : Fin 5) (he : Legal H (play R c .white) e)
    (hcase : e = c ∨ ((R c).length + 1 = H ∧ e ≠ q))
    (hnb2 : ¬ HasFour H (play (play R c .white) e .black) .black) :
    CInv H q h0 (play (play R c .white) e .black) := by
  have hl' : (R c).length < H := hl
  have he' : (play R c .white e).length < H := he
  have l2 : ∀ d, (play (play R c .white) e .black d).length =
      (R d).length + (if d = c then 1 else 0) + (if d = e then 1 else 0) := by
    intro d; rw [play_len, play_len]
  have hnw1 := cinv_white inv c hl
  refine ⟨toMove_play_black (toMove_play_white inv.tm c) e,
    fun hf => hnw1 (hasFour_play_other (by decide) hf), hnb2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    have h1 := l2 d
    have h2 := inv.valid d
    have h3 := play_len R c e .white
    by_cases hdc : d = c <;> by_cases hde : d = e
    · subst hdc; subst hde; simp at h1 h3; omega
    · subst hdc; simp [hde] at h1; omega
    · subst hde; simp [hdc] at h1 h3; omega
    · simp [hdc, hde] at h1; omega
  · have h1 := l2 q; have := inv.ge; omega
  · intro hlt
    have h1 := l2 q
    rw [h1] at hlt ⊢
    by_cases hqc : q = c <;> by_cases hqe : q = e
    · subst hqc; subst hqe
      simp only [if_true] at hlt ⊢
      have := inv.par hl'; omega
    · rcases hcase with h | ⟨hcap, -⟩
      · exact absurd (hqc.trans h.symm) hqe
      · subst hqc; simp only [if_true, if_neg hqe] at hlt; omega
    · rcases hcase with h | ⟨-, hne⟩
      · exact absurd (hqe.trans h) hqc
      · exact absurd hqe.symm hne
    · simp only [if_neg hqc, if_neg hqe, add_zero] at hlt ⊢
      exact inv.par hlt
  · intro r hr1 hr2 hr3
    by_cases hqe : q = e
    · have hec : e = c := by
        rcases hcase with h | ⟨-, hne⟩
        · exact h
        · exact absurd hqe.symm hne
      subst hqe; subst hec
      rw [play_eq, play_eq, stone_append, stone_append]
      simp only [List.length_append, List.length_cons, List.length_nil]
      have hp := inv.par hl
      by_cases h1 : r < (R q).length
      · rw [if_pos (by omega), if_pos h1]; exact inv.alt r hr1 h1 hr3
      · have h2 := l2 q
        simp at h2
        have : r = (R q).length + 1 := by omega
        rw [if_neg (by omega), if_pos this]
    · rw [play_ne _ _ _ _ hqe]
      by_cases hqc : q = c
      · subst hqc
        rw [play_eq, stone_append]
        have hp := inv.par hl
        have h2 := l2 q
        simp [hqe] at h2
        by_cases h1 : r < (R q).length
        · rw [if_pos h1]; exact inv.alt r hr1 h1 hr3
        · omega
      · rw [play_ne _ _ _ _ hqc]
        rw [play_ne _ _ _ _ hqe, play_ne _ _ _ _ hqc] at hr2
        exact inv.alt r hr1 hr2 hr3
  · intro d hd ht
    by_cases hde : d = e
    · subst hde
      obtain ⟨-, h1, -, -⟩ := ht
      rw [play_eq, stone_append] at h1
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel,
        lt_irrefl, if_false, if_true] at h1
      cases h1
    · have h1 := l2 d
      by_cases hdc : d = c
      · rcases hcase with h | ⟨hcap, -⟩
        · exact hde (hdc.trans h.symm)
        · simp [hdc, hde] at h1; subst hdc; omega
      · unfold TopThree at ht
        rw [play_ne _ _ _ _ hde, play_ne _ _ _ _ hdc] at ht
        rw [play_ne _ _ _ _ hde, play_ne _ _ _ _ hdc] at hd
        exact inv.ntr d hd ht
  · intro d r hcell
    apply linesDead_play
    apply linesDead_play
    apply inv.dead
    rcases hcell with hE | hP
    · rcases exceptional_play hE with h | ⟨-, -, hp, -⟩
      · rcases exceptional_play h with h' | ⟨rfl, hr, -, htop⟩
        · exact Or.inl h'
        · exact Or.inr ⟨hr, hl, htop⟩
      · cases hp
    · by_cases hde : d = e
      · subst hde; exact absurd hP not_exc_top_black
      · have h1 := l2 d
        by_cases hdc : d = c
        · rcases hcase with h | ⟨hcap, -⟩
          · exact absurd (hdc.trans h.symm) hde
          · obtain ⟨-, hlt, -⟩ := hP
            simp [hdc, hde] at h1; subst hdc; omega
        · unfold PotExc at hP
          rw [play_ne _ _ _ _ hde, play_ne _ _ _ _ hdc] at hP
          exact Or.inr hP

/-- If all columns but `q` are full, the number of stones is `|q| + 4H`. -/
theorem total_of_others_full {H : Nat} {R : Board 5} {q : Fin 5}
    (h : ∀ e, e ≠ q → (R e).length = H) : totalStones R = (R q).length + 4 * H := by
  unfold totalStones
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ q)]
  congr 1
  rw [Finset.sum_congr rfl (fun e he => h e (Finset.ne_of_mem_erase he))]
  simp

theorem totalStones_odd_of_white {R : Board 5} (h : toMove R = .white) : totalStones R % 2 = 1 := by
  unfold toMove at h
  by_cases he : totalStones R % 2 = 0
  · rw [if_pos he] at h; cases h
  · omega

/-- **Criterion ZC (and Z).**  `q` is a column with an odd number of empty cells. -/
theorem claim_safe {H : Nat} (hH : H % 2 = 0) {R : Board 5} (q : Fin 5)
    (htm : toMove R = .white) (hnw : ¬ HasFour H R .white) (hnb : ¬ HasFour H R .black)
    (hv : Valid H R) (hq : (H - (R q).length) % 2 = 1)
    (hntr : ∀ c, (R c).length < H → ¬ TopThree R c)
    (hdead : ∀ c r, Exceptional R c r ∨ PotExc H R c r → LinesDead H R q (R q).length c r) :
    Safe H R := by
  have h0lt : (R q).length < H := by omega
  generalize hh0 : (R q).length = h0 at hq hdead h0lt
  have root : CInv H q h0 R :=
    ⟨htm, hnw, hnb, hv, by omega, fun _ => by rw [hh0], fun r h1 h2 _ => by omega, hntr, hdead⟩
  refine safe_of_inv2 (CInv H q h0) (fun R inv => ⟨inv.tm, inv.nw⟩) ?_ R root
  intro R inv c hl
  have hl' : (R c).length < H := hl
  refine ⟨cinv_white inv c hl, ?_⟩
  by_cases hfull : BoardFull H (play R c .white)
  · exact Or.inl hfull
  right
  have fin : ∀ e, Legal H (play R c .white) e → (e = c ∨ ((R c).length + 1 = H ∧ e ≠ q)) →
      Legal H (play R c .white) e ∧
        (HasFour H (play (play R c .white) e .black) .black ∨
          CInv H q h0 (play (play R c .white) e .black)) := by
    intro e he hcase
    refine ⟨he, ?_⟩
    by_cases hb : HasFour H (play (play R c .white) e .black) .black
    · exact Or.inl hb
    · exact Or.inr (cinv_step inv c hl e he hcase hb)
  by_cases hcap : (R c).length + 1 < H
  · exact ⟨c, fin c (by show (play R c .white c).length < H; rw [play_len]; simp; omega) (Or.inl rfl)⟩
  · have hcapeq : (R c).length + 1 = H := by omega
    -- a column other than `q` is not full
    have hex : ∃ e, e ≠ q ∧ (play R c .white e).length ≠ H := by
      by_contra hcon
      have hall : ∀ e, e ≠ q → (play R c .white e).length = H := by
        intro e heq; by_contra hne; exact hcon ⟨e, heq, hne⟩
      by_cases hqfull : (play R c .white q).length = H
      · apply hfull
        intro e
        by_cases heq : e = q
        · rw [heq]; exact hqfull
        · exact hall e heq
      · have ht := total_of_others_full hall
        rw [totalStones_play] at ht
        have hodd := totalStones_odd_of_white inv.tm
        have hqc : q ≠ c := by
          rintro rfl
          apply hqfull; rw [play_len]; simp; omega
        rw [play_ne _ _ _ _ hqc] at ht hqfull
        have hvq := inv.valid q
        have := inv.par (by omega)
        omega
    obtain ⟨e, heq, hne⟩ := hex
    have hle : (play R c .white e).length ≤ H := by
      rw [play_len]
      have := inv.valid e
      by_cases hec : e = c
      · subst hec; simp; omega
      · simp [hec]; exact this
    exact ⟨e, fin e (by show (play R c .white e).length < H; omega) (Or.inr ⟨hcapeq, heq⟩)⟩

#print axioms claim_safe

end C4W5
