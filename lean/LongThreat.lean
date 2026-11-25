import LongThreatDefs
namespace C4W5.LongThreat
open Connect4 (Player opponent)
open Connect4.NarrowBoards
set_option linter.deprecated false

theorem no_white {H : Nat} {R : Board 5} {c : Fin 5} (hl : Legal H R c)
    (hnw : ¬ HasFour H R .white) (hnb : ¬ HasFour H R .black)
    (hntr : ¬ TopThree R c)
    {t : Fin 5} {rho : Nat} {Q : Fin 5 → Prop} {h0 : Fin 5 → Nat}
    (dead : ∀ d r, Exceptional R d r ∨ PotExc H R d r → Dead H R t rho Q h0 d r)
    (guard : ∀ x y, Guard t rho Q h0 x y → cellAtInt H (play R c .white) x y ≠ some .white) :
    ¬ HasFour H (play R c .white) .white := by
  intro hf
  obtain ⟨d, hd, x, y, hdir⟩ := exists_dir hf
  have hnb1 : ¬ HasFour H (play R c .white) .black :=
    fun h => hnb (hasFour_play_other (by decide) h)
  by_cases hd0 : d = 0
  · -- vertical
    subst hd0
    have hdir' : ∀ i : Fin 4, cellAtInt H (play R c .white) x (y + (i.val : Int)) = some .white := by
      intro i; have := hdir i; simpa [dxI, dyI] using this
    have hy00 : 0 ≤ y := by
      obtain ⟨_, -, h, -, -⟩ := cellAtInt_some (hdir' 0); simpa using h
    by_cases hnew : x = (c.val : Int) ∧ y + 3 = ((R c).length : Int)
    · obtain ⟨hx, hy⟩ := hnew
      have hc := hntr
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
    · apply hnw
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
    have hdead := dead c' _ hcell (dyI d) (by
      rcases hdy with h | h | h <;> rw [h] <;> simp) i
    have ex : (c'.val : Int) - (i : Int) * 1 = x := by rw [hdx] at hx; omega
    have ey : (((y + (i : Int) * dyI d).toNat : Nat) : Int) - (i : Int) * dyI d = y := by
      rw [Int.toNat_of_nonneg hy0]; exact Int.add_sub_cancel _ _
    obtain ⟨j, hj⟩ := hdead
    dsimp only at hj
    have ex' : (↑c'.val : Int) - (i : Int) * 1 + (j : Int) * 1 = x + (j : Int) * 1 :=
      congrArg (· + (j : Int) * 1) ex
    have ey' : (↑((y + (i : Int) * dyI d).toNat) : Int) - (i : Int) * dyI d + (j : Int) * dyI d =
        y + (j : Int) * dyI d := congrArg (· + (j : Int) * dyI d) ey
    rw [ex', ey'] at hj
    rw [hdx] at hdir
    rcases hj with hb | hg | ho
    · have hw := hdir j
      rw [cell_play_mono hb c .white] at hw
      cases hw
    · exact guard _ _ hg (hdir j)
    · obtain ⟨d', hx, hy0, hyh, _⟩ := cellAtInt_some (hdir j)
      have := d'.isLt
      exact ho ⟨by omega, by omega, hy0, hyh⟩


structure Inv (H : Nat) (t : Fin 5) (rho : Nat) (Q : Fin 5 → Prop)
    (h0 : Fin 5 → Nat) (R : Board 5) : Prop where
  tm : toMove R = .white
  nw : ¬ HasFour H R .white
  nb : ¬ HasFour H R .black
  valid : Valid H R
  ge : ∀ q, q = t ∨ Q q → h0 q ≤ (R q).length
  par : ∀ q, q = t ∨ Q q → (R q).length % 2 = h0 q % 2
  alt : ∀ q, q = t ∨ Q q → ∀ r, h0 q < r → r < (R q).length →
    (r - h0 q) % 2 = 1 → stone (R q) r = some .black
  below : (R t).length < rho
  ntr : ∀ c, Legal H R c → ¬ TopThree R c
  threat : Threat H R t rho
  dead : ∀ c r, Exceptional R c r ∨ PotExc H R c r → Dead H R t rho Q h0 c r

theorem threat_play {H : Nat} {R : Board 5} {t : Fin 5} {rho : Nat} (ht : Threat H R t rho)
    (c : Fin 5) (p : Player) : Threat H (play R c p) t rho := by
  obtain ⟨x,y,dy,i,hd,hx,hy,ht⟩ := ht
  exact ⟨x,y,dy,i,hd,hx,hy,fun j hj => cell_play_mono (ht j hj) c p⟩

theorem threat_four {H : Nat} {R : Board 5} {t : Fin 5} {rho : Nat}
    (ht : Threat H R t rho) (hb : cellAtInt H R t.val rho = some .black) :
    HasFour H R .black := by
  obtain ⟨x,y,dy,i,hd,hx,hy,ht⟩ := ht
  have ha : HasFourDir H R .black x y 1 dy := by
    intro j
    by_cases hj : j = i
    · subst j
      rw [hx,hy]
      exact hb
    · exact ht j hj
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact Or.inr (Or.inl ⟨x,y,ha⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x,y,ha⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x,y,ha⟩))

theorem guard_not_white {H rho : Nat} {R : Board 5} {t : Fin 5} {Q : Fin 5 → Prop}
    {h0 : Fin 5 → Nat} (inv : Inv H t rho Q h0 R)
    (c : Fin 5) (x y : Int) (hc : Guard t rho Q h0 x y) :
    cellAtInt H (play R c .white) x y ≠ some .white := by
  rcases hc with ⟨q,hq,hc⟩ | ⟨hx,hy⟩
  · intro hw
    obtain ⟨hx, hlt, hodd⟩ := hc
    obtain ⟨c2, hx2, hy0, hyh, hst⟩ := cellAtInt_some hw
    have hc2 : c2 = q := Fin.ext (by omega)
    subst hc2
    have h1 : h0 c2 < y.toNat := by omega
    have h2 : (y.toNat - h0 c2) % 2 = 1 := by omega
    by_cases hcq : c2 = c
    · subst hcq
      rw [play_eq, stone_append] at hst
      by_cases h3 : y.toNat < (R c2).length
      · rw [if_pos h3, inv.alt _ hq _ h1 h3 h2] at hst; cases hst
      · rw [if_neg h3] at hst
        by_cases h4 : y.toNat = (R c2).length
        · have := inv.par _ hq
          omega
        · rw [if_neg h4] at hst; cases hst
    · rw [play_ne _ _ _ _ hcq] at hst
      rw [inv.alt _ hq _ h1 (stone_bound _ _ _ hst) h2] at hst; cases hst
  · intro hw
    obtain ⟨d, hx', hy0, _, hs⟩ := cellAtInt_some hw
    have hd : d = t := Fin.ext (by omega)
    subst d
    have hb := stone_bound _ _ _ hs
    rw [play_len] at hb
    have := inv.below
    split_ifs at hb <;> omega

theorem dead_play {H : Nat} {R : Board 5} {t : Fin 5} {rho : Nat}
    {Q : Fin 5 → Prop} {h0 : Fin 5 → Nat} {c : Fin 5} {r : Nat}
    (h : Dead H R t rho Q h0 c r) (e : Fin 5) (p : Player) :
    Dead H (play R e p) t rho Q h0 c r := by
  intro dy hdy i
  obtain ⟨j, hj⟩ := h dy hdy i
  exact ⟨j, hj.imp (fun hb => cell_play_mono hb e p) id⟩


theorem step {H rho : Nat} {R : Board 5} {t : Fin 5} {Q : Fin 5 → Prop}
    {h0 : Fin 5 → Nat} (inv : Inv H t rho Q h0 R)
    (c : Fin 5) (hl : Legal H R c) (e : Fin 5) (he : Legal H (play R c .white) e)
    (hcase : e = c ∨ ((R c).length + 1 = H ∧ c ≠ t ∧ ¬ Q c ∧ e ≠ t ∧ ¬ Q e))
    (hrt : h0 t < rho) (hro : (rho - h0 t) % 2 = 1)
    (hrH : rho < H)
    (hnb2 : ¬ HasFour H (play (play R c .white) e .black) .black) :
    Inv H t rho Q h0 (play (play R c .white) e .black) := by
  have hl' : (R c).length < H := hl
  have he' : (play R c .white e).length < H := he
  have l2 : ∀ d, (play (play R c .white) e .black d).length =
      (R d).length + (if d = c then 1 else 0) + (if d = e then 1 else 0) := by
    intro d; rw [play_len, play_len]
  have hnw1 := no_white hl inv.nw inv.nb (inv.ntr c hl) inv.dead (guard_not_white inv c)
  refine ⟨toMove_play_black (toMove_play_white inv.tm c) e,
    fun hf => hnw1 (hasFour_play_other (by decide) hf), hnb2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    have h1 := l2 d
    have h2 := inv.valid d
    have h3 := play_len R c e .white
    by_cases hdc : d = c <;> by_cases hde : d = e
    · subst hdc; subst hde; simp at h1 h3; omega
    · subst hdc; simp [hde] at h1; omega
    · subst hde; simp [hdc] at h1 h3; omega
    · simp [hdc, hde] at h1; omega

  · intro q hq
    have h1 := l2 q
    have := inv.ge q hq
    omega
  · intro q hq
    have h1 := l2 q
    have hp := inv.par q hq
    rcases hcase with hec | ⟨_, hct, hcQ, het, heQ⟩
    · subst e
      by_cases hqc : q = c
      · subst q; simp at h1; rw [h1]; omega
      · simp [hqc] at h1; rw [h1]; exact hp
    · have hqc : q ≠ c := fun h => by subst q; exact hq.elim hct hcQ
      have hqe : q ≠ e := fun h => by subst q; exact hq.elim het heQ
      simp [hqc,hqe] at h1
      omega
  · intro q hq r hr1 hr2 hr3
    by_cases hqe : q = e
    · have hec : e = c := by
        rcases hcase with h | ⟨_, _, _, het, heQ⟩
        · exact h
        · subst q
          exact (hq.elim het heQ).elim
      subst hqe; subst hec
      rw [play_eq, play_eq, stone_append, stone_append]
      simp only [List.length_append, List.length_cons, List.length_nil]
      have hp := inv.par q hq
      by_cases h1 : r < (R q).length
      · rw [if_pos (by omega), if_pos h1]; exact inv.alt q hq r hr1 h1 hr3
      · have h2 := l2 q
        simp at h2
        have : r = (R q).length + 1 := by omega
        rw [if_neg (by omega), if_pos this]
    · rw [play_ne _ _ _ _ hqe]
      by_cases hqc : q = c
      · subst hqc
        rcases hcase with hec | ⟨_, hqt, hqQ, _, _⟩
        · exact (hqe hec.symm).elim
        · exact (hq.elim hqt hqQ).elim
      · rw [play_ne _ _ _ _ hqc]
        rw [play_ne _ _ _ _ hqe, play_ne _ _ _ _ hqc] at hr2
        exact inv.alt q hq r hr1 hr2 hr3
  · have hb := inv.below
    have hp := inv.par t (Or.inl rfl)
    have hg := inv.ge t (Or.inl rfl)
    have h1 := l2 t
    rcases hcase with hec | ⟨_, hct, _, het, _⟩
    · subst e
      by_cases htc : t = c
      · subst c
        simp at h1
        by_contra hn
        have ht : rho = (R t).length + 1 := by omega
        apply hnb2
        apply threat_four (threat_play (threat_play inv.threat t .white) t .black)
        have h0r : 0 ≤ (rho : Int) := by omega
        have hh : (rho : Int) < H := by omega
        rw [cellAtInt_fin _ t _ h0r hh]
        simp only [Int.toNat_natCast]
        rw [play_eq, stone_append]
        have hlen : (play R t .white t).length = (R t).length + 1 := by simp [play_len]
        rw [hlen, if_neg (by omega), if_pos ht]
      · simp [htc] at h1
        omega
    · simp [Ne.symm hct, Ne.symm het] at h1
      omega
  · intro d hd ht
    change (play (play R c .white) e .black d).length < H at hd
    by_cases hde : d = e
    · subst hde
      obtain ⟨-, h1, -, -⟩ := ht
      rw [play_eq, stone_append] at h1
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel,
        lt_irrefl, if_false, if_true] at h1
      cases h1
    · have h1 := l2 d
      by_cases hdc : d = c
      · rcases hcase with h | ⟨hcap, _, _, _, _⟩
        · exact hde (hdc.trans h.symm)
        · simp [hdc] at h1; subst hdc; omega
      · unfold TopThree at ht
        rw [play_ne _ _ _ _ hde, play_ne _ _ _ _ hdc] at ht
        rw [play_ne _ _ _ _ hde, play_ne _ _ _ _ hdc] at hd
        exact inv.ntr d hd ht
  · exact threat_play (threat_play inv.threat c .white) e .black
  · intro d r hcell
    apply dead_play
    apply dead_play
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
        · rcases hcase with h | ⟨hcap, _, _, _, _⟩
          · exact absurd (hdc.trans h.symm) hde
          · obtain ⟨-, hlt, -⟩ := hP
            simp [hdc] at h1; subst hdc; omega
        · unfold PotExc at hP
          rw [play_ne _ _ _ _ hde, play_ne _ _ _ _ hdc] at hP
          exact Or.inr hP



theorem fallback {H rho : Nat} {R : Board 5} {t : Fin 5} {Q : Fin 5 → Prop}
    {h0 : Fin 5 → Nat} (inv : Inv H t rho Q h0 R)
    (hh : H % 2 = 0) (ht : h0 t % 2 = 1) (hq0 : ∀ d, Q d → h0 d % 2 = 0)
    (hrH : rho < H) (c : Fin 5) (hcap : (R c).length + 1 = H) :
    c ≠ t ∧ ¬ Q c ∧ ∃ e, e ≠ t ∧ ¬ Q e ∧ Legal H (play R c .white) e := by
  have hct : c ≠ t := by
    rintro rfl
    have := inv.below
    omega
  have hcQ : ¬ Q c := by
    intro hc
    have h := inv.par c (Or.inr hc)
    have := hq0 c hc
    omega
  refine ⟨hct,hcQ,?_⟩
  by_contra hhx
  let W := play R c .white
  have llen (d : Fin 5) : (W d).length = (R d).length + (if d = c then 1 else 0) :=
    play_len R c d .white
  have hW (d : Fin 5) : (W d).length ≤ H := by
    rw [llen]
    have := inv.valid d
    split_ifs with he
    · subst d; omega
    · omega
  have htp : (W t).length % 2 = 1 := by
    rw [llen, if_neg (Ne.symm hct), Nat.add_zero, inv.par t (Or.inl rfl)]
    exact ht
  have hdp (d : Fin 5) (hdt : d ≠ t) : (W d).length % 2 = 0 := by
    by_cases hdQ : Q d
    · have hdc : d ≠ c := fun h => hcQ (h ▸ hdQ)
      rw [llen, if_neg hdc, Nat.add_zero, inv.par d (Or.inr hdQ)]
      exact hq0 d hdQ
    · have hn : ¬ Legal H W d := fun he => hhx ⟨d,hdt,hdQ,he⟩
      change ¬ (W d).length < H at hn
      have := hW d
      omega
  have hodd : totalStones W % 2 = 1 := by
    simp only [totalStones, Fin.sum_univ_five]
    have htall : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by fin_cases t <;> decide
    rcases htall with rfl | rfl | rfl | rfl | rfl
    · have h1 := hdp 1 (by decide)
      have h2 := hdp 2 (by decide)
      have h3 := hdp 3 (by decide)
      have h4 := hdp 4 (by decide)
      omega
    · have h0 := hdp 0 (by decide)
      have h2 := hdp 2 (by decide)
      have h3 := hdp 3 (by decide)
      have h4 := hdp 4 (by decide)
      omega
    · have h0 := hdp 0 (by decide)
      have h1 := hdp 1 (by decide)
      have h3 := hdp 3 (by decide)
      have h4 := hdp 4 (by decide)
      omega
    · have h0 := hdp 0 (by decide)
      have h1 := hdp 1 (by decide)
      have h2 := hdp 2 (by decide)
      have h4 := hdp 4 (by decide)
      omega
    · have h0 := hdp 0 (by decide)
      have h1 := hdp 1 (by decide)
      have h2 := hdp 2 (by decide)
      have h3 := hdp 3 (by decide)
      omega
  dsimp [W] at hodd
  rw [totalStones_play] at hodd
  have := totalStones_odd_of_white inv.tm
  omega

theorem hyp_safe {H rho : Nat} {R : Board 5} {t : Fin 5} {Q : Fin 5 → Prop}
    (hy : Hyp H R t rho Q) (htm : toMove R = .white)
    (hnw : ¬ HasFour H R .white) (hnb : ¬ HasFour H R .black) :
    Safe H R := by
  let h0 := fun q => (R q).length
  have hrt : h0 t < rho := hy.target_gt
  have hro : (rho - h0 t) % 2 = 1 := hy.target_odd
  have ht : h0 t % 2 = 1 := by
    have hv := hy.valid t
    have ho := hy.odd
    have hh := hy.even
    dsimp [h0]
    omega
  have hq0 (q : Fin 5) (hq : Q q) : h0 q % 2 = 0 := by
    have hv := hy.valid q
    have hpar := hy.qpar q hq
    have hh := hy.even
    dsimp [h0]
    omega
  have root : Inv H t rho Q h0 R :=
    ⟨htm,hnw,hnb,hy.valid,fun _ _ => le_rfl,fun _ _ => rfl,
      fun _ _ _ hlt hgt _ => (Nat.not_lt_of_ge (Nat.le_of_lt hlt) hgt).elim,
      hrt,hy.ntr,hy.threat,hy.dead⟩
  refine safe_of_inv2 (Inv H t rho Q h0) (fun R inv => ⟨inv.tm, inv.nw⟩) ?_ R root
  intro S inv c hl
  refine ⟨no_white hl inv.nw inv.nb (inv.ntr c hl) inv.dead (guard_not_white inv c), Or.inr ?_⟩
  have hl' : (S c).length < H := hl
  have reply (e : Fin 5) (he : Legal H (play S c .white) e)
      (hec : e = c ∨ ((S c).length + 1 = H ∧ c ≠ t ∧ ¬ Q c ∧ e ≠ t ∧ ¬ Q e)) :
      HasFour H (play (play S c .white) e .black) .black ∨
        Inv H t rho Q h0 (play (play S c .white) e .black) := by
    by_cases h : HasFour H (play (play S c .white) e .black) .black
    · exact Or.inl h
    · exact Or.inr (step inv c hl e he hec hrt hro hy.target_lt h)
  by_cases h : (S c).length + 1 < H
  · have he : Legal H (play S c .white) c := by
      change (play S c .white c).length < H
      rw [play_len]; simpa using h
    exact ⟨c,he,reply c he (Or.inl rfl)⟩
  · have hcap : (S c).length + 1 = H := by omega
    obtain ⟨hct,hcQ,e,het,heQ,he⟩ := fallback inv hy.even ht hq0 hy.target_lt c hcap
    exact ⟨e,he,reply e he (Or.inr ⟨hcap,hct,hcQ,het,heQ⟩)⟩

#print axioms hyp_safe
end C4W5.LongThreat
