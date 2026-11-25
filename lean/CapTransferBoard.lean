import CapTransferDefs

/-!
Source-only formal proof core. This separate draft was not run through Lean.
The final controller theorem isolates the exact one remaining cap-certificate
obligation as an explicit premise, not an axiom or a claimed theorem.
-/
namespace C4W5.CapTransfer
open Connect4 (Player opponent)
open Connect4.NarrowBoards
set_option linter.deprecated false

def pair (R : Board 5) (c e : Fin 5) : Board 5 :=
  play (play R c .white) e .black

/-- White cover or cap is enough for exceptional-cell backward propagation,
    regardless of which available column is used for the cap reply. -/
theorem exceptions_pair {H : Nat} {R : Board 5} {c e d : Fin 5} {r : Nat}
    (hl : Legal H R c)
    (hcase : e = c ∨ (R c).length + 1 = H)
    (hcell : Exceptional (pair R c e) d r ∨ PotExc H (pair R c e) d r) :
    Exceptional R d r ∨ PotExc H R d r := by
  rcases hcell with hE | hP
  · rcases exceptional_play hE with h | ⟨-, -, hp, -⟩
    · rcases exceptional_play h with h' | ⟨rfl, hr, -, htop⟩
      · exact Or.inl h'
      · exact Or.inr ⟨hr, hl, htop⟩
    · cases hp
  · by_cases hde : d = e
    · subst d
      exact absurd hP not_exc_top_black
    · by_cases hdc : d = c
      · subst d
        rcases hcase with h | hcap
        · exact (hde h.symm).elim
        · have hh := hP.2.1
          change (play (play R c .white) e .black c).length < H at hh
          rw [play_ne _ _ _ _ hde, play_len] at hh
          simp at hh
          omega
      · unfold PotExc pair at hP
        rw [play_ne _ _ _ _ hde, play_ne _ _ _ _ hdc] at hP
        exact Or.inr hP

theorem postDead_mono {H : Nat} {R : Board 5} {t s c : Fin 5} {a b r : Nat}
    {Q : Fin 5 → Prop} {h0 : Fin 5 → Nat}
    (hy : PostDead H R t s a b Q h0 c r) (e : Fin 5) (p : Player) :
    PostDead H (play R e p) t s a b Q h0 c r := by
  intro dy hdy i
  obtain ⟨j, hj⟩ := hy dy hdy i
  exact ⟨j, hj.imp (fun hb => cell_play_mono hb e p) id⟩

theorem phaseA_step {H : Nat} {R : Board 5} {t s c e : Fin 5} {a b : Nat}
    {Q : Fin 5 → Prop} {h0 : Fin 5 → Nat}
    (inv : BeforeCap H R t s a b Q h0)
    (hl : Legal H R c) (he : Legal H (play R c .white) e)
    (hcase : e = c ∨ ((R c).length + 1 = H ∧
      c ≠ s ∧ ¬ protect t Q c ∧ e ≠ s ∧ ¬ protect t Q e))
    (ha : h0 s < a) (hao : (a - h0 s) % 2 = 1) (haH : a < H)
    (hn : ¬ HasFour H (pair R c e) .black) :
    BeforeCap H (pair R c e) t s a b Q h0 := by
  refine ⟨LongThreat.step inv.inv c hl e he hcase ha hao haH hn, ?_, ?_⟩
  · exact LongThreat.threat_play (LongThreat.threat_play inv.threatB c .white) e .black
  · intro d r h
    exact postDead_mono (postDead_mono
      (inv.deadB d r (exceptions_pair hl (hcase.imp id And.left) h)) c .white) e .black

/-- The single odd protected column is t, not the target column s.
    One uses the pre-cap column height parities and no geometry in this lemma. -/
theorem outside_after_cap {H : Nat} {R : Board 5} {t s c : Fin 5} {a b : Nat}
    {Q : Fin 5 → Prop} {h0 : Fin 5 → Nat}
    (cur : BeforeCap H R t s a b Q h0)
    (hh : H % 2 = 0) (hot : h0 t % 2 = 1) (hes : h0 s % 2 = 0)
    (hQ : ∀ q, Q q → h0 q % 2 = 0)
    (haH : a < H) (hneq : c ≠ t) (hcap : (R c).length + 1 = H) :
    c ≠ s ∧ ¬ protect t Q c ∧ ∃ e, e ≠ s ∧ ¬ protect t Q e ∧ Legal H (play R c .white) e := by
  have hcs : c ≠ s := by
    intro hc
    subst c
    have hb := cur.inv.below
    omega
  have hcQ : ¬ Q c := by
    intro he
    have h := cur.inv.par c (Or.inr (Or.inr he))
    have h' := hQ c he
    omega
  refine ⟨hcs, fun hc => hc.elim hneq hcQ, ?_⟩
  by_contra hhx
  let V := play R c .white
  have hlen (d : Fin 5) : (V d).length = (R d).length + (if d = c then 1 else 0) :=
    play_len R c d .white
  have hV (d : Fin 5) : (V d).length ≤ H := by
    rw [hlen]; have h := cur.inv.valid d
    split_ifs with he
    · subst d; omega
    · omega
  have htp : (V t).length % 2 = 1 := by
    rw [hlen, if_neg (Ne.symm hneq), Nat.add_zero, cur.inv.par t (Or.inr (Or.inl rfl))]
    exact hot
  have ev (d : Fin 5) (hdt : d ≠ t) : (V d).length % 2 = 0 := by
    by_cases hds : d = s
    · subst d
      rw [hlen, if_neg (Ne.symm hcs), Nat.add_zero, cur.inv.par s (Or.inl rfl)]
      exact hes
    · by_cases hdQ : Q d
      · have hdc : d ≠ c := fun hc => hcQ (hc ▸ hdQ)
        rw [hlen, if_neg hdc, Nat.add_zero, cur.inv.par d (Or.inr (Or.inr hdQ))]
        exact hQ d hdQ
      · have hn : ¬ Legal H V d := fun hd => hhx ⟨d,hds,fun h => h.elim hdt hdQ,hd⟩
        change ¬ (V d).length < H at hn
        have hd := hV d
        omega
  have ho : totalStones V % 2 = 1 := by
    simp only [totalStones, Fin.sum_univ_five]
    have hs : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by fin_cases t <;> decide
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · have h1 := ev 1 (by decide)
      have h2 := ev 2 (by decide)
      have h3 := ev 3 (by decide)
      have h4 := ev 4 (by decide)
      omega
    · have h0 := ev 0 (by decide)
      have h2 := ev 2 (by decide)
      have h3 := ev 3 (by decide)
      have h4 := ev 4 (by decide)
      omega
    · have h0 := ev 0 (by decide)
      have h1 := ev 1 (by decide)
      have h3 := ev 3 (by decide)
      have h4 := ev 4 (by decide)
      omega
    · have h0 := ev 0 (by decide)
      have h1 := ev 1 (by decide)
      have h2 := ev 2 (by decide)
      have h4 := ev 4 (by decide)
      omega
    · have h0 := ev 0 (by decide)
      have h1 := ev 1 (by decide)
      have h2 := ev 2 (by decide)
      have h3 := ev 3 (by decide)
      omega
  dsimp [V] at ho
  rw [totalStones_play] at ho
  have := totalStones_odd_of_white cur.inv.tm
  omega

/-- Exact certificate to be supplied at the one parity-changing move.
    No hypotheses of a running second controller are required. -/
def TransferPost (H : Nat) (t s : Fin 5) (a b : Nat)
    (Q : Fin 5 → Prop) (h0 : Fin 5 → Nat) : Prop :=
  ∀ R, BeforeCap H R t s a b Q h0 → (R t).length + 1 = H →
    ¬ HasFour H (pair R t s) .black → LongThreat.Hyp H (pair R t s) s b Q

theorem hyp_safe_of_transfer {H : Nat} {A : Board 5} {t s : Fin 5} {a b : Nat}
    {Q : Fin 5 → Prop} (hy : Hyp H A t s a b Q)
    (checkedSwitch : TransferPost H t s a b Q (fun d => (A d).length))
    (htm : toMove A = .white) (hnw : ¬ HasFour H A .white) (hnb : ¬ HasFour H A .black) :
    Safe H A := by
  let h0 := fun q => (A q).length
  have haH : a < H := Nat.lt_trans hy.order hy.below
  have init : BeforeCap H A t s a b Q h0 :=
    ⟨⟨htm,hnw,hnb,hy.valid,fun _ _ => le_rfl,fun _ _ => rfl,
        fun _ _ _ hlt hgt _ => (Nat.not_lt_of_ge (Nat.le_of_lt hlt) hgt).elim,
        hy.above,hy.noTriple,hy.threatA,hy.deadA⟩,hy.threatB,hy.deadB⟩
  refine safe_of_inv2L (fun R => BeforeCap H R t s a b Q h0)
    (fun _ h => ⟨h.inv.tm,h.inv.nw⟩) ?_ A init
  intro R cur c hl
  have hNW := LongThreat.no_white hl cur.inv.nw cur.inv.nb (cur.inv.ntr c hl) cur.inv.dead
    (LongThreat.guard_not_white cur.inv c)
  refine ⟨hNW, Or.inr ?_⟩
  have hh : (R c).length < H := hl
  have next (e : Fin 5) (he : Legal H (play R c .white) e)
      (hj : e = c ∨ ((R c).length + 1 = H ∧
        c ≠ s ∧ ¬ protect t Q c ∧ e ≠ s ∧ ¬ protect t Q e)) :
      HasFour H (pair R c e) .black ∨ BeforeCap H (pair R c e) t s a b Q h0 ∨
        Safe H (pair R c e) := by
    by_cases hb : HasFour H (pair R c e) .black
    · exact Or.inl hb
    · exact Or.inr (Or.inl (phaseA_step cur hl he hj hy.above hy.oddA haH hb))
  by_cases hf : (R c).length + 1 < H
  · have he : Legal H (play R c .white) c := by
      change (play R c .white c).length < H
      rw [play_len]; simpa using hf
    exact ⟨c,he,next c he (Or.inl rfl)⟩
  have hcap : (R c).length + 1 = H := by omega
  by_cases hc : c = t
  · subst c
    have he : Legal H (play R t .white) s := by
      change (play R t .white s).length < H
      rw [play_ne _ _ _ _ hy.distinct]
      exact Nat.lt_trans cur.inv.below haH
    refine ⟨s,he,?_⟩
    by_cases hb : HasFour H (pair R t s) .black
    · exact Or.inl hb
    · apply Or.inr; apply Or.inr
      exact LongThreat.hyp_safe (checkedSwitch R cur hcap hb)
        (toMove_play_black (toMove_play_white cur.inv.tm t) s)
        (fun hx => hNW (hasFour_play_other (by decide) hx)) hb
  · obtain ⟨hcS,hcQ,e,heS,heQ,he⟩ :=
      outside_after_cap cur hy.even hy.oddT hy.evenS hy.evenQ haH hc hcap
    exact ⟨e,he,next e he (Or.inr ⟨hcap,hcS,hcQ,heS,heQ⟩)⟩

end C4W5.CapTransfer
