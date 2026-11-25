import C4W5.Theory.StretchZone
import C4W5.Cert.StretchTree
import C4W5.Cert.ZoneC

/-!
# Kernel-checkable certificates for the zone game modulo stretching (with claim-criterion leaves)

States are `(k, p, l)`: zone height, compact position, labels.  Mirrors `gen/szgen.cpp`.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

/-! ## Lifting along a contraction -/

theorem sblackWin_lift {D k' k : Nat} {A' A : Board 5} {ℓ : Fin 5 → Lab} (hD : 2 ≤ D)
    (s : SEq D k' A' k A) (h : SBlackWin D k' A' ℓ) : SBlackWin D k A ℓ := by
  obtain ⟨e, hl, hlen, hall⟩ := h
  refine ⟨e, hl, (s.legal_iff e).mp hlen, fun k₂ A₂ hv => ?_⟩
  obtain ⟨k₂', B₂, hv', s2⟩ := variant_lift s hv
  exact (s2.hasFour_iff hD _).mp (hall k₂' B₂ hv')

theorem jl_lift {D : Nat} {J : Nat → Board 5 → (Fin 5 → Lab) → Prop} {k' k : Nat} {A' A : Board 5}
    {ℓ : Fin 5 → Lab} (s : SEq D k' A' k A) (h : JL D J k' A' ℓ) : JL D J k A ℓ := by
  obtain ⟨k₃, A₃, hm, s3⟩ := h
  exact ⟨k₃, A₃, hm, s3.trans s⟩

theorem sblackOut_lift {D : Nat} {J : Nat → Board 5 → (Fin 5 → Lab) → Prop} {k' k : Nat}
    {A' A : Board 5} {ℓ : Fin 5 → Lab} {e : Fin 5} (hD : 2 ≤ D) (s : SEq D k' A' k A)
    (hv : Valid k A) (h : SBlackOut D J k' A' ℓ e) : SBlackOut D J k A ℓ e := by
  rcases h with ⟨hl, hlen, hall⟩ | ⟨hl, hlen, hj⟩ | ⟨hl, hj⟩
  · refine Or.inl ⟨hl, (s.legal_iff e).mp hlen, fun k₂ A₂ hvar => ?_⟩
    obtain ⟨k₂', B₂, hv', s2⟩ := variant_lift s hvar
    rcases hall k₂' B₂ hv' with hf | hj
    · exact Or.inl ((s2.hasFour_iff hD _).mp hf)
    · exact Or.inr (jl_lift s2 hj)
  · refine Or.inr (Or.inl ⟨hl, ?_, jl_lift s hj⟩)
    have h1 : ¬ (A e).length < k := fun h => by
      have : (A' e).length < k' := (s.legal_iff e).mpr h
      omega
    have := hv e
    omega
  · exact Or.inr (Or.inr ⟨hl, jl_lift s hj⟩)

/-! ## The checker -/

/-- Target check for a state reached without a board move. -/
def szTarget (memf : Nat → Pos → Lab5 → Bool) (k : Nat) (p : Pos) (l : Lab5) : Bool :=
  memf k p l || claimB k p

/-- Black's low move `e` in all variants: a four, or a member / leaf after contraction. -/
def szBlackLow (D : Nat) (memf : Nat → Pos → Lab5 → Bool) (k : Nat) (p : Pos) (l : Lab5) (e : Nat) :
    Bool :=
  (varsF D k p e .black).all fun v =>
    forceP v.2 fun p₂ => p₂.hasFourQ .black ||
      (withNorm D v.1 p₂ e fun k₃ p₃ => memf k₃ p₃ l || claimB k₃ p₃)

def szWinLow (D k : Nat) (p : Pos) (e : Nat) : Bool :=
  (varsF D k p e .black).all fun v => forceP v.2 fun p₂ => p₂.hasFourQ .black

def szOut (D : Nat) (memf : Nat → Pos → Lab5 → Bool) (k : Nat) (p : Pos) (l : Lab5) (e : Nat) : Bool :=
  force (l.get e) fun le =>
  if le = 0 then
    (if p.ht e < k then szBlackLow D memf k p l e else szTarget memf k p (l.set e 1))
  else if le = 1 then szTarget memf k p (l.set e 2) else false

def szWin (D k : Nat) (p : Pos) (l : Lab5) (e : Nat) : Bool :=
  if l.get e = 0 then (if p.ht e < k then szWinLow D k p e else false) else false

/-- One variant of White's low move in column `c`; `free`: Black need not cover. -/
def szCheckV (D : Nat) (memf : Nat → Pos → Lab5 → Bool) (l : Lab5) (free : Bool) (c e : Nat)
    (v : Nat × Pos) : Bool :=
  forceP v.2 fun p₁ =>
    !p₁.hasFourQ .white &&
    (withNorm D v.1 p₁ c fun k₁ n₁ =>
      szWin D k₁ n₁ l e || ((e == c || free) && szOut D memf k₁ n₁ l e))

def szCol (D : Nat) (memf : Nat → Pos → Lab5 → Bool) (k : Nat) (p : Pos) (l : Lab5) (rep c : Nat) :
    Bool :=
  force (l.get c) fun lc =>
  if lc = 0 then
    (if p.ht c < k then
      force (p.LM k) fun lm =>
        szCheckV D memf l (Nat.ble (p.ht c + 5) k) c (replyOf rep (2 * c)) (k, p.push c .white) &&
        (if clearM D k lm (p.ht c + D + 1) && !clearM D k lm (p.ht c + D + 2) then
          szCheckV D memf l (Nat.ble (p.ht c + 5) k) c (replyOf rep (2 * c + 1))
            (k + 2, (stretchPos p (p.ht c + D + 1)).push c .white)
        else true)
    else szTarget memf k p (l.set c 2))
  else if lc = 1 then
    ((l.set c 2).allDead ||
      (force (replyOf rep (2 * c)) fun e =>
        szWin D k p (l.set c 2) e || szOut D memf k p (l.set c 2) e))
  else true

def stepOKSZ (D : Nat) (memf : Nat → Pos → Lab5 → Bool) (k : Nat) (p : Pos) (l : Lab5) (rep : Nat) :
    Bool :=
  p.wfB k && szCol D memf k p l rep 0 && szCol D memf k p l rep 1 && szCol D memf k p l rep 2 &&
  szCol D memf k p l rep 3 && szCol D memf k p l rep 4

/-! ## Soundness -/

section
variable {D : Nat} {J : Nat → Board 5 → (Fin 5 → Lab) → Prop} {memf : Nat → Pos → Lab5 → Bool}

theorem szTarget_sound (hm : ∀ k q l, memf k q l = true → J k q.toBoard l.fn) {k : Nat} {p : Pos}
    {l : Lab5} (h : szTarget memf k p l = true) : JL D J k p.toBoard l.fn := by
  unfold szTarget at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact ⟨k, _, Or.inl (hm _ _ _ h), SEq.refl _ _⟩
  · exact ⟨k, _, Or.inr (claimB_sound h), SEq.refl _ _⟩

theorem szBlackLow_sound (hm : ∀ k q l, memf k q l = true → J k q.toBoard l.fn) {k : Nat} {p : Pos}
    (hw : p.WF k) {l : Lab5} (e : Fin 5) (hlt : p.ht e.val < k)
    (hb : szBlackLow D memf k p l e.val = true) :
    ∀ k₂ A₂, Variant D k p.toBoard e .black k₂ A₂ → HasFour k₂ A₂ .black ∨ JL D J k₂ A₂ l.fn := by
  unfold szBlackLow at hb
  simp only [List.all_eq_true, forceP_eq, withNorm_eq, Bool.or_eq_true] at hb
  intro k₂ A₂ hv
  obtain ⟨v, hmem, rfl, rfl, hwv⟩ := vars_complete hw e .black hlt hv
  rcases hb v hmem with hwin | hin
  · left
    rw [Pos.hasFourQ_eq] at hwin
    exact (hasFourF_iff hwv _).mp hwin
  · right
    obtain ⟨-, hs⟩ := normAt_sound (D := D) hwv e.val
    rcases hin with hin | hin
    · exact ⟨_, _, Or.inl (hm _ _ _ hin), hs⟩
    · exact ⟨_, _, Or.inr (claimB_sound hin), hs⟩

theorem szWinLow_sound {k : Nat} {p : Pos} (hw : p.WF k) (e : Fin 5) (hlt : p.ht e.val < k)
    (hb : szWinLow D k p e.val = true) :
    ∀ k₂ A₂, Variant D k p.toBoard e .black k₂ A₂ → HasFour k₂ A₂ .black := by
  unfold szWinLow at hb
  simp only [List.all_eq_true, forceP_eq] at hb
  intro k₂ A₂ hv
  obtain ⟨v, hmem, rfl, rfl, hwv⟩ := vars_complete hw e .black hlt hv
  have := hb v hmem
  rw [Pos.hasFourQ_eq] at this
  exact (hasFourF_iff hwv _).mp this

theorem szOut_sound (hm : ∀ k q l, memf k q l = true → J k q.toBoard l.fn) {k : Nat} {p : Pos}
    (hw : p.WF k) {l : Lab5} {e : Fin 5} (h : szOut D memf k p l e.val = true) :
    SBlackOut D J k p.toBoard l.fn e := by
  unfold szOut at h
  rw [force_eq] at h
  have hht := (hw e.val).2
  by_cases h0 : l.get e.val = 0
  · rw [if_pos h0] at h
    have hl : l.fn e = .low := by simp [Lab5.fn, natLab, h0]
    by_cases hlt : p.ht e.val < k
    · rw [if_pos hlt] at h
      exact Or.inl ⟨hl, by rw [Pos.height]; exact hlt, szBlackLow_sound hm hw e hlt h⟩
    · rw [if_neg hlt] at h
      have := szTarget_sound (D := D) hm h
      rw [Lab5.fn_set] at this
      exact Or.inr (Or.inl ⟨hl, by rw [Pos.height]; omega, this⟩)
  · rw [if_neg h0] at h
    by_cases h1 : l.get e.val = 1
    · rw [if_pos h1] at h
      have hl : l.fn e = .odd := by simp [Lab5.fn, natLab, h1]
      have := szTarget_sound (D := D) hm h
      rw [Lab5.fn_set] at this
      exact Or.inr (Or.inr ⟨hl, this⟩)
    · rw [if_neg h1] at h; exact Bool.noConfusion h

theorem szWin_sound {k : Nat} {p : Pos} (hw : p.WF k) {l : Lab5} {e : Fin 5}
    (h : szWin D k p l e.val = true) : SBlackWin D k p.toBoard l.fn := by
  unfold szWin at h
  by_cases h0 : l.get e.val = 0
  · rw [if_pos h0] at h
    by_cases hlt : p.ht e.val < k
    · rw [if_pos hlt] at h
      exact ⟨e, by simp [Lab5.fn, natLab, h0], by rw [Pos.height]; exact hlt, szWinLow_sound hw e hlt h⟩
    · rw [if_neg hlt] at h; exact Bool.noConfusion h
  · rw [if_neg h0] at h; exact Bool.noConfusion h

theorem WF_valid {k : Nat} {p : Pos} (hw : p.WF k) : Valid k p.toBoard := by
  intro c; rw [Pos.height]; exact (hw c.val).2

theorem szCheckV_sound (hD : 2 ≤ D) (hm : ∀ k q l, memf k q l = true → J k q.toBoard l.fn)
    {l : Lab5} {free : Bool} (c e : Fin 5) {v : Nat × Pos} (hwv : v.2.WF v.1)
    (hc : szCheckV D memf l free c.val e.val v = true) :
    ¬ HasFour v.1 v.2.toBoard .white ∧
    (SBlackWin D v.1 v.2.toBoard l.fn ∨
      ((e = c ∨ free = true) ∧ SBlackOut D J v.1 v.2.toBoard l.fn e)) := by
  unfold szCheckV at hc
  simp only [forceP_eq, withNorm_eq, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true,
    Pos.hasFourQ_eq, beq_iff_eq] at hc
  obtain ⟨hnf, hrest⟩ := hc
  obtain ⟨hwn, hs⟩ := normAt_sound (D := D) hwv c.val
  refine ⟨?_, ?_⟩
  · intro hf
    rw [← hasFourF_iff hwv, hnf] at hf; exact Bool.noConfusion hf
  · rcases hrest with hwin | ⟨hcond, hout⟩
    · exact Or.inl (sblackWin_lift hD hs (szWin_sound hwn hwin))
    · refine Or.inr ⟨?_, sblackOut_lift hD hs (WF_valid hwv) (szOut_sound hm hwn hout)⟩
      rcases hcond with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr h

theorem szCol_sound (hD : 2 ≤ D) (hm : ∀ k q l, memf k q l = true → J k q.toBoard l.fn) {k : Nat}
    {p : Pos} (hw : p.WF k) {l : Lab5} {rep : Nat} (c : Fin 5)
    (hok : szCol D memf k p l rep c.val = true) :
    (l.fn c = .low → (p.toBoard c).length < k → ∀ k₁ A₁, Variant D k p.toBoard c .white k₁ A₁ →
      ¬ HasFour k₁ A₁ .white ∧
      (SBlackWin D k₁ A₁ l.fn ∨
        ∃ e, (e = c ∨ (p.toBoard c).length + 5 ≤ k) ∧ SBlackOut D J k₁ A₁ l.fn e)) ∧
    (l.fn c = .low → (p.toBoard c).length = k → JL D J k p.toBoard (Function.update l.fn c .dead)) ∧
    (l.fn c = .odd → (∀ d, Function.update l.fn c .dead d = .dead) ∨
      SBlackWin D k p.toBoard (Function.update l.fn c .dead) ∨
      ∃ e, SBlackOut D J k p.toBoard (Function.update l.fn c .dead) e) := by
  unfold szCol at hok
  rw [force_eq] at hok
  have hfn : l.fn c = natLab (l.get c.val) := rfl
  have hset : (l.set c.val 2).fn = Function.update l.fn c .dead := by
    rw [Lab5.fn_set]; rfl
  by_cases h0 : l.get c.val = 0
  · rw [if_pos h0] at hok
    have hlow : l.fn c = .low := by rw [hfn, h0]; rfl
    refine ⟨?_, ?_, ?_⟩
    · intro _ hlen k₁ A₁ hv
      rw [Pos.height] at hlen ⊢
      rw [if_pos hlen, force_eq, Bool.and_eq_true] at hok
      obtain ⟨hok0, hok1⟩ := hok
      obtain ⟨v, hmem, rfl, rfl, hwv⟩ := vars_complete hw c .white hlen hv
      unfold varsF at hmem
      rw [force_eq] at hmem
      have key : ∃ e : Fin 5, szCheckV D memf l (Nat.ble (p.ht c.val + 5) k) c.val e.val v = true := by
        by_cases hcrit : (clearM D k (p.LM k) (p.ht c.val + D + 1) &&
            !clearM D k (p.LM k) (p.ht c.val + D + 2)) = true
        · rw [if_pos hcrit] at hmem hok1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl
          · exact ⟨⟨replyOf rep (2 * c.val), Nat.mod_lt _ (by decide)⟩, hok0⟩
          · exact ⟨⟨replyOf rep (2 * c.val + 1), Nat.mod_lt _ (by decide)⟩, hok1⟩
        · rw [if_neg hcrit] at hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          subst hmem
          exact ⟨⟨replyOf rep (2 * c.val), Nat.mod_lt _ (by decide)⟩, hok0⟩
      obtain ⟨e, he⟩ := key
      obtain ⟨hnf, hrest⟩ := szCheckV_sound hD hm c e hwv he
      refine ⟨hnf, ?_⟩
      rcases hrest with hwin | ⟨hcond, hout⟩
      · exact Or.inl hwin
      · refine Or.inr ⟨e, ?_, hout⟩
        rcases hcond with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [Nat.ble_eq] at h; exact h)
    · intro _ hlen
      rw [Pos.height] at hlen
      rw [if_neg (by omega)] at hok
      have := szTarget_sound (D := D) hm hok
      rw [hset] at this
      exact this
    · intro hodd; exact absurd (hlow.symm.trans hodd) (by decide)
  · rw [if_neg h0] at hok
    by_cases h1 : l.get c.val = 1
    · rw [if_pos h1] at hok
      have hodd : l.fn c = .odd := by rw [hfn, h1]; rfl
      refine ⟨fun hl => absurd (hodd.symm.trans hl) (by decide),
        fun hl => absurd (hodd.symm.trans hl) (by decide), ?_⟩
      intro _
      rw [Bool.or_eq_true, force_eq, Bool.or_eq_true] at hok
      rcases hok with hall | hwin | hout
      · left; intro d; rw [← hset]; exact Lab5.allDead_sound hall d
      · right; left
        have := szWin_sound (D := D) hw (e := ⟨replyOf rep (2 * c.val), Nat.mod_lt _ (by decide)⟩) hwin
        rw [hset] at this; exact this
      · right; right
        have := szOut_sound (D := D) hm hw (e := ⟨replyOf rep (2 * c.val), Nat.mod_lt _ (by decide)⟩) hout
        rw [hset] at this
        exact ⟨_, this⟩
    · have hdead : l.fn c = .dead := by
        rw [hfn]; unfold natLab; rw [if_neg h0, if_neg h1]
      exact ⟨fun hl => absurd (hdead.symm.trans hl) (by decide),
        fun hl => absurd (hdead.symm.trans hl) (by decide),
        fun hl => absurd (hdead.symm.trans hl) (by decide)⟩

theorem stepOKSZ_sound (hD : 2 ≤ D) (hm : ∀ k q l, memf k q l = true → J k q.toBoard l.fn) {k : Nat}
    {p : Pos} {l : Lab5} {rep : Nat} (hok : stepOKSZ D memf k p l rep = true) :
    Valid k p.toBoard ∧ ∀ c : Fin 5,
    (l.fn c = .low → (p.toBoard c).length < k → ∀ k₁ A₁, Variant D k p.toBoard c .white k₁ A₁ →
      ¬ HasFour k₁ A₁ .white ∧
      (SBlackWin D k₁ A₁ l.fn ∨
        ∃ e, (e = c ∨ (p.toBoard c).length + 5 ≤ k) ∧ SBlackOut D J k₁ A₁ l.fn e)) ∧
    (l.fn c = .low → (p.toBoard c).length = k → JL D J k p.toBoard (Function.update l.fn c .dead)) ∧
    (l.fn c = .odd → (∀ d, Function.update l.fn c .dead d = .dead) ∨
      SBlackWin D k p.toBoard (Function.update l.fn c .dead) ∨
      ∃ e, SBlackOut D J k p.toBoard (Function.update l.fn c .dead) e) := by
  unfold stepOKSZ at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨hwf, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  have hw := Pos.wfB_sound hwf
  refine ⟨WF_valid hw, fun c => ?_⟩
  have : szCol D memf k p l rep c.val = true := by
    obtain rfl | rfl | rfl | rfl | rfl := fin5c c
    exacts [h0, h1, h2, h3, h4]
  exact szCol_sound hD hm hw c this

end

end C4W5
