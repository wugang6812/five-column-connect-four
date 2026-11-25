import LongThreatZone
import C4W5.Theory.StretchZone

/-! Extension of the accepted StretchZone simulation by one certified real-tail disjunct. -/

namespace C4W5.LongThreat.SZ
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

/-- Membership up to stretching, or a claim-criterion leaf. -/
def JL (D : Nat) (J : Nat → Board 5 → (Fin 5 → Lab) → Prop) (k : Nat) (A : Board 5)
    (ℓ : Fin 5 → Lab) : Prop :=
  ∃ k₃ A₃, (J k₃ A₃ ℓ ∨ (∃ q, ClaimHyp k₃ A₃ q) ∨ ZHyp k₃ A₃) ∧ SEq D k₃ A₃ k A

def SBlackWin (D k : Nat) (A : Board 5) (ℓ : Fin 5 → Lab) : Prop :=
  ∃ e, ℓ e = .low ∧ (A e).length < k ∧ ∀ k₂ A₂, Variant D k A e .black k₂ A₂ → HasFour k₂ A₂ .black

def SBlackOut (D : Nat) (J : Nat → Board 5 → (Fin 5 → Lab) → Prop) (k : Nat) (A : Board 5)
    (ℓ : Fin 5 → Lab) (e : Fin 5) : Prop :=
  (ℓ e = .low ∧ (A e).length < k ∧
    ∀ k₂ A₂, Variant D k A e .black k₂ A₂ → HasFour k₂ A₂ .black ∨ JL D J k₂ A₂ ℓ) ∨
  (ℓ e = .low ∧ (A e).length = k ∧ JL D J k A (Function.update ℓ e .odd)) ∨
  (ℓ e = .odd ∧ JL D J k A (Function.update ℓ e .dead))

def SZCert (D : Nat) (J : Nat → Board 5 → (Fin 5 → Lab) → Prop) : Prop :=
  ∀ k A ℓ, J k A ℓ → Valid k A ∧ ∀ c : Fin 5,
    (ℓ c = .low → (A c).length < k → ∀ k₁ A₁, Variant D k A c .white k₁ A₁ →
      ¬ HasFour k₁ A₁ .white ∧
      (SBlackWin D k₁ A₁ ℓ ∨ ∃ e, (e = c ∨ (A c).length + 5 ≤ k) ∧ SBlackOut D J k₁ A₁ ℓ e)) ∧
    (ℓ c = .low → (A c).length = k → JL D J k A (Function.update ℓ c .dead)) ∧
    (ℓ c = .odd → (∀ d, Function.update ℓ c .dead d = .dead) ∨
      SBlackWin D k A (Function.update ℓ c .dead) ∨ ∃ e, SBlackOut D J k A (Function.update ℓ c .dead) e)

/-- The real states at zone height `K`. -/
def IK (D : Nat) (J : Nat → Board 5 → (Fin 5 → Lab) → Prop) (K : Nat) (L : Board 5)
    (ℓ : Fin 5 → Lab) : Prop :=
  ∃ k A, J k A ℓ ∧ SEq D k A K L

/-- Target set of the real zone game: members or leaves. -/
def IKL (D : Nat) (J : Nat → Board 5 → (Fin 5 → Lab) → Prop) (K : Nat) (L : Board 5)
    (ℓ : Fin 5 → Lab) : Prop :=
  IK D J K L ℓ ∨ (∃ q, ClaimHyp K L q) ∨ ZHyp K L

theorem jl_real {D : Nat} (hD : 2 ≤ D) {J : Nat → Board 5 → (Fin 5 → Lab) → Prop} {k K : Nat}
    {A L : Board 5} {ℓ : Fin 5 → Lab} (h : JL D J k A ℓ) (s : SEq D k A K L) : IKL D J K L ℓ := by
  obtain ⟨k₃, A₃, hm | (⟨q, hy⟩ | hz), s3⟩ := h
  · exact Or.inl ⟨k₃, A₃, hm, s3.trans s⟩
  · exact Or.inr (Or.inl ⟨q, claimHyp_seq hD (s3.trans s) hy⟩)
  · exact Or.inr (Or.inr (zhyp_seq hD (s3.trans s) hz))

theorem sblackWin_real {D : Nat} (hD : 2 ≤ D) {k K : Nat} {A L : Board 5} {ℓ : Fin 5 → Lab}
    (s : SEq D k A K L) (h : SBlackWin D k A ℓ) : BlackWin K L ℓ := by
  obtain ⟨e, hl, hlen, hall⟩ := h
  have hleg : (L e).length < K := (s.legal_iff e).mp hlen
  obtain ⟨k₂, A₂, hv, s2⟩ := exists_variant s e .black
  exact ⟨e, hl, hleg, (s2.hasFour_iff hD _).mp (hall k₂ A₂ hv)⟩

theorem sblackOut_real {D : Nat} (hD : 2 ≤ D) {J : Nat → Board 5 → (Fin 5 → Lab) → Prop}
    {k K : Nat} {A L : Board 5} {ℓ : Fin 5 → Lab} (s : SEq D k A K L) (hv : Valid K L) {e : Fin 5}
    (h : SBlackOut D J k A ℓ e) : BlackWin K L ℓ ∨ BlackOut K (IKL D J K) L ℓ e := by
  rcases h with ⟨hl, hlen, hall⟩ | ⟨hl, hlen, hj⟩ | ⟨hl, hj⟩
  · have hleg : (L e).length < K := (s.legal_iff e).mp hlen
    obtain ⟨k₂, A₂, hvar, s2⟩ := exists_variant s e .black
    rcases hall k₂ A₂ hvar with hf | hj
    · exact Or.inl ⟨e, hl, hleg, (s2.hasFour_iff hD _).mp hf⟩
    · exact Or.inr (Or.inl ⟨hl, hleg, jl_real hD hj s2⟩)
  · have hfull : (L e).length = K := by
      have h1 : ¬ (L e).length < K := fun h => by
        have : (A e).length < k := (s.legal_iff e).mpr h
        omega
      have := hv e
      omega
    exact Or.inr (Or.inr (Or.inl ⟨hl, hfull, jl_real hD hj s⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hl, jl_real hD hj s⟩))

/-- **Zone on stretch.**  An abstract certificate gives a zone certificate on every zone height. -/
theorem zoneCert2_of_sz {D : Nat} (hD : 2 ≤ D) {J : Nat → Board 5 → (Fin 5 → Lab) → Prop}
    (hJ : SZCert D J) (K : Nat) : ZoneCert2 K (IK D J K) (IKL D J K) := by
  rintro L ℓ ⟨k, A, hm, s⟩ c
  obtain ⟨hvA, hc⟩ := hJ k A ℓ hm
  have hvL : Valid K L := s.valid hvA
  obtain ⟨h1, h2, h3⟩ := hc c
  refine ⟨?_, ?_, ?_⟩
  · intro hl hlen
    have hlenA : (A c).length < k := (s.legal_iff c).mpr hlen
    obtain ⟨k₁, A₁, hvar, s1⟩ := exists_variant s c .white
    obtain ⟨hnf, hrest⟩ := h1 hl hlenA k₁ A₁ hvar
    refine ⟨fun hf => hnf ((s1.hasFour_iff hD _).mpr hf), ?_⟩
    have hv1 : Valid K (play L c .white) := play_valid hvL hlen
    rcases hrest with hw | ⟨e, hcond, hout⟩
    · exact Or.inl (sblackWin_real hD s1 hw)
    · rcases sblackOut_real hD s1 hv1 hout with hw | ho
      · exact Or.inl hw
      · refine Or.inr ⟨e, ?_, ho⟩
        rcases hcond with h | h
        · exact Or.inl h
        · right
          have := s.room c
          omega
  · intro hl hlen
    have hlenA : (A c).length = k := by
      have h1' : ¬ (A c).length < k := fun h => by
        have : (L c).length < K := (s.legal_iff c).mp h
        omega
      have := hvA c
      omega
    exact jl_real hD (h2 hl hlenA) s
  · intro hl
    rcases h3 hl with hall | hw | ⟨e, hout⟩
    · exact Or.inl hall
    · exact Or.inr (Or.inl (sblackWin_real hD s hw))
    · rcases sblackOut_real hD s hvL hout with hw | ho
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr ⟨e, ho⟩)

/-- **Safety from an abstract zone certificate.**  `R` is a real board on height `H ≥ K + 2` whose
bottom `K` rows are a stretch of a member, with all-`low`… labels read off `R`. -/
theorem zone_safe_extra {K H : Nat} (hK : K % 2 = 0) (hH : H % 2 = 0) (hKH : K + 2 ≤ H)
    {I : Board 5 → (Fin 5 → Lab) → Prop}
    (hI : ZoneCert2 K I (fun L ℓ => I L ℓ ∨ (∃ q, ClaimHyp K L q) ∨ ZHyp K L)) {R : Board 5}
    (inv : ZInv K H I R) : Safe H R := by
  refine safe_of_inv2L (ZInv K H I) (fun _ h => ⟨h.tm, h.nw⟩) ?_ R inv
  intro R inv c hc
  obtain ⟨hnw1, hrest⟩ := zone_step2 hK hH hKH (fun L ℓ h => Or.inl h) hI inv c hc
  refine ⟨hnw1, ?_⟩
  rcases hrest with hfull | ⟨e, he, hwin | inv2⟩
  · exact Or.inl hfull
  · exact Or.inr ⟨e, he, Or.inl hwin⟩
  · refine Or.inr ⟨e, he, Or.inr ?_⟩
    rcases inv2.abs with (hI2 | (⟨q, hy⟩ | hz)) | hhigh
    · exact Or.inl ⟨inv2.tm, inv2.nw, inv2.nb, inv2.dE, inv2.dT, inv2.valid, Or.inl hI2⟩
    · exact Or.inr (zone_leaf_safe hH (by omega) inv2.tm inv2.nw inv2.nb inv2.valid inv2.dE inv2.dT hy)
    · exact Or.inr (zone_leaf (by omega) hH inv2.tm inv2.nw inv2.nb inv2.valid inv2.dE inv2.dT hz)
    · exact Or.inl ⟨inv2.tm, inv2.nw, inv2.nb, inv2.dE, inv2.dT, inv2.valid, Or.inr hhigh⟩

theorem sz_safe {D : Nat} (hD : 2 ≤ D) {J : Nat → Board 5 → (Fin 5 → Lab) → Prop}
    (hJ : SZCert D J) {K H : Nat} (hK : K % 2 = 0) (hH : H % 2 = 0) (hKH : K + 2 ≤ H)
    {R : Board 5} (htm : toMove R = .white) (hnw : ¬ HasFour H R .white)
    (hnb : ¬ HasFour H R .black) (hE : DiscE K R) (hT : ∀ c, TCol K H R c) (hv : Valid H R)
    {k : Nat} {A : Board 5} (hm : J k A (labs H K R)) (s : SEq D k A K (trunc K R)) : Safe H R :=
  zone_safe_extra hK hH hKH (zoneCert2_of_sz hD hJ K)
    ⟨htm, hnw, hnb, hE, hT, hv, Or.inl ⟨k, A, hm, s⟩⟩

#print axioms C4W5.LongThreat.SZ.sz_safe
end C4W5.LongThreat.SZ
