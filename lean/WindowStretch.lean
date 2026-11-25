import WindowBank
import C4W5.Cert.StretchZoneTree

/-! The same packed bank supports both old checking games. The encoding is only
a routing hint: matched rows must decode to the actual board, height, and labels. -/
namespace C4W5.WindowBank
open Connect4 (Player opponent)
open Connect4.NarrowBoards

structure SFormat where
  radix : Nat
  repBase : Nat
  key : Nat → Pos → Nat
  height : Nat → Nat
  pos : Nat → Pos

def srel (F : SFormat) (t : Bank) (h : Nat) (A : Board 5) : Prop :=
  ∃ w, Contains F.radix t w ∧ F.height w = h ∧ A = (F.pos w).toBoard

def smem (F : SFormat) (t : Bank) (h : Nat) (p : Pos) : Bool :=
  force (F.key h p) fun key =>
    match find F.radix F.repBase key t with
    | none => false
    | some w => (F.height w == h) && (F.pos w).beq p

theorem smem_sound {F : SFormat} {t : Bank} {h : Nat} {p : Pos}
    (hmem : smem F t h p = true) : srel F t h p.toBoard := by
  simp only [smem, force_eq] at hmem
  split at hmem
  · cases hmem
  next w ew =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hmem
    exact ⟨w, find_sound ew, hmem.1, congrArg Pos.toBoard (Pos.eq_of_beq hmem.2).symm⟩

def scheckRow (D : Nat) (F : SFormat) (t : Bank) (w : Nat) : Bool :=
  force w fun w => forceP (F.pos w) fun p =>
    stepOKS D (smem F t) (F.height w) p (w % F.repBase)

theorem stretchCert_of_bank {D : Nat} (hD : 2 ≤ D) (F : SFormat) (t : Bank)
    (hall : all F.radix (scheckRow D F t) t = true) :
    StretchCertL D CL (srel F t) := by
  rintro h A ⟨w, hw, rfl, rfl⟩ c hl h₁ A₁ hv
  have hc := all_sound hall hw
  simp only [scheckRow, force_eq, forceP_eq] at hc
  exact stepOKS_sound hD (fun _ _ h => smem_sound h) hc c hl h₁ A₁ hv

theorem stretch_safe_of_bank {D : Nat} (hD : 2 ≤ D) (F : SFormat) (t : Bank)
    (hall : all F.radix (scheckRow D F t) t = true)
    {h : Nat} {q : Pos} (hq : smem F t h q = true) {H : Nat} {R : Board 5}
    (htm : toMove R = .white) (hnw : ¬ HasFour H R .white)
    (hs : SEq D h q.toBoard H R) : Safe H R :=
  stretch_safeL hD (claim_leafSound hD) (stretchCert_of_bank hD F t hall)
    htm hnw (smem_sound hq) hs

structure SZFormat where
  radix : Nat
  repBase : Nat
  key : Nat → Pos → Lab5 → Nat
  height : Nat → Nat
  pos : Nat → Pos
  labels : Nat → Lab5

def szrel (F : SZFormat) (t : Bank) (h : Nat) (A : Board 5) (ls : Fin 5 → Lab) : Prop :=
  ∃ w, Contains F.radix t w ∧ F.height w = h ∧ A = (F.pos w).toBoard ∧ ls = (F.labels w).fn

def szmem (F : SZFormat) (t : Bank) (h : Nat) (p : Pos) (ls : Lab5) : Bool :=
  force (F.key h p ls) fun key =>
    match find F.radix F.repBase key t with
    | none => false
    | some w => (F.height w == h) && (F.pos w).beq p && (F.labels w).beq ls

theorem szmem_sound {F : SZFormat} {t : Bank} {h : Nat} {p : Pos} {ls : Lab5}
    (hmem : szmem F t h p ls = true) : szrel F t h p.toBoard ls.fn := by
  simp only [szmem, force_eq] at hmem
  split at hmem
  · cases hmem
  next w ew =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hmem
    exact ⟨w, find_sound ew, hmem.1.1, congrArg Pos.toBoard (Pos.eq_of_beq hmem.1.2).symm,
           congrArg Lab5.fn (Lab5.eq_of_beq hmem.2).symm⟩

def szcheckRow (D : Nat) (F : SZFormat) (t : Bank) (w : Nat) : Bool :=
  force w fun w => forceP (F.pos w) fun p =>
    stepOKSZ D (szmem F t) (F.height w) p (F.labels w) (w % F.repBase)

theorem szCert_of_bank {D : Nat} (hD : 2 ≤ D) (F : SZFormat) (t : Bank)
    (hall : all F.radix (szcheckRow D F t) t = true) :
    SZCert D (szrel F t) := by
  rintro h A ls ⟨w, hw, rfl, rfl, rfl⟩
  have hc := all_sound hall hw
  simp only [szcheckRow, force_eq, forceP_eq] at hc
  exact stepOKSZ_sound hD (fun _ _ _ h => szmem_sound h) hc

theorem sz_safe_of_bank {D : Nat} (hD : 2 ≤ D) (F : SZFormat) (t : Bank)
    (hall : all F.radix (szcheckRow D F t) t = true)
    {K H : Nat} (hK : K % 2 = 0) (hH : H % 2 = 0) (hKH : K + 2 ≤ H) {R : Board 5}
    (htm : toMove R = .white) (hnw : ¬ HasFour H R .white) (hnb : ¬ HasFour H R .black)
    (hE : DiscE K R) (hT : ∀ c, TCol K H R c) (hv : Valid H R)
    {k : Nat} {q : Pos} {lb : Lab5} (hq : szmem F t k q lb = true) (hl : lb.fn = labs H K R)
    (s : SEq D k q.toBoard K (trunc K R)) : Safe H R :=
  sz_safe hD (szCert_of_bank hD F t hall) hK hH hKH htm hnw hnb hE hT hv
    (hl ▸ szmem_sound hq) s

#print axioms C4W5.WindowBank.stretch_safe_of_bank
#print axioms C4W5.WindowBank.sz_safe_of_bank
end C4W5.WindowBank
