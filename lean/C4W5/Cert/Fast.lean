import C4W5.Cert.Four

/-!
# Kernel-friendly versions

The kernel evaluates by name: an argument used twice is computed twice.  `force n f` makes the kernel
compute `n` to a literal before continuing.  `hasFourQ` is `hasFourF` with the five masks forced.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

def force {α : Sort _} (n : Nat) (f : Nat → α) : α :=
  match n with
  | 0 => f 0
  | m + 1 => f (m + 1)

@[simp] theorem force_eq {α : Sort _} (n : Nat) (f : Nat → α) : force n f = f n := by
  cases n <;> rfl

/-- Force all ten fields of a position. -/
def forceP {α : Sort _} (p : Pos) (f : Pos → α) : α :=
  force p.b0 fun a0 => force p.b1 fun a1 => force p.b2 fun a2 => force p.b3 fun a3 => force p.b4 fun a4 =>
  force p.h0 fun c0 => force p.h1 fun c1 => force p.h2 fun c2 => force p.h3 fun c3 => force p.h4 fun c4 =>
  f ⟨a0, a1, a2, a3, a4, c0, c1, c2, c3, c4⟩

@[simp] theorem forceP_eq {α : Sort _} (p : Pos) (f : Pos → α) : forceP p f = f p := by
  simp [forceP]

def fourM (m0 m1 m2 m3 m4 : Nat) : Bool :=
  and4 m0 (m0 >>> 1) (m0 >>> 2) (m0 >>> 3) || and4 m1 (m1 >>> 1) (m1 >>> 2) (m1 >>> 3) ||
  and4 m2 (m2 >>> 1) (m2 >>> 2) (m2 >>> 3) || and4 m3 (m3 >>> 1) (m3 >>> 2) (m3 >>> 3) ||
  and4 m4 (m4 >>> 1) (m4 >>> 2) (m4 >>> 3) ||
  and4 m0 m1 m2 m3 || and4 m1 m2 m3 m4 ||
  and4 m0 (m1 >>> 1) (m2 >>> 2) (m3 >>> 3) || and4 m1 (m2 >>> 1) (m3 >>> 2) (m4 >>> 3) ||
  and4 (m0 >>> 3) (m1 >>> 2) (m2 >>> 1) m3 || and4 (m1 >>> 3) (m2 >>> 2) (m3 >>> 1) m4

def Pos.hasFourQ (p : Pos) (pl : Player) : Bool :=
  force (p.mask pl 0) fun m0 => force (p.mask pl 1) fun m1 => force (p.mask pl 2) fun m2 =>
  force (p.mask pl 3) fun m3 => force (p.mask pl 4) fun m4 => fourM m0 m1 m2 m3 m4

theorem Pos.hasFourQ_eq (p : Pos) (pl : Player) : p.hasFourQ pl = p.hasFourF pl := by
  simp only [Pos.hasFourQ, force_eq, fourM, Pos.hasFourF, List.any_cons, List.any_nil, lineB,
    Bool.or_false, Bool.or_assoc]

end C4W5
