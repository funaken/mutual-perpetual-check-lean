import MPC.Legacy.CheckCompatibility
import MPC.Geometry.OpenableGeometry
import Lean
/-!
# MPC.Tests.OpenableGeometry

Concrete checks for the geometry of , with the enemy king at `(4, 4)`.

- Half-lines: `(6, 6)` lies two steps along `(1, 1)`, and `OnRay.unique` recovers
  that direction and distance. `(5, 6)` and `(3, 2)`, a knight's jump away, lie on
  no half-line.
- A rook on an empty board attacks `(4, 4)` from `(4, 0)` by sliding.
  `ray_of_attack_not_step` puts `(4, 0)` on the half-line along `(0, -1)` and lists
  the squares between: `(4, 2)` is one, `(5, 2)` is not. A knight attacking from
  `(3, 2)` by a step lies on no half-line, so the lemma needs its step premise.
- With a pawn on `(4, 2)`, `not_canMoveToOriented_of_blocked` rules out the rook
  moving from `(4, 0)` to `(4, 4)`, and a gold moving from `(4, 1)` to `(4, 3)`.
  On the empty board the rook move is possible, so the occupied square is needed.

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Openable geometry verification must not import GameSeq"

namespace MPC
namespace OpenableGeometryTests

private def K : Pos := (4, 4)

/-! ## Half-lines -/

private theorem diag : OnRay K (1, 1) 2 ((6, 6) : Pos) := by
  unfold OnRay K
  decide

-- The direction and the distance of a point are determined.
example (d : Dir) (c : ℤ) (h : OnRay K d c ((6, 6) : Pos)) : d = (1, 1) ∧ c = 2 :=
  OnRay.unique h diag

-- No king direction reaches a knight's jump from `K`.
private theorem off_ray (x y : Fin 9) (dx dy : ℤ) (hx : (x.val : ℤ) = 4 + dx)
    (hy : (y.val : ℤ) = 4 + dy) (hk : (dx = 1 ∨ dx = -1) ∧ (dy = 2 ∨ dy = -2)) (d : Dir)
    (c : ℤ) : ¬ OnRay K d c ((x, y) : Pos) := by
  rintro ⟨hd, hc, hq⟩
  simp only [PieceType.stepDirs, List.mem_cons, List.mem_nil_iff, or_false] at hd
  have h1 := congrArg Prod.fst hq
  have h2 := congrArg Prod.snd hq
  change (x.val : ℤ) = 4 + c * d.1 at h1
  change (y.val : ℤ) = 4 + c * d.2 at h2
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at h1 h2 <;> omega

example (d : Dir) (c : ℤ) : ¬ OnRay K d c ((5, 6) : Pos) :=
  off_ray 5 6 1 2 (by decide) (by decide) (by decide) d c

/-! ## Sliding attacks -/

private def emptyBoard : Board := { grid := fun _ => none, hand := fun _ => ∅ }

private theorem rook_attacks : attacksOriented emptyBoard .sente .rook ((4, 0) : Pos) K :=
  Or.inr ⟨(0, 1), by decide, by decide, 4, by decide, by decide, by decide,
    fun _ _ _ _ => rfl⟩

private theorem rook_not_step :
    Pos.dirTo ((4, 0) : Pos) K ∉ PieceType.rook.stepDirs.map (Dir.forPlayer · .sente) := by
  simp [PieceType.stepDirs]

-- The rook stands on the half-line along `(0, -1)`; `(4, 2)` is between, `(5, 2)` is not.
example : (∃ n : ℤ, OnRay K (0, -1) n ((4, 0) : Pos)) ∧
    (((4 : ℤ), (2 : ℤ)) ∈ slidePath ((4, 0) : Pos) K) ∧
    (((5 : ℤ), (2 : ℤ)) ∉ slidePath ((4, 0) : Pos) K) := by
  obtain ⟨d, n, hB, _, hiff⟩ := ray_of_attack_not_step _ _ _ _ _ rook_attacks rook_not_step
  have hdn := OnRay.unique hB (show OnRay K (0, -1) 4 ((4, 0) : Pos) by unfold OnRay K; decide)
  obtain ⟨rfl, rfl⟩ := hdn
  refine ⟨⟨4, hB⟩, (hiff _).mpr ⟨2, by norm_num, by norm_num, by decide⟩, ?_⟩
  rw [hiff]
  rintro ⟨c, _, _, h⟩
  have h1 := congrArg Prod.fst h
  change (5 : ℤ) = 4 + c * 0 at h1
  omega

-- A knight attacking by a step lies on no half-line: the step premise is needed.
example : attacksOriented emptyBoard .sente .knight ((3, 2) : Pos) K ∧
    ∀ (d : Dir) (c : ℤ), ¬ OnRay K d c ((3, 2) : Pos) :=
  ⟨Or.inl (by decide), off_ray 3 2 (-1) (-2) (by decide) (by decide) (by decide)⟩

/-! ## Blocked moves -/

private def pawnBoard : Board :=
  { grid := fun q => if q = ((4, 2) : Pos) then some ⟨.gote, .pawn⟩ else none
    hand := fun _ => ∅ }

-- The rook cannot pass the pawn, and neither can a gold step over it.
example : ¬ canMoveToOriented pawnBoard .sente .rook ((4, 0) : Pos) ((4, 4) : Pos) ∧
    ¬ canMoveToOriented pawnBoard .sente .gold ((4, 1) : Pos) ((4, 3) : Pos) := by
  constructor
  · exact not_canMoveToOriented_of_blocked pawnBoard .sente .rook (4, 0) (4, 4) (4, 2) (0, 1) 4 2
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide) (by decide)
  · exact not_canMoveToOriented_of_blocked pawnBoard .sente .gold (4, 1) (4, 3) (4, 2) (0, 1) 2 1
      (by decide) (by decide) (by norm_num) (by norm_num) (by decide) (by decide)

-- On the empty board the rook move is possible, so the occupied square is needed.
example : canMoveToOriented emptyBoard .sente .rook ((4, 0) : Pos) ((4, 4) : Pos) :=
  rook_attacks

end OpenableGeometryTests
end MPC
