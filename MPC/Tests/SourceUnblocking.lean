import MPC.Legacy.CheckCompatibility
import MPC.Trace.SourceUnblocking
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.SourceUnblocking

Concrete new/continuing checks and the source-presence boundary. These board
updates do not certify complete movement, promotion, or capture legality.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Source unblocking verification must not import GameSeq"

namespace MPC
namespace SourceUnblockingTests

private def point (owner : Player) (diagonal : Bool) (j : Fin 9) : Pos :=
  (if diagonal then j else 0, if owner = .sente then j else 4 - j)
private def direction (owner : Player) (diagonal : Bool) : Dir :=
  (if diagonal then 1 else 0, if owner = .sente then 1 else -1)
private def kind (diagonal lance : Bool) : PieceType :=
  if diagonal then .bishop else if lance then .lance else .rook
private def initial (owner : Player) (diagonal lance occupied : Bool) : BoardState :=
  { board :=
    { grid := fun p =>
        if p = point owner diagonal 0 then some ⟨owner, kind diagonal lance⟩
        else if p = point owner diagonal 2 then some ⟨owner, .gold⟩
        else if p = (8, 8) then some ⟨owner, .king⟩
        else if p = point owner diagonal 4 then some ⟨owner.opponent, .king⟩
        else if p = (5, 4) ∧ occupied = true then some ⟨owner.opponent, .pawn⟩ else none
      hand := fun _ => ∅ }
    turn := owner }
private def move (owner : Player) (diagonal promote : Bool) : Move :=
  .boardMove (point owner diagonal 2) (5, 4) promote

private theorem clearance (b : Board) (owner : Player) (diagonal : Bool) :
    pathClear b (point owner diagonal 0) (point owner diagonal 4) ↔
      b.grid (point owner diagonal 1) = none ∧ b.grid (point owner diagonal 2) = none ∧
      b.grid (point owner diagonal 3) = none := by
  have hc := pathClear_iff_of_exact_steps b (point owner diagonal 0) (point owner diagonal 4)
    (direction owner diagonal) 4 (by cases owner <;> cases diagonal <;> decide)
    (by decide) (by cases owner <;> cases diagonal <;> decide)
    (by cases owner <;> cases diagonal <;> decide) (by cases owner <;> cases diagonal <;> decide)
  constructor
  · intro h
    have h1 := hc.mp h 1 (by decide) (by decide) (by cases owner <;> cases diagonal <;> unfold onBoard <;> decide)
    have h2 := hc.mp h 2 (by decide) (by decide) (by cases owner <;> cases diagonal <;> unfold onBoard <;> decide)
    have h3 := hc.mp h 3 (by decide) (by decide) (by cases owner <;> cases diagonal <;> unfold onBoard <;> decide)
    cases owner <;> cases diagonal <;> exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    apply hc.mpr
    intro j hj hjn hob
    interval_cases j <;> cases owner <;> cases diagonal <;> assumption

private theorem ray_attack (b : Board) (owner : Player) (diagonal lance : Bool) :
    attacksOriented b owner (kind diagonal lance) (point owner diagonal 0) (point owner diagonal 4) ↔
      pathClear b (point owner diagonal 0) (point owner diagonal 4) := by
  constructor
  · rintro (hs | ⟨_, _, _, _, _, _, _, hc⟩)
    · cases diagonal <;> cases lance <;> simp [kind, PieceType.stepDirs] at hs
    · exact hc
  · intro hc
    refine Or.inr ⟨direction owner diagonal, ?_, ?_, 4, by decide, ?_, ?_, hc⟩ <;>
      cases owner <;> cases diagonal <;> cases lance <;> decide

private theorem ray_new (owner : Player) (diagonal lance occupied promote : Bool) :
    ¬ attacksOriented (initial owner diagonal lance occupied).board owner (kind diagonal lance)
      (point owner diagonal 0) (point owner diagonal 4) ∧
    attacksOriented (applyMove (initial owner diagonal lance occupied) (move owner diagonal promote)).board
      owner (kind diagonal lance) (point owner diagonal 0) (point owner diagonal 4) := by
  constructor
  · rw [ray_attack, clearance]
    intro h
    have he := h.2.1
    cases owner <;> cases diagonal <;> simp [initial, point] at he
  · rw [ray_attack, clearance]
    cases owner <;> cases diagonal <;> cases lance <;> cases occupied <;> cases promote <;>
      exact ⟨rfl, rfl, rfl⟩

-- All three slider types, both owners, both promotion flags and destination
-- occupancies use actual before/after attacks and the public exact-ray theorem.
example (owner : Player) (diagonal lance occupied promote : Bool) :
    ∃ d ∈ (kind diagonal lance).slideDirs.map (Dir.forPlayer · owner),
      (Pos.dirTo (point owner diagonal 0) (point owner diagonal 4)).normalize = d ∧
      ∃ n j : ℕ, 1 ≤ n ∧ n ≤ 8 ∧ 1 ≤ j ∧ j < n ∧
        (point owner diagonal 4).toInt = ((point owner diagonal 0).toInt.1 + ↑n * d.1,
          (point owner diagonal 0).toInt.2 + ↑n * d.2) ∧
        (point owner diagonal 2).toInt = ((point owner diagonal 0).toInt.1 + ↑j * d.1,
          (point owner diagonal 0).toInt.2 + ↑j * d.2) := by
  exact applyMove_boardMove_new_attack_exact_slide _ _ _ _ _ promote ⟨owner, .gold⟩
    ⟨owner, kind diagonal lance⟩ (by cases owner <;> cases diagonal <;> rfl)
    (ray_new owner diagonal lance occupied promote).1 (ray_new owner diagonal lance occupied promote).2

private theorem other_checker (owner : Player) (diagonal lance occupied promote : Bool) :
    hasOtherCheckerOriented (applyMove (initial owner diagonal lance occupied)
      (move owner diagonal promote)).board (move owner diagonal promote) owner.opponent
      (point owner diagonal 4) := by
  refine ⟨point owner diagonal 0, ?_, ⟨owner, kind diagonal lance⟩, ?_, ?_,
    (ray_new owner diagonal lance occupied promote).2⟩
  · change point owner diagonal 0 ≠ (5, 4)
    cases owner <;> cases diagonal <;> decide
  · cases owner <;> cases diagonal <;> cases occupied <;> rfl
  · cases owner <;> rfl

private theorem before_safe (owner : Player) (diagonal lance occupied : Bool) :
    ¬ inCheckOriented (initial owner diagonal lance occupied).board owner.opponent
      (point owner diagonal 4) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  dsimp only [initial] at hp
  split_ifs at hp with h0 h2 hk h4 hd
  · cases hp; subst pos; exact (ray_new owner diagonal lance occupied false).1 ha
  · cases hp; subst pos
    cases owner <;> cases diagonal <;>
      simp [attacksOriented, canMoveToOriented, PieceType.stepDirs, PieceType.slideDirs,
        point, Pos.dirTo, Dir.forPlayer, Dir.flip] at ha
  · cases hp; subst pos
    cases owner <;> cases diagonal <;>
      simp [attacksOriented, canMoveToOriented, PieceType.stepDirs, PieceType.slideDirs,
        point, Pos.dirTo, Dir.forPlayer, Dir.flip] at ha
  · cases hp; cases owner <;> cases ho
  · cases hp; cases owner <;> cases ho

private def positions (owner : Player) : Player → Pos :=
  fun p => if p = owner then (8, 8) else point owner false 4

private theorem placed (owner : Player) :
    KingsWellPlaced (initial owner false false false).board (positions owner) := by
  intro p q
  cases owner <;> cases p <;> by_cases h0 : q = (0, 0) <;>
    by_cases h4 : q = (0, 4) <;> by_cases h2 : q = (0, 2) <;> by_cases hk : q = (8, 8) <;>
    simp_all [initial, positions, point, kind, Player.opponent]

-- Actual kings, generated positions, and the trace corollary at the only hand
-- (both the first and last hand). Position equality is supplied explicitly.
example (owner : Player) (promote : Bool) :
    let tr := MoveTrace.single (initial owner false false false) (move owner false promote)
    let kp := tr.kingPositionsFrom (positions owner)
    tr.KingsWellPlaced kp ∧ ∃ pos piece,
      (tr.before (0 : Fin 1)).board.grid pos = some piece ∧
      (tr.after (0 : Fin 1)).board.grid pos = some piece ∧
      piece.owner = owner ∧ (point owner false 2).toInt ∈ slidePath pos (kp 1 owner.opponent) := by
  dsimp only
  let tr := MoveTrace.single (initial owner false false false) (move owner false promote)
  have ht := MoveTrace.single_followsTransitions (initial owner false false false) (move owner false promote)
  have hp : tr.KingsWellPlaced (tr.kingPositionsFrom (positions owner)) := by
    apply MoveTrace.kingsWellPlaced_kingPositionsFrom tr (positions owner) ht
    · intro i p; have hi := Fin.eq_zero i; subst i
      change (initial owner false false false).board.grid (5, 4) ≠ some ⟨p, .king⟩
      cases owner <;> cases p <;> decide
    · intro i pt dst hm; change Move.boardMove _ _ _ = .dropMove pt dst at hm; cases hm
    · exact placed owner
  refine ⟨hp, ?_⟩
  have h := MoveTrace.boardMove_otherChecker_source_unblocking tr ht
    (tr.kingPositionsFrom (positions owner)) (0 : Fin 1) (point owner false 2) (5, 4) promote
    ⟨owner, .gold⟩ owner.opponent rfl (by cases owner <;> rfl)
    (by cases owner <;> rfl) (by cases owner <;> exact before_safe _ _ _ _)
    (by cases owner
        · exact other_checker .sente false false false promote
        · exact other_checker .gote false false false promote)
  obtain ⟨pos, piece, _, _, hb, ha, ho, _, hs, _⟩ := h
  exact ⟨pos, piece, hb, ha, by cases owner <;> exact ho, hs⟩

-- The diagonal example also has a destination checker (a gold), so the new
-- other-position check is not an exclusive alternative to destination check.
example (occupied promote : Bool) :
    hasDestinationCheckerOriented
      (applyMove (initial .sente true false occupied) (move .sente true promote)).board
      (move .sente true promote) .gote (4, 4) ∧
    hasOtherCheckerOriented
      (applyMove (initial .sente true false occupied) (move .sente true promote)).board
      (move .sente true promote) .gote (4, 4) := by
  refine ⟨⟨⟨.sente, .gold⟩, ?_, rfl, ?_⟩, other_checker _ _ _ _ _⟩
  · cases occupied <;> cases promote <;> rfl
  · left; change Pos.dirTo (5, 4) (4, 4) ∈ PieceType.gold.stepDirs.map (Dir.forPlayer · .sente); decide

-- Moving an off-ray piece preserves an existing checker: the before-attack
-- is true, so the new-attack premise is unavailable.
example (owner : Player) :
    let bs := applyMove (initial owner false false false) (move owner false false)
    attacksOriented bs.board owner .rook (point owner false 0) (point owner false 4) ∧
    attacksOriented (applyMove bs (.boardMove (5, 4) (6, 4) false)).board owner .rook
      (point owner false 0) (point owner false 4) ∧
    (Pos.toInt (5, 4)) ∉ slidePath (point owner false 0) (point owner false 4) := by
  refine ⟨(ray_new owner false false false false).2, ?_, ?_⟩
  · change attacksOriented _ owner (kind false false) _ _
    rw [ray_attack, clearance]
    cases owner <;> exact ⟨rfl, rfl, rfl⟩
  · cases owner <;> decide

-- An absent source can erase the occupied destination and thereby enable a
-- remote checker. This is an applyMove example, not a legal move or GameSeq.
example (owner : Player) :
    let bs := initial owner false false false
    bs.board.grid (7, 7) = none ∧
    ¬ attacksOriented bs.board owner .rook (point owner false 0) (point owner false 4) ∧
    attacksOriented (applyMove bs (.boardMove (7, 7) (0, 2) false)).board owner .rook
      (point owner false 0) (point owner false 4) ∧
    (Pos.toInt (7, 7)) ∉ slidePath (point owner false 0) (point owner false 4) ∧
    (Pos.toInt (0, 2)) ∈ slidePath (point owner false 0) (point owner false 4) := by
  refine ⟨by cases owner <;> rfl, (ray_new owner false false false false).1, ?_, ?_, ?_⟩
  · change attacksOriented _ owner (kind false false) _ _
    rw [ray_attack, clearance]
    cases owner <;> exact ⟨rfl, rfl, rfl⟩
  · cases owner <;> decide
  · cases owner <;> decide

end SourceUnblockingTests
end MPC
