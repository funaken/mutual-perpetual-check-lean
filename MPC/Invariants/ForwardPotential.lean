import MPC.Geometry.OpenableGeometry
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
# MPC.Invariants.ForwardPotential

Knights, lances, and pawns never make a discovered check in a periodic trace.

**The general potential lemma.** Fix a property `P` of pieces and a weight
`f : Pos → ℕ`. The potential of a state sums `f` over its non-glaring squares
whose piece satisfies `P`. In a periodic trace
these squares change only when a non-glaring piece with `P` moves on the board:
- a glaring piece moves to a glaring square (Lemma 2.6), and a drop glares
  (Lemma 2.7);
- a captured piece glares (Lemma 2.9), so no counted square is captured;
- a non-glaring piece lands on a non-glaring square (Lemma 2.8) and keeps its
  kind, so it is counted before the move exactly when it is counted after.
Such a move replaces `f src` by `f dst` in the sum
(`potential_succ_add_of_move`), and every other move keeps the sum
(`potential_succ_of_not_move`). If no such move lowers `f`, the potential never
falls; periodicity brings it back, so no such move changes `f`
(`potential_move_eq_of_periodic`).

**The application.** A knight, lance, or pawn moves strictly forward
(`forwardRank_lt_of_canMoveToOriented`). With `f` the owner's forward rank, a
non-glaring one would raise the potential, so none moves
(`not_nonGlaring_forward_move_of_periodic`). In particular, none is moved by a
discovered check (`not_openableMove_forward_of_periodic`). -/

namespace MPC

/-- How far `q` lies toward the opponent's side, as seen by `o`. -/
def forwardRank (o : Player) (q : Pos) : ℕ :=
  match o with
  | .sente => q.2.val
  | .gote => 8 - q.2.val

/-- The sign of the forward direction of `o` on the board's second coordinate. -/
private def fwdSign (o : Player) : ℤ :=
  match o with
  | .sente => 1
  | .gote => -1

private theorem forwardRank_sub (o : Player) (src dst : Pos) :
    (forwardRank o dst : ℤ) - forwardRank o src = fwdSign o * (Pos.dirTo src dst).2 := by
  have h1 := src.2.isLt
  have h2 := dst.2.isLt
  cases o <;> simp only [forwardRank, fwdSign, Pos.dirTo] <;> push_cast [Nat.cast_sub (by omega :
    src.2.val ≤ 8), Nat.cast_sub (by omega : dst.2.val ≤ 8)] <;> ring

private theorem step_forward (pt : PieceType) (o : Player)
    (hpt : pt = .knight ∨ pt = .lance ∨ pt = .pawn) :
    ∀ d ∈ pt.stepDirs.map (Dir.forPlayer · o), 0 < fwdSign o * d.2 := by
  rcases hpt with rfl | rfl | rfl <;> cases o <;> decide

private theorem slide_forward (pt : PieceType) (o : Player)
    (hpt : pt = .knight ∨ pt = .lance ∨ pt = .pawn) :
    ∀ d ∈ pt.slideDirs.map (Dir.forPlayer · o), 0 < fwdSign o * d.2 := by
  rcases hpt with rfl | rfl | rfl <;> cases o <;> decide

/-- A knight, lance, or pawn moves strictly forward. -/
theorem forwardRank_lt_of_canMoveToOriented (board : Board) (o : Player) (pt : PieceType)
    (src dst : Pos) (hpt : pt = .knight ∨ pt = .lance ∨ pt = .pawn)
    (h : canMoveToOriented board o pt src dst) : forwardRank o src < forwardRank o dst := by
  have hsub := forwardRank_sub o src dst
  rcases h with hst | ⟨sd, hsd, _, k, hk, _, hy, _⟩
  · have := step_forward pt o hpt _ hst
    omega
  · have hpos := slide_forward pt o hpt _ hsd
    have hk' : (0 : ℤ) < k := by exact_mod_cast hk
    have : 0 < fwdSign o * (Pos.dirTo src dst).2 := by
      rw [hy, show fwdSign o * (↑k * sd.2) = ↑k * (fwdSign o * sd.2) by ring]
      exact mul_pos hk' hpos
    omega

namespace MoveTrace

/-- Move `i` moves a non-glaring piece with `P` on the board from `src` to `dst`. -/
def NonGlaringMoveOf (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (P : Piece → Prop) (i : Fin tr.len) (src dst : Pos) : Prop :=
  ∃ (promote : Bool) (p : Piece), tr.moves i = .boardMove src dst promote ∧
    (tr.before i).board.grid src = some p ∧ ¬ tr.GlaresAtEnemyKing kp i.castSucc src ∧ P p

/-- The potential of state `k`: the sum of `f` over the non-glaring squares whose
    piece satisfies `P`. -/
noncomputable def potential (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (P : Piece → Prop) (f : Pos → ℕ) (k : Fin (tr.len + 1)) : ℕ :=
  (tr.nonGlaringSquaresOf kp P k).sum f

/-- In a periodic trace satisfying the periodic-check premises, a move keeps every counted square
    other than its endpoints, and never counts its destination before the move. -/
private theorem mem_succ_iff_of_ne (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (P : Piece → Prop) (i : Fin tr.len) (q : Pos)
    (hq : ¬ (tr.moves i).Touches q) :
    q ∈ tr.nonGlaringSquaresOf kp P i.succ ↔ q ∈ tr.nonGlaringSquaresOf kp P i.castSucc := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hg : (tr.states i.succ).board.grid q = (tr.states i.castSucc).board.grid q := by
    have key : ∀ mv : Move, tr.moves i = mv →
        (tr.states i.succ).board.grid q = (tr.states i.castSucc).board.grid q := by
      intro mv hm
      rw [hm] at hq
      cases mv with
      | boardMove src dst promote =>
        exact tr.boardMove_grid_other ht i src dst promote q hm (fun h => hq (Or.inl h))
          (fun h => hq (Or.inr h))
      | dropMove pt dst =>
        exact tr.dropMove_grid_other ht i pt dst q hm hq
    exact key _ rfl
  rw [mem_nonGlaringSquaresOf, mem_nonGlaringSquaresOf, hg,
    tr.glaresAtEnemyKing_congr kp ht hg ((hkp _).trans (hkp _).symm)]

private theorem destination_not_mem (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (P : Piece → Prop) (i : Fin tr.len) :
    (tr.moves i).destination ∉ tr.nonGlaringSquaresOf kp P i.castSucc := by
  intro hmem
  obtain ⟨⟨p, hpq, _⟩, hng⟩ := (tr.mem_nonGlaringSquaresOf kp P i.castSucc _).mp hmem
  exact hng (tr.glares_destination_of_occupied_of_periodic kp ht hs hk hsafe h0 hc hr hp i
    (by change (tr.states i.castSucc).board.grid _ ≠ none; rw [hpq]; exact Option.some_ne_none _))

/-- Under the same premises, a non-glaring piece with `P` moving from `src` to `dst`
    replaces `src` by `dst` among the counted squares. -/
theorem nonGlaringSquaresOf_succ_of_move (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (P : Piece → Prop) (i : Fin tr.len) (src dst : Pos)
    (hmv : tr.NonGlaringMoveOf kp P i src dst) :
    src ∈ tr.nonGlaringSquaresOf kp P i.castSucc ∧
      dst ∉ (tr.nonGlaringSquaresOf kp P i.castSucc).erase src ∧
      tr.nonGlaringSquaresOf kp P i.succ =
        insert dst ((tr.nonGlaringSquaresOf kp P i.castSucc).erase src) := by
  obtain ⟨promote, p, hm, hpc, hng, hP⟩ := hmv
  have hd := tr.boardMoveEndpointsDistinct_of_oriented hs hr
  have hsd := hd i src dst promote hm
  have hsrc : src ∈ tr.nonGlaringSquaresOf kp P i.castSucc :=
    (tr.mem_nonGlaringSquaresOf kp P _ _).mpr ⟨⟨p, hpc, hP⟩, hng⟩
  have hdst0 : dst ∉ tr.nonGlaringSquaresOf kp P i.castSucc := by
    have h := tr.destination_not_mem kp ht hs hk hsafe h0 hc hr hp P i
    rw [hm] at h
    exact h
  refine ⟨hsrc, fun h => hdst0 (Finset.mem_of_mem_erase h), ?_⟩
  ext q
  rw [Finset.mem_insert, Finset.mem_erase]
  by_cases hqd : q = dst
  · subst hqd
    -- The destination receives the same non-glaring piece.
    have hgrid := tr.boardMove_grid_dst_eq_of_not_glares_of_periodic kp ht hs hk hsafe h0 hc hr hp
      i src q promote hm hng
    have hngd : ¬ tr.GlaresAtEnemyKing kp i.succ q := fun hg =>
      hng (tr.glares_source_of_glares_destination_of_periodic kp ht hs hk hsafe h0 hc hr hp i src
        q promote hm hg)
    refine ⟨fun _ => Or.inl rfl, fun _ => ?_⟩
    refine (tr.mem_nonGlaringSquaresOf kp P _ _).mpr ⟨⟨p, ?_, hP⟩, hngd⟩
    change (tr.after i).board.grid q = some p
    rw [hgrid, hpc]
  · by_cases hqs : q = src
    · subst hqs
      have hempty : (tr.states i.succ).board.grid q = none :=
        tr.boardMove_grid_src ht i q dst promote hm hsd
      constructor
      · intro hmem
        obtain ⟨⟨p', hp', _⟩, _⟩ := (tr.mem_nonGlaringSquaresOf kp P _ _).mp hmem
        rw [hempty] at hp'
        cases hp'
      · rintro (h | ⟨h, _⟩)
        · exact absurd h hqd
        · exact absurd rfl h
    · have hiff := tr.mem_succ_iff_of_ne kp ht hs hk hsafe h0 hc hr hp P i q (by
        rw [hm]
        rintro (h | h)
        · exact hqs h
        · exact hqd h)
      rw [hiff]
      constructor
      · intro h
        exact Or.inr ⟨hqs, h⟩
      · rintro (h | ⟨_, h⟩)
        · exact absurd h hqd
        · exact h

/-- Under the same premises, a move that is not a non-glaring move of a piece with
    `P` keeps the counted squares. -/
theorem nonGlaringSquaresOf_succ_of_not_move (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (P : Piece → Prop) (i : Fin tr.len)
    (hno : ∀ src dst, ¬ tr.NonGlaringMoveOf kp P i src dst) :
    tr.nonGlaringSquaresOf kp P i.succ = tr.nonGlaringSquaresOf kp P i.castSucc := by
  have hd := tr.boardMoveEndpointsDistinct_of_oriented hs hr
  have hdst0 := tr.destination_not_mem kp ht hs hk hsafe h0 hc hr hp P i
  ext q
  by_cases hq : (tr.moves i).Touches q
  · -- The move touches `q`: neither side counts it.
    have hnot : q ∉ tr.nonGlaringSquaresOf kp P i.succ := by
      intro hmem
      obtain ⟨⟨p', hp', hP'⟩, hng'⟩ := (tr.mem_nonGlaringSquaresOf kp P _ _).mp hmem
      rcases hm : tr.moves i with ⟨src, dst, promote⟩ | ⟨pt, dst⟩
      · rw [hm] at hq
        rcases hq with rfl | rfl
        · have hempty : (tr.states i.succ).board.grid q = none :=
            tr.boardMove_grid_src ht i q dst promote hm (hd i q dst promote hm)
          rw [hempty] at hp'
          cases hp'
        · -- A counted destination comes from a non-glaring source with the same piece.
          obtain ⟨p, hpc, _⟩ := hs i src q promote hm
          have hsng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src := fun hg =>
            hng' (tr.destination_glares_of_source_glares kp ht hs hk hsafe h0 hc i src q promote
              hm hg)
          have hgrid := tr.boardMove_grid_dst_eq_of_not_glares_of_periodic kp ht hs hk hsafe h0
            hc hr hp i src q promote hm hsng
          change (tr.after i).board.grid q = some p' at hp'
          rw [hgrid, hpc] at hp'
          have hpp : p = p' := Option.some.inj hp'
          exact hno src q ⟨promote, p, hm, hpc, hsng, by rw [hpp]; exact hP'⟩
      · rw [hm] at hq
        change q = dst at hq
        subst hq
        exact hng' (tr.dropMove_glares_of_everyMoveChecksOpponent kp ht hs hk hsafe h0 hc i pt q hm)
    have hnot0 : q ∉ tr.nonGlaringSquaresOf kp P i.castSucc := by
      intro hmem
      rcases hm : tr.moves i with ⟨src, dst, promote⟩ | ⟨pt, dst⟩
      · rw [hm] at hq
        rcases hq with rfl | rfl
        · obtain ⟨⟨p, hpc, hP⟩, hng⟩ := (tr.mem_nonGlaringSquaresOf kp P _ _).mp hmem
          exact hno q dst ⟨promote, p, hm, hpc, hng, hP⟩
        · rw [hm] at hdst0
          exact hdst0 hmem
      · rw [hm] at hq hdst0
        change q = dst at hq
        subst hq
        exact hdst0 hmem
    exact ⟨fun h => absurd h hnot, fun h => absurd h hnot0⟩
  · exact tr.mem_succ_iff_of_ne kp ht hs hk hsafe h0 hc hr hp P i q hq

/-- Under the same premises, a non-glaring move of a piece with `P` from `src` to
    `dst` replaces `f src` by `f dst` in the potential. -/
theorem potential_succ_add_of_move (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (P : Piece → Prop) (f : Pos → ℕ) (i : Fin tr.len) (src dst : Pos)
    (hmv : tr.NonGlaringMoveOf kp P i src dst) :
    tr.potential kp P f i.succ + f src = tr.potential kp P f i.castSucc + f dst := by
  obtain ⟨hsrc, hdst, heq⟩ :=
    tr.nonGlaringSquaresOf_succ_of_move kp ht hs hk hsafe h0 hc hr hp P i src dst hmv
  unfold potential
  rw [heq, Finset.sum_insert hdst, ← Finset.add_sum_erase _ f hsrc]
  ring

/-- Under the same premises, every other move keeps the potential. -/
theorem potential_succ_of_not_move (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (P : Piece → Prop) (f : Pos → ℕ) (i : Fin tr.len)
    (hno : ∀ src dst, ¬ tr.NonGlaringMoveOf kp P i src dst) :
    tr.potential kp P f i.succ = tr.potential kp P f i.castSucc := by
  unfold potential
  rw [tr.nonGlaringSquaresOf_succ_of_not_move kp ht hs hk hsafe h0 hc hr hp P i hno]

/-- A count that never falls along a trace and ends where it started is the same in
    every state. -/
theorem count_eq_initial_of_step_ge (n : ℕ) (g : Fin (n + 1) → ℕ)
    (hstep : ∀ i : Fin n, g i.castSucc ≤ g i.succ) (hlast : g (Fin.last n) = g 0)
    (k : Fin (n + 1)) : g k = g 0 := by
  have hmono : ∀ {j l : Fin (n + 1)}, j ≤ l → g j ≤ g l := by
    intro j l hjl
    revert hjl
    induction l using Fin.induction with
    | zero =>
      intro hjl
      rw [Fin.le_zero_iff.mp hjl]
    | succ i ih =>
      intro hjl
      by_cases he : j = i.succ
      · rw [he]
      · have hlt : j < i.succ := Nat.lt_of_le_of_ne hjl fun hv => he (Fin.ext hv)
        exact (ih (Fin.le_castSucc_iff.mpr hlt)).trans (hstep i)
  have h1 := hmono (Fin.zero_le k)
  have h2 := hmono (Fin.le_last k)
  omega

/-- The general potential lemma: in a periodic trace satisfying the periodic-check premises, if
    no non-glaring move of a piece with `P` lowers `f`, then none changes `f`. -/
theorem potential_move_eq_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (P : Piece → Prop) (f : Pos → ℕ)
    (hf : ∀ i src dst, tr.NonGlaringMoveOf kp P i src dst → f src ≤ f dst)
    (i : Fin tr.len) (src dst : Pos) (hmv : tr.NonGlaringMoveOf kp P i src dst) :
    f dst = f src := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hstep : ∀ j : Fin tr.len,
      tr.potential kp P f j.castSucc ≤ tr.potential kp P f j.succ := by
    intro j
    by_cases hj : ∃ src dst, tr.NonGlaringMoveOf kp P j src dst
    · obtain ⟨s, d, hjm⟩ := hj
      have h := tr.potential_succ_add_of_move kp ht hs hk hsafe h0 hc hr hp P f j s d hjm
      have := hf j s d hjm
      omega
    · push Not at hj
      exact (tr.potential_succ_of_not_move kp ht hs hk hsafe h0 hc hr hp P f j hj).ge
  have hlast : tr.potential kp P f (Fin.last tr.len) = tr.potential kp P f 0 := by
    have hgrid : ∀ q, (tr.states (Fin.last tr.len)).board.grid q = (tr.states 0).board.grid q :=
      fun q => by rw [show tr.states (Fin.last tr.len) = tr.states 0 from hp]
    have hset : tr.nonGlaringSquaresOf kp P (Fin.last tr.len) = tr.nonGlaringSquaresOf kp P 0 := by
      ext q
      rw [tr.mem_nonGlaringSquaresOf, tr.mem_nonGlaringSquaresOf, hgrid q,
        tr.glaresAtEnemyKing_congr kp ht (hgrid q) (hp.kingPos_last hk)]
    unfold potential
    rw [hset]
  have hconst := count_eq_initial_of_step_ge tr.len (tr.potential kp P f) hstep hlast
  have h := tr.potential_succ_add_of_move kp ht hs hk hsafe h0 hc hr hp P f i src dst hmv
  rw [hconst i.succ, hconst i.castSucc] at h
  omega

/-- Under the same premises, no knight, lance, or pawn moves from a non-glaring
    square: it would move forward and raise the potential of its owner's forward
    ranks. -/
theorem not_nonGlaring_forward_move_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool) (p : Piece)
    (hm : tr.moves i = .boardMove src dst promote)
    (hpc : (tr.before i).board.grid src = some p)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src)
    (hpt : p.pieceType = .knight ∨ p.pieceType = .lance ∨ p.pieceType = .pawn) : False := by
  let P : Piece → Prop := fun x => x.owner = p.owner ∧
    (x.pieceType = .knight ∨ x.pieceType = .lance ∨ x.pieceType = .pawn)
  have hlt : ∀ j s d, tr.NonGlaringMoveOf kp P j s d →
      forwardRank p.owner s < forwardRank p.owner d := by
    rintro j s d ⟨pr, x, hmj, hxc, _, hxo, hxt⟩
    have h := hr j s d pr x hmj hxc
    rw [hxo] at h
    exact forwardRank_lt_of_canMoveToOriented _ _ _ s d hxt h
  have hmv : tr.NonGlaringMoveOf kp P i src dst := ⟨promote, p, hm, hpc, hng, rfl, hpt⟩
  have heq := tr.potential_move_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp P
    (forwardRank p.owner) (fun j s d h => (hlt j s d h).le) i src dst hmv
  have := hlt i src dst hmv
  omega

/-- In a periodic mutual-check trace, no knight, lance, or pawn is moved by a
    discovered check. -/
theorem not_openableMove_forward_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp) (o : Player)
    (pt : PieceType) (hpt : pt = .knight ∨ pt = .lance ∨ pt = .pawn) :
    ¬ tr.OpenableMoveBy kp o pt := by
  rintro ⟨i, src, dst, promote, _, hmv, hsrc, hng, _⟩
  exact tr.not_nonGlaring_forward_move_of_periodic kp hm.transitions hm.sourcesOwned
    hm.kingsWellPlaced hm.ownKingSafe hm.initialOpponentSafe hm.checks hm.movementRules
    hm.periodic i src dst promote ⟨o, pt⟩ hmv hsrc hng hpt

end MoveTrace
end MPC
