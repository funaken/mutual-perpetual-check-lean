import MPC.Pieces.GoldTypeMove
/-!
# MPC.Pieces.SilverMove

Where a non-glaring silver can move in a periodic trace.

A board move of a non-glaring piece goes between two half-lines from the enemy
king `K` that are neither equal nor opposite, and neither end attacks `K`
by a step (step attacks ignore the board). For a silver this leaves only the moves
between `(σ, 0)` and `(0, τ)` relative to `K`, where `σ = ±1` and `τ` is the
owner's forward sign (`silver_step_between_lines`, `SilverSquares`). These are the
paper's moves between `(±1, 0)` and `(0, 1)`.

Each such move has a reverse (`silver_move_reverse_of_periodic`):
- from `(σ, 0)` to `(0, τ)`: the silver reached `(σ, 0)` by a move of the same
  silver (coverage, ), which can only come from `(0, τ)`;
- from `(0, τ)` to `(σ, 0)`: the silver leaves `(σ, 0)` later (Proposition 3.3),
  which it can only do toward `(0, τ)`.

 uses both moves to place the mover's king and count rooks. No GameSeq is
used.
-/

namespace MPC

/-- Coordinates of `q` relative to `K`. -/
def relTo (K q : Pos) : ℤ × ℤ := (q.toInt.1 - K.toInt.1, q.toInt.2 - K.toInt.2)

theorem relTo_inj {K a b : Pos} (h : relTo K a = relTo K b) : a = b := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [relTo, Pos.toInt] at h1 h2
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

/-- The silver's squares: relative to the enemy king, a non-glaring silver of `o`
    moves between `(σ, 0)` and `(0, τ)`, with `σ = ±1` and `τ = forwardSign o`. -/
def SilverSquares (o : Player) (v w : ℤ × ℤ) : Prop :=
  ((v.1 = 1 ∨ v.1 = -1) ∧ v.2 = 0 ∧ w = (0, forwardSign o)) ∨
    (v = (0, forwardSign o) ∧ (w.1 = 1 ∨ w.1 = -1) ∧ w.2 = 0)

/-- The case analysis: between two lines through the enemy king, not collinear
    with it, a silver step whose ends do not attack the king by a silver step goes
    between `(σ, 0)` and `(0, τ)`. -/
theorem silver_step_between_lines (o : Player) (v w : ℤ × ℤ)
    (hv : v.1 = 0 ∨ v.2 = 0 ∨ v.1 = v.2 ∨ v.1 = -v.2)
    (hw : w.1 = 0 ∨ w.2 = 0 ∨ w.1 = w.2 ∨ w.1 = -w.2)
    (hcross : v.1 * w.2 - v.2 * w.1 ≠ 0)
    (hs : ((w.1 - v.1, w.2 - v.2) : Dir) ∈ PieceType.silver.stepDirs.map (Dir.forPlayer · o))
    (hv' : ((-v.1, -v.2) : Dir) ∉ PieceType.silver.stepDirs.map (Dir.forPlayer · o))
    (hw' : ((-w.1, -w.2) : Dir) ∉ PieceType.silver.stepDirs.map (Dir.forPlayer · o)) :
    SilverSquares o v w := by
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  dsimp only at hv hw hcross hs hv' hw'
  unfold SilverSquares
  simp only [Prod.mk.injEq]
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = w1 - v1 := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s2, s2 = w2 - v2 := ⟨_, rfl⟩
  have hcross' : v1 * s2 - v2 * s1 ≠ 0 := by
    intro h
    apply hcross
    rw [hs1, hs2] at h
    have e : v1 * w2 - v2 * w1 = v1 * (w2 - v2) - v2 * (w1 - v1) := by ring
    rw [e]
    exact h
  have hw1 : w1 = v1 + s1 := by omega
  have hw2 : w2 = v2 + s2 := by omega
  rw [← hs1, ← hs2] at hs
  subst hw1
  subst hw2
  -- Both ends lie within two squares of the king; the rest is a finite check.
  cases o <;>
    simp only [PieceType.stepDirs, List.map_cons, List.map_nil, Dir.forPlayer, Dir.flip,
      List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hs <;>
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [forwardSign] <;>
    (have hb : -2 ≤ v1 ∧ v1 ≤ 2 ∧ -2 ≤ v2 ∧ v2 ≤ 2 := by omega
     obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
     interval_cases v1 <;> interval_cases v2 <;>
       first | omega | exact absurd (by decide) hv' | exact absurd (by decide) hw')

/-- In board coordinates: a silver step between two half-lines from the enemy king
    `K` that are neither equal nor opposite, whose ends do not attack `K` by a silver
    step, goes between `(σ, 0)` and `(0, τ)` relative to `K`. -/
theorem silverSquares_of_step_between_rays (o : Player) (K src dst : Pos) (d e : Dir)
    (a b : ℤ) (hsrc : OnRay K d a src) (hdst : OnRay K e b dst) (h1 : e ≠ d)
    (h2 : e ≠ (-d.1, -d.2))
    (hmove : Pos.dirTo src dst ∈ PieceType.silver.stepDirs.map (Dir.forPlayer · o))
    (hsK : Pos.dirTo src K ∉ PieceType.silver.stepDirs.map (Dir.forPlayer · o))
    (hdK : Pos.dirTo dst K ∉ PieceType.silver.stepDirs.map (Dir.forPlayer · o)) :
    SilverSquares o (relTo K src) (relTo K dst) :=
  silver_step_between_lines o (relTo K src) (relTo K dst) hsrc.on_line hdst.on_line
    (hsrc.cross_ne_zero hdst h1 h2)
    (by
      convert hmove using 1
      simp only [relTo, Pos.dirTo, Pos.toInt]
      ext <;> dsimp only <;> ring)
    (by
      convert hsK using 2
      simp only [relTo, Pos.dirTo, Pos.toInt]
      ext <;> dsimp only <;> ring)
    (by
      convert hdK using 2
      simp only [relTo, Pos.dirTo, Pos.toInt]
      ext <;> dsimp only <;> ring)

namespace MoveTrace

/-- In a periodic trace satisfying the periodic-check premises, a board move of a non-glaring
    silver goes between `(σ, 0)` and `(0, τ)` relative to the enemy king. -/
theorem silverSquares_of_nonGlaring_move_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool) (p : Piece)
    (hm : tr.moves i = .boardMove src dst promote)
    (hpc : (tr.before i).board.grid src = some p)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) (hpt : p.pieceType = .silver) :
    SilverSquares p.owner (relTo (kp 0 p.owner.opponent) src)
      (relTo (kp 0 p.owner.opponent) dst) := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hown : p.owner = (tr.before i).turn := by
    obtain ⟨piece, hpiece, ho⟩ := hs i src dst promote hm
    rw [hpc] at hpiece
    cases hpiece
    exact ho
  obtain ⟨d, e, a, b, hsrc, hdst, h1, h2⟩ :=
    tr.openable_move_rays_of_periodic kp ht hs hk hsafe h0 hc hr hp i src dst promote hm hng
  rw [← hown] at hsrc hdst
  have hmove : Pos.dirTo src dst ∈ PieceType.silver.stepDirs.map (Dir.forPlayer · p.owner) := by
    rcases hr i src dst promote p hm hpc with hst | ⟨sd, hsd, _⟩
    · rw [hpt] at hst
      exact hst
    · rw [hpt] at hsd
      exact absurd hsd (List.not_mem_nil)
  have hsK : Pos.dirTo src (kp 0 p.owner.opponent) ∉
      PieceType.silver.stepDirs.map (Dir.forPlayer · p.owner) := by
    intro h
    apply hng
    refine ⟨p, hpc, Or.inl ?_⟩
    rw [hkp i.castSucc, hpt]
    exact h
  have hdK : Pos.dirTo dst (kp 0 p.owner.opponent) ∉
      PieceType.silver.stepDirs.map (Dir.forPlayer · p.owner) := by
    intro h
    have hngd : ¬ tr.GlaresAtEnemyKing kp i.succ dst := fun hg =>
      hng (tr.glares_source_of_glares_destination_of_periodic kp ht hs hk hsafe h0 hc hr hp i
        src dst promote hm hg)
    apply hngd
    have hgrid := tr.boardMove_grid_dst_eq_of_not_glares_of_periodic kp ht hs hk hsafe h0 hc hr
      hp i src dst promote hm hng
    refine ⟨p, ?_, Or.inl ?_⟩
    · change (tr.after i).board.grid dst = some p
      rw [hgrid, hpc]
    · rw [hkp i.succ, hpt]
      exact h
  exact silverSquares_of_step_between_rays p.owner _ src dst d e a b hsrc hdst h1 h2 hmove hsK
    hdK

/-- Under the same premises, the piece standing on a non-glaring move's source came
    there by a non-glaring board move of the same piece. -/
theorem arrival_of_nonGlaring_move_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool) (p : Piece)
    (hm : tr.moves i = .boardMove src dst promote)
    (hpc : (tr.before i).board.grid src = some p)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) :
    ∃ (i' : Fin tr.len) (src' : Pos) (pr : Bool), tr.moves i' = .boardMove src' src pr ∧
      (tr.before i').board.grid src' = some p ∧ ¬ tr.GlaresAtEnemyKing kp i'.castSucc src' := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hopen : tr.IsOpenableAt kp i.castSucc src := by
    refine ⟨?_, hng, fun himm => himm.2 i (by rw [hm]; exact Or.inl rfl)⟩
    change (tr.before i).board.grid src ≠ none
    rw [hpc]
    exact Option.some_ne_none _
  obtain ⟨i', j', _, _, _, _, _, _, _, hdi', hngi', _, hcyc, _, _, _, _, hall⟩ :=
    tr.openable_covered_of_periodic kp ht hs hk hsafe h0 hc hr hp i.castSucc src hopen
  have hgrid : (tr.states i.castSucc).board.grid src = (tr.states i'.succ).board.grid src :=
    (hall i.castSucc hcyc).1
  -- The arrival is a board move: a drop would glare.
  rcases hmi : tr.moves i' with ⟨src', d', pr⟩ | ⟨pt, d'⟩
  · rw [hmi] at hdi'
    change d' = src at hdi'
    subst hdi'
    have hsng : ¬ tr.GlaresAtEnemyKing kp i'.castSucc src' := fun hg =>
      hngi' (tr.destination_glares_of_source_glares kp ht hs hk hsafe h0 hc i' src' d' pr hmi hg)
    have hdst := tr.boardMove_grid_dst_eq_of_not_glares_of_periodic kp ht hs hk hsafe h0 hc hr hp
      i' src' d' pr hmi hsng
    refine ⟨i', src', pr, hmi, ?_, hsng⟩
    rw [← hdst]
    change (tr.states i'.succ).board.grid d' = some p
    rw [← hgrid]
    exact hpc
  · rw [hmi] at hdi'
    change d' = src at hdi'
    subst hdi'
    exact absurd (tr.dropMove_glares_of_everyMoveChecksOpponent kp ht hs hk hsafe h0 hc i' pt d'
      hmi) hngi'

/-- Under the same premises, the piece a non-glaring move puts on its destination
    leaves it later by a non-glaring board move of the same piece. -/
theorem departure_of_nonGlaring_move_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool) (p : Piece)
    (hm : tr.moves i = .boardMove src dst promote)
    (hpc : (tr.before i).board.grid src = some p)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) :
    ∃ (j : Fin tr.len) (dst' : Pos) (pr : Bool), tr.moves j = .boardMove dst dst' pr ∧
      (tr.before j).board.grid dst = some p ∧ ¬ tr.GlaresAtEnemyKing kp j.castSucc dst := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hngd : ¬ tr.GlaresAtEnemyKing kp i.succ (tr.moves i).destination := by
    rw [hm]
    exact fun hg => hng (tr.glares_source_of_glares_destination_of_periodic kp ht hs hk hsafe h0
      hc hr hp i src dst promote hm hg)
  obtain ⟨j, dst', pr, _, _, hmj, _, _, hall⟩ :=
    tr.openable_glaring_line_cyclic_of_periodic kp ht hs hk hsafe h0 hc hr hp i hngd
  have hmj' : tr.moves j = .boardMove dst dst' pr := by rw [hmj, hm]; rfl
  have hgrid : (tr.states j.castSucc).board.grid dst = (tr.states i.succ).board.grid dst := by
    have h := (hall j.castSucc (cyclicBetween_self_right _ _)).1
    rw [hm] at h
    exact h
  have hngd' : ¬ tr.GlaresAtEnemyKing kp i.succ dst := by
    rw [hm] at hngd
    exact hngd
  have hdst := tr.boardMove_grid_dst_eq_of_not_glares_of_periodic kp ht hs hk hsafe h0 hc hr hp
    i src dst promote hm hng
  have hpd : (tr.states i.succ).board.grid dst = some p := by
    change (tr.after i).board.grid dst = some p
    rw [hdst, hpc]
  refine ⟨j, dst', pr, hmj', ?_, ?_⟩
  · change (tr.states j.castSucc).board.grid dst = some p
    rw [hgrid, hpd]
  · exact fun hg => hngd' ((tr.glaresAtEnemyKing_congr kp ht hgrid
      ((hkp _).trans (hkp _).symm)).mp hg)

/-- Under the same premises, every board move of a non-glaring silver has a reverse
    move of the same silver, from its destination back to its source. -/
theorem silver_move_reverse_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool) (p : Piece)
    (hm : tr.moves i = .boardMove src dst promote)
    (hpc : (tr.before i).board.grid src = some p)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) (hpt : p.pieceType = .silver) :
    ∃ (j : Fin tr.len) (pr : Bool), tr.moves j = .boardMove dst src pr ∧
      (tr.before j).board.grid dst = some p ∧ ¬ tr.GlaresAtEnemyKing kp j.castSucc dst := by
  have hsq := tr.silverSquares_of_nonGlaring_move_of_periodic kp ht hs hk hsafe h0 hc hr hp i src
    dst promote p hm hpc hng hpt
  have hτ : forwardSign p.owner ≠ 0 := by cases p.owner <;> decide
  rcases hsq with ⟨_, hs2, hdq⟩ | ⟨hsq, _, hd2⟩
  · -- From `(σ, 0)` to `(0, τ)`: the silver came to `(σ, 0)` from `(0, τ)`.
    obtain ⟨i', src', pr, hmi', hpi', hngi'⟩ :=
      tr.arrival_of_nonGlaring_move_of_periodic kp ht hs hk hsafe h0 hc hr hp i src dst promote p
        hm hpc hng
    have hsq' := tr.silverSquares_of_nonGlaring_move_of_periodic kp ht hs hk hsafe h0 hc hr hp
      i' src' src pr p hmi' hpi' hngi' hpt
    have hsrc' : src' = dst := by
      rcases hsq' with ⟨_, _, h⟩ | ⟨h, _, _⟩
      · have := congrArg Prod.snd h
        dsimp only at this
        exact absurd (hs2.symm.trans this) (Ne.symm hτ)
      · exact relTo_inj (h.trans hdq.symm)
    subst hsrc'
    exact ⟨i', pr, hmi', hpi', hngi'⟩
  · -- From `(0, τ)` to `(σ, 0)`: the silver leaves `(σ, 0)` toward `(0, τ)`.
    obtain ⟨j, dst', pr, hmj, hpj, hngj⟩ :=
      tr.departure_of_nonGlaring_move_of_periodic kp ht hs hk hsafe h0 hc hr hp i src dst promote
        p hm hpc hng
    have hsq' := tr.silverSquares_of_nonGlaring_move_of_periodic kp ht hs hk hsafe h0 hc hr hp
      j dst dst' pr p hmj hpj hngj hpt
    have hdst' : dst' = src := by
      rcases hsq' with ⟨_, _, h⟩ | ⟨h, _, _⟩
      · exact relTo_inj (h.trans hsq.symm)
      · have := congrArg Prod.snd h
        dsimp only at this
        exact absurd (hd2.symm.trans this) (Ne.symm hτ)
    subst hdst'
    exact ⟨j, pr, hmj, hpj, hngj⟩

end MoveTrace
end MPC
