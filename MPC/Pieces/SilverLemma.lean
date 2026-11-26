import MPC.Pieces.SilverGeometry
/-!
# MPC.Pieces.SilverLemma

The paper's Lemma 5.1 on periodic traces: no silver is moved by a discovered
check. It needs the piece counts (`PieceCountsAtMostTwo`).

By the silver movement lemma, a non-glaring silver of `o` moves only between `a = (σ, 0)` and
`b = (0, τ)` relative to the enemy king `K` (`τ` is `o`'s forward sign), and it
makes both moves `a → b` and `b → a`.

**The king's position.** Before each move `o` is in check. By Corollary 3.4 the
move lands on the checker's square or on its sliding line to `o`'s king `L`
(`checker_cases`). On the board this means: `L` sees the destination along a line
whose first square past the destination is neither the silver's source nor `K`
(both occupied before the move), or an enemy knight on the destination attacks
`L` (the paper's footnote 7) (`CheckerConstraint`). The kings are not adjacent. A
finite case analysis over both moves leaves `L = (2σ, τ)` or `L = (σ, 2τ)`
(`king_position_of_silver`), as in the paper.

**Three rooks.** For `L = (2σ, τ)` take the move `a → b`, and for `L = (σ, 2τ)`
the move `b → a`. Before that move three distinct squares hold a rook or a
dragon:
- the unblocked checker behind the source (Lemma 2.4), sliding along the source's
  line (`source_slider_of_nonGlaring_move`);
- Proposition 3.3's glaring piece behind the destination
  (`destination_slider_of_nonGlaring_move`);
- the enemy checker, which slides along the line from the destination to `L`.
A slider along a rank or file that does not move toward its owner's front is a
rook or a dragon (`rookDragon_of_slideDir`). This contradicts the piece counts
(`not_openableMove_silver_of_periodic`). -/

namespace MPC

namespace MoveTrace

/-- A square holding a rook or a dragon belongs to `rookDragonSquares`. -/
theorem mem_rookDragonSquares_of (tr : MoveTrace) (k : Fin (tr.len + 1)) (q : Pos) (P : Piece)
    (hq : (tr.states k).board.grid q = some P)
    (hP : P.pieceType = .rook ∨ P.pieceType = .dragon) : q ∈ tr.rookDragonSquares k := by
  simp only [rookDragonSquares, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨P, hq, hP⟩

/-- Three distinct rook-or-dragon squares in one state contradict the piece counts. -/
theorem false_of_three_rookDragon (tr : MoveTrace) (hcount : tr.PieceCountsAtMostTwo)
    (k : Fin (tr.len + 1)) (q1 q2 q3 : Pos) (h12 : q1 ≠ q2) (h13 : q1 ≠ q3) (h23 : q2 ≠ q3)
    (h1 : q1 ∈ tr.rookDragonSquares k) (h2 : q2 ∈ tr.rookDragonSquares k)
    (h3 : q3 ∈ tr.rookDragonSquares k) : False := by
  have hsub : ({q1, q2, q3} : Finset Pos) ⊆ tr.rookDragonSquares k := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  have hcard : ({q1, q2, q3} : Finset Pos).card = 3 :=
    Finset.card_eq_three.mpr ⟨q1, q2, q3, h12, h13, h23, rfl⟩
  have := Finset.card_le_card hsub
  have := (hcount k).2
  omega

/-- In a periodic trace satisfying the periodic-check premises, the unblocked checker of a board
    move from a non-glaring square next to the enemy king, along `u`, slides back
    along `u` from at least two squares away. -/
theorem source_slider_of_nonGlaring_move (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hns : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) (u : Dir)
    (hsrc : OnRay (kp 0 (tr.before i).turn.opponent) u 1 src) :
    ∃ (C : Pos) (X : Piece) (n : ℤ), (tr.before i).board.grid C = some X ∧
      X.owner = (tr.before i).turn ∧ OnRay (kp 0 (tr.before i).turn.opponent) u n C ∧
      2 ≤ n ∧ ((-u.1, -u.2) : Dir) ∈ X.pieceType.slideDirs.map (Dir.forPlayer · X.owner) := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hu := tr.unblockedChecker_of_not_glares_source_of_periodic kp ht hs hk hsafe h0 hc hr hp
    i src dst promote hm hns
  rw [hm] at hu
  obtain ⟨C, X, _, _, hXb, _, hXo, hatk, hsrcmem, _, _, _⟩ := hu
  have hXo' : X.owner = (tr.before i).turn := by rw [hXo, Player.opponent_opponent]
  rw [hkp i.succ] at hatk hsrcmem
  have hstep : Pos.dirTo C (kp 0 (tr.before i).turn.opponent) ∉
      X.pieceType.stepDirs.map (Dir.forPlayer · X.owner) := by
    have h := tr.not_stepAttack_of_before kp ht hsafe h0 i C X hXb hXo'
    rw [hkp i.castSucc] at h
    exact h
  obtain ⟨d, n, hC, _, hiff⟩ := ray_of_attack_not_step _ _ _ C _ hatk hstep
  obtain ⟨c, hc1, hcn, hsrcEq⟩ := (hiff _).mp hsrcmem
  obtain ⟨hdu, hc1'⟩ := OnRay.unique ⟨hC.1, by omega, hsrcEq⟩ hsrc
  subst hdu
  have hslide := slideDir_of_attack_not_step _ _ _ C _ hatk hstep hC
  exact ⟨C, X, n, hXb, hXo', hC, by omega, hslide⟩

/-- Under the same premises, Proposition 3.3's glaring piece behind the destination of
    a board move from a non-glaring square, when both ends are next to the enemy king,
    stands on the destination's half-line at least two squares away before the move
    and slides back along it. -/
theorem destination_slider_of_nonGlaring_move (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hns : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) (u v : Dir)
    (hdst : OnRay (kp 0 (tr.before i).turn.opponent) u 1 dst)
    (hsrc : OnRay (kp 0 (tr.before i).turn.opponent) v 1 src) :
    ∃ (B : Pos) (Q : Piece) (m : ℤ), (tr.before i).board.grid B = some Q ∧
      Q.owner = (tr.before i).turn ∧ OnRay (kp 0 (tr.before i).turn.opponent) u m B ∧
      2 ≤ m ∧ ((-u.1, -u.2) : Dir) ∈ Q.pieceType.slideDirs.map (Dir.forPlayer · Q.owner) := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hngd : ¬ tr.GlaresAtEnemyKing kp i.succ (tr.moves i).destination := by
    rw [hm]
    exact fun hg => hns (tr.glares_source_of_glares_destination_of_periodic kp ht hs hk hsafe h0
      hc hr hp i src dst promote hm hg)
  obtain ⟨_, _, _, B, Q, e, b', m, _, hown, hray, hB, hbm, hall⟩ :=
    tr.openable_glaring_ray_cyclic_of_periodic kp ht hs hk hsafe h0 hc hr hp i hngd
  rw [hown] at hray hB
  rw [hm] at hray
  change OnRay _ e b' dst at hray
  obtain ⟨heu, hb1⟩ := OnRay.unique hray hdst
  subst heu
  obtain ⟨hQ1, hgl1⟩ := (hall i.succ (cyclicBetween_self_left _ _)).2
  -- `B` is neither end of the move, so it held `Q` before the move too.
  have hBs : B ≠ src := by
    rintro rfl
    have := (OnRay.unique hB hsrc).2
    omega
  have hBd : B ≠ dst := by
    rintro rfl
    have := (OnRay.unique hB hdst).2
    omega
  have hQb : (tr.before i).board.grid B = some Q := by
    rw [← hQ1]
    exact (tr.boardMove_grid_other ht i src dst promote B hm hBs hBd).symm
  have hstep : Pos.dirTo B (kp 0 (tr.before i).turn.opponent) ∉
      Q.pieceType.stepDirs.map (Dir.forPlayer · Q.owner) := by
    have h := tr.not_stepAttack_of_before kp ht hsafe h0 i B Q hQb hown
    rw [hkp i.castSucc] at h
    exact h
  obtain ⟨Q', hQ', hatkQ⟩ := hgl1
  rw [hQ1] at hQ'
  cases hQ'
  rw [hkp i.succ, show kp 0 Q.owner.opponent = kp 0 (tr.before i).turn.opponent by rw [hown]]
    at hatkQ
  have hslide := slideDir_of_attack_not_step _ _ _ B _ hatkQ hstep hB
  exact ⟨B, Q, m, hQb, hown, hB, by omega, hslide⟩

/-- Under the same premises, before every move the mover is in check, and the move's
    destination lies as in `checker_cases` relative to the checker. -/
theorem checker_before_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) :
    ∃ (C : Pos) (X : Piece), (tr.before i).board.grid C = some X ∧
      X.owner = (tr.before i).turn.opponent ∧
      attacksOriented (tr.before i).board X.owner X.pieceType C (kp 0 (tr.before i).turn) ∧
      ((tr.moves i).destination = C ∨
        ((tr.moves i).destination.toInt ∈ slidePath C (kp 0 (tr.before i).turn) ∧
          Pos.dirTo C (kp 0 (tr.before i).turn) ∉
            X.pieceType.stepDirs.map (Dir.forPlayer · X.owner))) := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  obtain ⟨C, X, hX, hXo, hatk⟩ := tr.inCheck_before_of_periodic kp ht hk hc hp i
  have hcor := tr.destination_on_checker_line kp ht hs hsafe i
    (by rw [hkp i.succ, hkp i.castSucc]) C X hX hXo hatk
  rw [hkp i.castSucc] at hatk hcor
  exact ⟨C, X, hX, hXo, hatk, hcor⟩

/-- The king-separation consequence used by the silver geometry. -/
private theorem kings_far_relative (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (o : Player) (K L : Pos) (hKdef : K = kp 0 o.opponent) (hLdef : L = kp 0 o) :
    ¬ (-1 ≤ (relTo K L).1 ∧ (relTo K L).1 ≤ 1 ∧ -1 ≤ (relTo K L).2 ∧
      (relTo K L).2 ≤ 1) := by
  rintro ⟨h1, h2, h3, h4⟩
  have hLK : L ≠ K := by
    intro h
    have hL := (hk 0).king_present o
    have hK := (hk 0).king_present o.opponent
    rw [← hKdef, ← h, hLdef, hL] at hK
    cases o <;> cases hK
  have hne : ¬ ((relTo K L).1 = 0 ∧ (relTo K L).2 = 0) := by
    rintro ⟨e1, e2⟩
    apply hLK
    apply relTo_inj
    rw [show relTo K K = (0, 0) by simp [relTo]]
    exact Prod.ext e1 e2
  have hstep : Pos.dirTo L K ∈ PieceType.king.stepDirs := by
    rw [PieceType.mem_king_stepDirs_iff]
    have e1 : (Pos.dirTo L K).1 = -(relTo K L).1 := by
      simp only [Pos.dirTo, relTo, Pos.toInt]
      ring
    have e2 : (Pos.dirTo L K).2 = -(relTo K L).2 := by
      simp only [Pos.dirTo, relTo, Pos.toInt]
      ring
    rw [e1, e2]
    omega
  have hmap : ∀ d ∈ PieceType.king.stepDirs,
      d ∈ PieceType.king.stepDirs.map (Dir.forPlayer · o) := by
    cases o <;> decide
  apply tr.kings_not_adjacent kp hk hsafe h0 0 o
  rw [← hLdef, ← hKdef]
  exact Or.inl (hmap _ hstep)

/-- Lemma 5.1: in a periodic mutual-check trace with the piece counts, no silver
    is moved by a discovered check. -/
theorem not_openableMove_silver_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (hcount : tr.PieceCountsAtMostTwo) (o : Player) : ¬ tr.OpenableMoveBy kp o .silver := by
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, _, _⟩ := hm
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  rintro ⟨i, src, dst, promote, hturn, hmv, hsrc, hng, _⟩
  -- Notation: the silver `p`, the kings `K` and `L`, and `o`'s forward sign `τ`.
  obtain ⟨K, hKdef⟩ : ∃ K, K = kp 0 o.opponent := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = kp 0 o := ⟨_, rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = forwardSign o := ⟨_, rfl⟩
  have hτ : τ = 1 ∨ τ = -1 := hτdef ▸ forwardSign_cases o
  let p : Piece := ⟨o, .silver⟩
  have hsq := tr.silverSquares_of_nonGlaring_move_of_periodic kp ht hs hk hsafe h0 hc hr hp i src
    dst promote p hmv hsrc hng rfl
  obtain ⟨j, pr, hmj, hpj, hngj⟩ := tr.silver_move_reverse_of_periodic kp ht hs hk hsafe h0 hc hr
    hp i src dst promote p hmv hsrc hng rfl
  -- The two squares `a = (σ, 0)` and `b = (0, τ)`, and the moves `a → b` and `b → a`.
  obtain ⟨σ, a, b, iA, iB, prA, prB, hσ, ha, hb, hmA, hpA, hngA, hmB, hpB, hngB⟩ :
      ∃ (σ : ℤ) (a b : Pos) (iA iB : Fin tr.len) (prA prB : Bool), (σ = 1 ∨ σ = -1) ∧
        relTo K a = (σ, 0) ∧ relTo K b = (0, τ) ∧
        tr.moves iA = .boardMove a b prA ∧ (tr.before iA).board.grid a = some p ∧
        ¬ tr.GlaresAtEnemyKing kp iA.castSucc a ∧
        tr.moves iB = .boardMove b a prB ∧ (tr.before iB).board.grid b = some p ∧
        ¬ tr.GlaresAtEnemyKing kp iB.castSucc b := by
    change SilverSquares o (relTo (kp 0 o.opponent) src) (relTo (kp 0 o.opponent) dst) at hsq
    rw [← hKdef] at hsq
    unfold SilverSquares at hsq
    rw [← hτdef] at hsq
    rcases hsq with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact ⟨(relTo K src).1, src, dst, i, j, promote, pr, h1, by rw [← h2], h3, hmv, hsrc, hng,
        hmj, hpj, hngj⟩
    · exact ⟨(relTo K dst).1, dst, src, j, i, pr, promote, h2, by rw [← h3], h1, hmj, hpj, hngj,
        hmv, hsrc, hng⟩
  have hturnOf : ∀ (k : Fin tr.len) (s d : Pos) (pr : Bool), tr.moves k = .boardMove s d pr →
      (tr.before k).board.grid s = some p → (tr.before k).turn = o := by
    intro k s d pr hmk hpk
    obtain ⟨piece, hpiece, ho⟩ := hs k s d pr hmk
    rw [hpk] at hpiece
    cases hpiece
    exact ho.symm
  have htA := hturnOf iA a b prA hmA hpA
  have htB := hturnOf iB b a prB hmB hpB
  have hKocc : ∀ k : Fin (tr.len + 1), (tr.states k).board.grid K ≠ none := by
    intro k
    rw [hKdef, ← hkp k, (hk k).king_present]
    exact Option.some_ne_none _
  -- Corollary 3.4 at both moves.
  have hCA := tr.checker_before_of_periodic kp ht hs hk hsafe h0 hc hr hp iA
  have hCB := tr.checker_before_of_periodic kp ht hs hk hsafe h0 hc hr hp iB
  rw [htA, hmA, ← hLdef] at hCA
  rw [htB, hmB, ← hLdef] at hCB
  obtain ⟨CA, XA, hXA, hXAo, hatkA, hDA⟩ := hCA
  obtain ⟨CB, XB, hXB, hXBo, hatkB, hDB⟩ := hCB
  have hτX : ∀ X : Piece, X.owner = o.opponent → -forwardSign X.owner = τ := by
    intro X hX
    rw [hX, forwardSign_opponent, neg_neg, hτdef]
  have hconA := checkerConstraint_of_checker _ XA CA L b a K hatkA hDA
    (by rw [hpA]; exact Option.some_ne_none _) (hKocc iA.castSucc)
  have hconB := checkerConstraint_of_checker _ XB CB L a b K hatkB hDB
    (by rw [hpB]; exact Option.some_ne_none _) (hKocc iB.castSucc)
  rw [hτX XA hXAo, hb, ha] at hconA
  rw [hτX XB hXBo, ha, hb] at hconB
  -- The kings are not adjacent.
  have hfar := tr.kings_far_relative kp hk hsafe h0 o K L hKdef hLdef
  have hpos := king_position_of_silver τ σ hτ hσ (relTo K L) hconA hconB hfar
  -- Facts used in both cases.
  have hRD : ∀ (k : Fin (tr.len + 1)) (q : Pos) (P : Piece) (sd : Dir),
      (tr.states k).board.grid q = some P →
      sd ∈ P.pieceType.slideDirs.map (Dir.forPlayer · P.owner) → (sd.1 = 0 ∨ sd.2 = 0) →
      sd ≠ (0, forwardSign P.owner) → q ∈ tr.rookDragonSquares k :=
    fun k q P sd hq h1 h2 h3 =>
      tr.mem_rookDragonSquares_of k q P hq (rookDragon_of_slideDir _ _ sd h1 h2 h3)
  have hσK : ((σ, 0) : Dir) ∈ PieceType.king.stepDirs := by
    rcases hσ with rfl | rfl <;> decide
  have hτK : ((0, τ) : Dir) ∈ PieceType.king.stepDirs := by
    rcases hτ with rfl | rfl <;> decide
  have hrayA : OnRay K (σ, 0) 1 a := OnRay.of_relTo hσK one_pos (by rw [ha]; simp)
  have hrayB : OnRay K (0, τ) 1 b := OnRay.of_relTo hτK one_pos (by rw [hb]; simp)
  have hKA : kp 0 (tr.before iA).turn.opponent = K := by rw [htA, hKdef]
  have hKB : kp 0 (tr.before iB).turn.opponent = K := by rw [htB, hKdef]
  have hrel : ∀ {q q' : Pos}, q = q' → relTo K q = relTo K q' := fun h => by rw [h]
  rcases hpos with hL | hL
  · -- `L = (2σ, τ)`: three rooks or dragons before the move `a → b`.
    obtain ⟨C1, X1, n1, hX1, hX1o, hC1, hn1, hsl1⟩ :=
      tr.source_slider_of_nonGlaring_move kp ht hs hk hsafe h0 hc hr hp iA a b prA hmA hngA
        (σ, 0) (by rw [hKA]; exact hrayA)
    obtain ⟨B2, Q2, m, hQ2, hQ2o, hB2, hm2, hsl2⟩ :=
      tr.destination_slider_of_nonGlaring_move kp ht hs hk hsafe h0 hc hr hp iA a b prA hmA hngA
        (0, τ) (σ, 0) (by rw [hKA]; exact hrayB) (by rw [hKA]; exact hrayA)
    rw [hKA] at hC1 hB2
    dsimp only at hsl1 hsl2
    simp only [neg_zero] at hsl1 hsl2
    have hbL : OnRay L (-σ, 0) 2 b := by
      refine ⟨neg_mem_king_stepDirs hσK, two_pos, ?_⟩
      have e1 := congrArg Prod.fst hb
      have e2 := congrArg Prod.snd hb
      have f1 := congrArg Prod.fst hL
      have f2 := congrArg Prod.snd hL
      simp only [relTo] at e1 e2 f1 f2
      ext <;> dsimp only <;> linarith
    rcases checker_cases _ XA CA L b hatkA hDA with ⟨hbC, hst⟩ | ⟨d, n, c, hCa, hc1, hcn, hDe,
        hsl3, _⟩
    · -- A step from `b` reaches `L` only if `L - b` is a step.
      subst hbC
      exfalso
      have hd : Pos.dirTo b L = (2 * σ, 0) := by
        have e1 := congrArg Prod.fst hb
        have e2 := congrArg Prod.snd hb
        have f1 := congrArg Prod.fst hL
        have f2 := congrArg Prod.snd hL
        simp only [relTo, Pos.toInt] at e1 e2 f1 f2
        simp only [Pos.dirTo]
        ext <;> dsimp only <;> linarith
      rw [hd] at hst
      rcases stepDir_unit_or_forward_knight _ _ _ hst with hu | ⟨_, h2⟩
      · rw [PieceType.mem_king_stepDirs_iff] at hu
        dsimp only at hu
        omega
      · rw [hXAo, forwardSign_opponent, ← hτdef] at h2
        dsimp only at h2
        omega
    · obtain ⟨hd, hc⟩ := OnRay.unique ⟨hCa.1, by omega, hDe⟩ hbL
      subst hd
      dsimp only at hsl3
      simp only [neg_neg, neg_zero] at hsl3
      have hCA_rd := hRD _ CA XA (σ, 0) hXA hsl3 (Or.inr rfl)
        (by intro h; have := congrArg Prod.fst h; dsimp only at this; omega)
      have hC1_rd := hRD _ C1 X1 (-σ, 0) hX1 hsl1 (Or.inr rfl)
        (by intro h; have := congrArg Prod.fst h; dsimp only at this; omega)
      have hB2_rd := hRD _ B2 Q2 (0, -τ) hQ2 hsl2 (Or.inl rfl)
        (by rw [hQ2o, htA, ← hτdef]; intro h; have := congrArg Prod.snd h; dsimp only at this;
            omega)
      have rC1 := hC1.relTo_eq
      have rB2 := hB2.relTo_eq
      have rCA : relTo K CA = ((relTo K L).1 + n * -σ, (relTo K L).2 + n * 0) := by
        obtain ⟨_, _, hCe⟩ := hCa
        simp only [relTo, hCe]
        ext <;> dsimp only <;> ring
      rw [hL] at rCA
      apply tr.false_of_three_rookDragon hcount iA.castSucc C1 B2 CA ?_ ?_ ?_ hC1_rd hB2_rd
        hCA_rd
      · intro h
        have := hrel h
        rw [rC1, rB2] at this
        have := congrArg Prod.snd this
        dsimp only at this
        rcases hτ with rfl | rfl <;> omega
      · intro h
        have := hrel h
        rw [rC1, rCA] at this
        have := congrArg Prod.snd this
        dsimp only at this
        rcases hτ with rfl | rfl <;> omega
      · intro h
        have := hrel h
        rw [rB2, rCA] at this
        have := congrArg Prod.snd this
        dsimp only at this
        rcases hτ with rfl | rfl <;> omega
  · -- `L = (σ, 2τ)`: three rooks or dragons before the move `b → a`.
    obtain ⟨C1, X1, n1, hX1, hX1o, hC1, hn1, hsl1⟩ :=
      tr.source_slider_of_nonGlaring_move kp ht hs hk hsafe h0 hc hr hp iB b a prB hmB hngB
        (0, τ) (by rw [hKB]; exact hrayB)
    obtain ⟨B2, Q2, m, hQ2, hQ2o, hB2, hm2, hsl2⟩ :=
      tr.destination_slider_of_nonGlaring_move kp ht hs hk hsafe h0 hc hr hp iB b a prB hmB hngB
        (σ, 0) (0, τ) (by rw [hKB]; exact hrayA) (by rw [hKB]; exact hrayB)
    rw [hKB] at hC1 hB2
    dsimp only at hsl1 hsl2
    simp only [neg_zero] at hsl1 hsl2
    have haL : OnRay L (0, -τ) 2 a := by
      refine ⟨neg_mem_king_stepDirs hτK, two_pos, ?_⟩
      have e1 := congrArg Prod.fst ha
      have e2 := congrArg Prod.snd ha
      have f1 := congrArg Prod.fst hL
      have f2 := congrArg Prod.snd hL
      simp only [relTo] at e1 e2 f1 f2
      ext <;> dsimp only <;> linarith
    rcases checker_cases _ XB CB L a hatkB hDB with ⟨haC, hst⟩ | ⟨d, n, c, hCa, hc1, hcn, hDe,
        hsl3, _⟩
    · subst haC
      exfalso
      have hd : Pos.dirTo a L = (0, 2 * τ) := by
        have e1 := congrArg Prod.fst ha
        have e2 := congrArg Prod.snd ha
        have f1 := congrArg Prod.fst hL
        have f2 := congrArg Prod.snd hL
        simp only [relTo, Pos.toInt] at e1 e2 f1 f2
        simp only [Pos.dirTo]
        ext <;> dsimp only <;> linarith
      rw [hd] at hst
      rcases stepDir_unit_or_forward_knight _ _ _ hst with hu | ⟨h1, _⟩
      · rw [PieceType.mem_king_stepDirs_iff] at hu
        dsimp only at hu
        rcases hτ with rfl | rfl <;> omega
      · dsimp only at h1
        omega
    · obtain ⟨hd, hc⟩ := OnRay.unique ⟨hCa.1, by omega, hDe⟩ haL
      subst hd
      dsimp only at hsl3
      simp only [neg_neg, neg_zero] at hsl3
      have hCB_rd := hRD _ CB XB (0, τ) hXB hsl3 (Or.inl rfl)
        (by rw [hXBo, forwardSign_opponent, ← hτdef]; intro h; have := congrArg Prod.snd h;
            dsimp only at this; rcases hτ with rfl | rfl <;> omega)
      have hC1_rd := hRD _ C1 X1 (0, -τ) hX1 hsl1 (Or.inl rfl)
        (by rw [hX1o, htB, ← hτdef]; intro h; have := congrArg Prod.snd h; dsimp only at this;
            rcases hτ with rfl | rfl <;> omega)
      have hB2_rd := hRD _ B2 Q2 (-σ, 0) hQ2 hsl2 (Or.inr rfl)
        (by intro h; have := congrArg Prod.fst h; dsimp only at this; rcases hσ with rfl | rfl <;>
            omega)
      have rC1 := hC1.relTo_eq
      have rB2 := hB2.relTo_eq
      have rCB : relTo K CB = ((relTo K L).1 + n * 0, (relTo K L).2 + n * -τ) := by
        obtain ⟨_, _, hCe⟩ := hCa
        simp only [relTo, hCe]
        ext <;> dsimp only <;> ring
      rw [hL] at rCB
      apply tr.false_of_three_rookDragon hcount iB.castSucc C1 B2 CB ?_ ?_ ?_ hC1_rd hB2_rd
        hCB_rd
      · intro h
        have := hrel h
        rw [rC1, rB2] at this
        have := congrArg Prod.fst this
        dsimp only at this
        rcases hσ with rfl | rfl <;> omega
      · intro h
        have := hrel h
        rw [rC1, rCB] at this
        have := congrArg Prod.fst this
        dsimp only at this
        rcases hσ with rfl | rfl <;> omega
      · intro h
        have := hrel h
        rw [rB2, rCB] at this
        have := congrArg Prod.fst this
        dsimp only at this
        rcases hσ with rfl | rfl <;> omega

end MoveTrace
end MPC
