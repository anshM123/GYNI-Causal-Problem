# S2 — Quantum networks, causal structures, indefinite causal order, real vs complex QT, QRFs

Literature scout report, 2026-09-27. Scope: which OPEN problems in this area admit a POSITIVE result (construction / exact value / improved bound / new certified nonclassicality) that one researcher could reach in 1–5 days on an RTX 5070 Ti (12 GB), 24-core i9, 32 GB RAM, Python + cvxpy (SCS/Clarabel, no MOSEK) + `inflation` package + exact arithmetic.

Citation policy: arXiv IDs below were all seen directly (arXiv abstract pages, arXiv listings, or the PDFs, which were downloaded and read). Anything not seen directly is marked "(ID unverified)". Numbers quoted from papers were read in the PDF text unless flagged otherwise.

---

## 0. Status of the seed questions (read this first)

| Seed question | Status (2026-09-27) | Key source |
|---|---|---|
| Triangle network, no inputs, binary outputs: any quantum nonlocality? | **SOLVED (May 2026).** The noisy-W family `W_v = (v/3)([001]+[010]+[100]) + (1-v)/8` is proven nonlocal at v ∈ {0.622070, 0.623250, 0.623875, 0.624500}. The proof uses level-3 classical inflation (3 copies per source, 2^27 events, exploiting party-permutation symmetry). An explicit quantum model reproduces W_v for all v ≤ 0.6245: one entangled source `|ω>=cosω|00>−sinω|11>` plus a classical coin, and two classical 1-bit sources. A local model is known for v ≤ 0.5966. W_v is not realizable, even post-quantumly, for v > 3(2−√3) ≈ 0.8038. As a corollary, (2,2,3), (2,2,4), (3,3,2) etc. are also settled. | Don, Bavaresco, Lipka-Bartosik, Gisin, Brunner, Pozas-Kerstjens, arXiv:2605.00981; da Silva, Pozas-Kerstjens, Parisio, arXiv:2503.16654 (PRA 112, L030403 (2025)) |
| Earlier "best evidence" (Boreiri et al.) | 3-3-3 and 3-3-2 examples via PTC rigidity. Now superseded. | arXiv:2207.08532 (PRA 107, 062413 (2023)) |
| EJM distribution in the triangle: rigorously nonclassical? | **SOLVED (Oct 2025).** The proof uses a (2,2,4) inflation with symmetry reduction, a Frank–Wolfe polytope-membership solver and an exact-integer certificate. Finding the certificate took about 5 days on 12 cores with about 50 GB RAM (ETH Euler); checking it takes 20 s on a laptop. In the "purified-EJM" family `p_v = v·p_pure + (1−v)/64` (EJM ↔ v = 0.75) they obtain 3/7 ≤ v* < 383/512 ≈ 0.748, which means **essentially zero noise tolerance (about 0.27% white noise)**. Their own conclusion says noisy EJM "remains difficult" and needs much larger inflations. Code: github.com/vgitton/fast-inflation. | Gitton & Renner, arXiv:2510.15143 |
| Henson–Lal–Pusey open causal structures (≤ 6 nodes) | **CLOSED (Dec 2025).** The last open structure also has a classical–quantum gap. | Khanna, Pusey, Colbeck, arXiv:2512.04058 |
| Evans / "Unrelated Confounders" (UC) scenario | **SOLVED (2024).** Quantum nonclassicality with three dichotomic variables. Observational critical visibility is ≈ 0.98873; with interventions it is ≈ 0.87743. An experiment using interventions followed in Aug 2026. Observational robustness is still very poor (→ S2-04). | Lauand, Poderini, Rabelo, Chaves, arXiv:2404.12790; earlier arXiv:2211.13349 (PRX Quantum 4, 020311 (2023)); experiment Xiao et al., arXiv:2608.03552 |
| Causal inequalities: exact maximal violations | OCB: exact, equal to the CHSH-Tsirelson analogue (2+√2)/4. LGYNI: exact, ≈ 0.8194 (achieved with qubits). **GYNI: OPEN. The best known value is ≥ 0.6219 (seesaw, d = 6,7), and the upper bound is 0.7592.** Stated as open in Liu–Chiribella, in the June-2026 review, and in the June-2026 GPU paper (→ S2-01). | Liu & Chiribella, arXiv:2403.02749 (Nat. Commun. 2025); Boghiu & Simonov, arXiv:2606.20519; Costa, Rubino, Branciard, Brukner, Quintino (review), arXiv:2606.19438 |
| Liu–Chiribella SDP hierarchy | Only "level 1" exists. Higher levels are explicitly open. Boghiu & Simonov suggest the block-matrix relaxation of D'Alessandro, Roch i Carceller & Tavakoli (arXiv:2603.19388, PRX 2026) as a route, but nothing has been implemented. | as above |
| Quantum switch / higher-order advantages | Two-use unitary discrimination: ICO advantage **conjectured impossible** (arXiv:2105.13369). Asymptotic (Stein) channel discrimination: shown that parallel = adaptive = general (Zhu & Wang, arXiv:2609.30268, Sep 2026). Group-action estimation: no ICO advantage (arXiv:2501.09312, Quantum 2025). Isolated-switch DI certification via fixed-order inequalities: open, but likely negative (see AVOID). | — |
| Real vs complex QT | Star-network gap grows linearly in N (Sarkar, Trillo, Renou, Augusiak, arXiv:2503.09724, Rep. Prog. Phys. 89, 070503 (2026)). Partial independence suffices (Weilenmann, Gisin, Sekatski, arXiv:2502.20102). Efficient test, real 14.69 vs complex 18 (Batle et al., arXiv:2405.03013, Quantum 9, 1595 (2025)). Communication advantage (Elliott, arXiv:2505.16523). **Contested:** Hoffreumon & Woods (arXiv:2603.19208) argue RQT cannot be falsified once independence is defined operationally; Maioli, Curado, Gazeau (arXiv:2604.19482). The ICO real–complex "reversal" (Surace, Minagawa, Kunjwal, arXiv:2605.30238) was flagged as flawed by its authors. **Tightness of the original real bound T ≲ 7.6605 was left open by Renou et al. and is still open** (→ S2-06). Complex self-testing: Chen, Mančinska, Volčič, arXiv:2512.07160. | — |
| Network-compatible states | Pure 3-qubit triangle compatibility is fully classified (Smith, Wolfe, Spekkens, arXiv:2501.12320, PRX Quantum 7, 010351 (2026)). GHZ fidelity in the triangle LOSR network: 0.548 < F < 0.618 (→ S2-07). | Neumann et al., arXiv:2503.09473; Zhou et al., arXiv:2503.09480 |
| Quantum reference frames | 2025–26 work is conceptual (perspective-neutral, groupoid and "beyond subsystems" frameworks). No computational open problem with a positive endpoint was identified, so there is **no QRF candidate**. | — |

IQOQI Open Quantum Problems wiki (https://oqp.iqoqi.oeaw.ac.at) returned HTTP 500 on every attempt, so it could not be consulted.

---

## 1. Candidates

### S2-01 — Better (or exact) Tsirelson bound for the bipartite GYNI causal inequality

**Question.** The setting is bipartite process matrices W of any finite dimension with local quantum instruments. Inputs x, y ∈ {0,1} are uniform and outputs a, b ∈ {0,1}. Determine
`I*_GYNI = sup (1/4) Σ_{x,y} P(a=y, b=x | x,y)`. The causal bound is 1/2.

**Closest known results**
- **Lower bounds (seesaw)** from Boghiu & Simonov, arXiv:2606.20519 (June 2026):
  - d=2: 0.5694; d=3: 0.6104; d=4: 0.6217; d=5: 0.6218; d=6, 7: 0.6219; d=8: 0.62189.
  - This took about one month of wall-clock time per dimension on MareNostrum5, using a custom GPU-accelerated SCS.
  - Their verdict: gains are "marginal beyond d=5". It remains unclear whether the gap is intrinsic or reflects weak relaxations.
- **Upper bounds**
  - `p ≤ 1 − 1/(d_I d_O + 1)`, dimension dependent (Bavaresco et al. 2019, as cited in review arXiv:2606.19438; ID unverified).
  - GYNI cannot be won perfectly even in infinite dimension (Kunjwal & Oreshkov 2023, per the review; ID unverified).
  - **Dimension-free 0.7592** (Liu & Chiribella, arXiv:2403.02749). It comes from decomposing GYNI into single-trigger pieces and summing their exact single-trigger values `2^{Dmax(M*_I || NoSig)}`. Because each piece is optimized independently, the bound is structurally loose.
- **Explicit open-problem statements**
  - Liu–Chiribella: "finding the exact value of I_GYNI remains an open problem"; "our SDP relaxation may be just the first level of a similar hierarchy … among the most important research directions".
  - Review arXiv:2606.19438: "possibly not tight".
  - Boghiu–Simonov: "developing stronger relaxations … is an important open problem".

**Precise gap.** [0.6219, 0.7592], width ≈ 0.137. The saturation of the seesaw values suggests the true value is ≈ 0.622.

**Method and first experiment**
1. **Reproduce (half a day).** Re-implement the LC SDPs in cvxpy with Clarabel. Check LGYNI → 0.8194 (single-trigger, exact) and GYNI → 0.7592 (minimum over single-trigger decompositions).
2. **Tighten.** Three routes, possibly combined:
   - (a) A *joint* relaxation in which the single-trigger pieces must share one underlying process and instrument family. Couple the per-piece Choi variables through common marginals and consistency constraints, instead of summing independent maxima.
   - (b) An NPA / block-moment relaxation of the representation `p(a,b|x,y) = d_AO·d_BO·Tr[ρ (M_{a|x} ⊗ N_{b|y})]` with `ρ = W/(d_AO d_BO)`. Sanity check: plain "post-selected Bell with constant success probability" is useless, because a classical post-selection strategy wins GYNI perfectly with success probability 1/4 for all x, y. The strength must therefore come from adding the instrument constraints `Σ_a Tr_{A_O} M_{a|x} = 1_{A_I}` and the process-validity constraints as localizing constraints (D'Alessandro–Roch i Carceller–Tavakoli style, arXiv:2603.19388).
   - (c) Symmetry reduction under the GYNI group (party swap and relabelings).
3. **Side deliverables**
   - A certified qubit value (d = 2), using a dimension-constrained relaxation.
   - Structured lower-bound constructions (coherent control of classical process functions, time-delocalized constructions) instead of generic seesaw.

**Compute.** The LC SDP works on operators of dimension ∏ m_i n_i = 16, which is tiny. Level-2-type moment matrices would be of size ~10²–10³, taking seconds to minutes in Clarabel/SCS; 32 GB is ample. Do not redo the high-dimensional seesaw (a month per dimension on an HPC system).

**Most plausible positive route.** Any rigorous dimension-free bound < 0.7592 (e.g., ≤ 0.70) is publishable. Approaching 0.622 would essentially settle a problem stated in a Nat. Commun. paper and a 2026 review.

- **Difficulty:** 4/5.
- **Importance:** 4/5. Venue: Quantum/PRA for an improved bound; PRL/Nat. Commun. if closed. The topic sits at the IQOQI-Vienna core (Brukner process-matrix line).
- **Novelty risk:** medium.
  - Checked: arXiv listing for "causal inequality/inequalities" (48 hits, newest 2026-09-19); searches for "GYNI 0.7592", "Liu Chiribella hierarchy second level", "block-moment"; the June-2026 review.
  - Latest related papers: Boghiu & Simonov (2026-06-18, lower bounds only) and the review (2026-06-17). No improved upper bound found.
  - Two 2026 abstracts touching causal constraints/structure, arXiv:2609.22998 and arXiv:2607.15345, give no GYNI bounds.
  - Risk: the GPU-paper authors may pursue block-matrix relaxations.
- **Probability of a meaningful positive advance in 1–5 days:** 25% for an improved bound; about 5% for essentially closing the gap.

---

### S2-02 — Noise-robust quantum nonlocality in the binary-output triangle (widen the 0.622–0.6245 window)

**Question.** (i) Find a quantum triangle distribution p(a,b,c) with a, b, c ∈ {0,1} and no inputs, together with an exact-arithmetic certificate that `(1−ε)p + ε/8` is not triangle-local, for ε as large as possible. The current best is ε ≈ 0.4%: the W-model at v = 0.6245 can only be diluted down to the certified v = 0.62207. (ii) Relatedly, determine `v_Q = max{v : W_v is quantum-realizable}`. Currently 0.6245 ≤ v_Q ≤ 0.8038.

**Closest known results**
- **Don et al., arXiv:2605.00981**
  - Nonlocality is proven only at 4 discrete v. Non-convexity blocks interval statements.
  - Their tester seesaw (Eqs. 4–6: states and measurements merged into "testers" satisfying SDP constraints) found realizations up to v = 0.6245 only; beyond that the distance to the target grows linearly.
  - The quantum model uses one entangled source and two classical bits. It is "minimally network nonclassical" but NOT fully network nonlocal.
  - Local models exist for v ≤ 0.5966 (arXiv:2503.16654).
- **Other triangle distributions**
  - Robust proofs for 4-outcome triangle distributions tolerate ≈ 0.5% white noise and ≈ 80% dephasing (Boreiri, Ulu, Brunner, Sekatski, arXiv:2311.02182, Quantum 2025).
  - EJM tolerates ≈ 0.27% (arXiv:2510.15143).
  - Bell-embedding (Fritz-type) proofs are far more robust: 10% loss certified with N00N states (Kriváchy & Kerschbaumer, arXiv:2503.24213, PRL 135, 160803 (2025)). Binary outputs exclude such input-revealing embeddings.
  - "Genuine" triangle experiments still rely on conjectured inequalities or neural-network (ML) evidence: arXiv:2401.15428, and arXiv:2501.08079 (a layered local-hidden-variable neural network, "LHV-Net"; visibility threshold 0.94).

**Precise gap.**
- Certified robustness in the binary triangle is ~0.4%.
- v_Q is known only to lie in [0.6245, 0.8038].
- There are no fully or genuinely network-nonlocal binary examples. Don et al. list this explicitly as open.

**Method and first experiment**
1. Implement the tester seesaw with larger tester dimensions (qutrit/ququart local spaces, all three sources quantum) and many random restarts. Target (a) W_v with v > 0.6245, and (b) maximization of a fixed polynomial witness.
2. Inflation.
   - Level 2 (2 copies per source): 12 binary variables, 4096 events.
   - Level 3 with symmetry: 27 binary variables, 2^27 ≈ 1.3×10^8 events. Under S3 party symmetry × (S3)^3 copy symmetry this reduces to ≈ 1×10^5 orbits.
   - Tools: the `inflation` package or Gitton's fast-inflation (Frank–Wolfe polytope-membership formulation).
   - Extract the dual certificate and verify it in exact rational arithmetic.
3. Inflation-guided quantum search: dual certificate → witness (polynomial if LPI constraints are avoided) → maximize over testers → re-solve the LP → iterate.

**Compute.**
- Level-2 LP: trivial.
- Level-3 symmetric LP: ~10^5 variables. Orbit enumeration in C takes minutes; the LP is feasible in 32 GB with HiGHS or a first-order/Frank–Wolfe solver.
- Tester SDPs: < 100×100.
- Overall feasible, as long as the full 2^27 space is never materialized in Python.

**Most plausible positive route.**
- A quantum realization of W_v at v ≈ 0.63–0.65, certified at that v. This widens the window 3–10×, to about 1–4% white noise.
- Or a different binary family, e.g. with three quantum sources, that remains certifiable at larger noise.
- Extension: the first binary example of full network nonlocality, using an inflation with one source classical and the others quantum/NS.

- **Difficulty:** 4.
- **Importance:** 4 (the minimal network-nonlocality scenario made experimentally relevant). Venue: PRL / PRX Quantum / Quantum.
- **Novelty risk:** moderate-high. Don et al. announce a forthcoming paper on the tester method (their Ref. [37]). arXiv listings "triangle network nonlocality" (21 hits) and "triangle network binary outputs" (5 hits) show no follow-up as of 2026-09-27. Newest related: arXiv:2609.11451 (Sep 2026, variational certification with the wagon-wheel inequality; not binary triangle).
- **Probability:** 20%.

---

### S2-03 — Analytic (polynomial) Bell inequality for binary-triangle quantum nonlocality, toward the exact W-family threshold

**Question.**
- Give an explicit polynomial inequality F(p) ≤ 0, valid for all triangle-local binary distributions and violated by some quantum distribution.
- Don et al. ask for exactly this: "derive a fully analytical proof … by deriving an appropriate Bell-like inequality". Their LPs contain linearized polynomial identification (LPI) constraints, so the dual certificates cannot be read as Bell inequalities.
- **Stretch goal:** prove one of the tight inequalities conjectured by da Silva–Pozas-Kerstjens–Parisio for the permutation-symmetric binary triangle. That would give nonlocality of W_v for all v ∈ (0.5966, 0.6245], a window about 10× wider, and fix the exact local threshold at 0.5966.

**Closest known results.**
- arXiv:2503.16654: exhaustive local-model search, analytic boundary curves conjectured to be all the tight inequalities. Code: github.com/mariofilho281/symmetric_triangle.
- arXiv:2605.00981: numerical, LPI-based certificates only.
- Classical W-type inflation inequalities (Wolfe–Spekkens–Fritz) are far too weak for quantum points.

**Gap.** No human-checkable witness of binary-triangle quantum nonlocality exists. The region v ∈ (0.5966, 0.62207) is undecided.

**Method.**
1. Re-run level-3 inflation using only certificate-type constraints (injectable/expressible sets, no LPI). If the quantum point is still excluded, the Farkas dual is a polynomial inequality: rationalize it, compress it by symmetry, and verify it exactly.
2. If that relaxation is too weak, use tailored non-fan-out sub-inflations (cut/spiral/web) restricted to the symmetric subspace.
3. For the exact threshold, try to prove the conjectured boundary. Options: combine the parity-token-counting (PTC)-style rigidity of Boreiri et al. with inflation constraints, or use a monotone-path argument along the W line (non-convexity makes this delicate).

**Compute.** Same as S2-02. Exact verification of a certificate with ~10^5 rational coefficients is fine.

**Positive route.** The first analytic Bell-type inequality for the minimal network scenario, with an explicit quantum violation.

- **Difficulty:** 4–5.
- **Importance:** 4.
- **Novelty risk:** moderate (same groups).
- **Probability:** 15% for an analytic inequality; below 5% for the exact threshold.

---

### S2-04 — Noise-robust, purely observational nonclassicality in the dichotomic Unrelated-Confounders (Evans) scenario

**Question.** The UC DAG is A←γ→B←α→C with direct edges B→A and B→C; all variables are binary and there are no inputs. Classically,
`P(a,b,c) = Σ P(α)P(γ)P(a|b,γ)P(b|α,γ)P(c|b,α)`.
Find quantum strategies (two independent bipartite sources, B's binary POVM, A and C measuring conditioned on b) together with certified classical-incompatibility witnesses. The goal is the lowest critical visibility under isotropic source noise, **using observational data only**.

**Closest known results.**
- Lauand et al. (arXiv:2404.12790) give a concave observational inequality with v_crit ≈ 0.98873, and a hybrid observational-interventional one with v_crit ≈ 0.87743. Numerical optimality is claimed only for two-qubit states and those specific inequalities.
- The Evans/UC question was open in arXiv:2211.13349.
- Experiment with interventions and causal data fusion: Xiao et al., arXiv:2608.03552 (Aug 2026).
- Networks with measurement dependence and non-binary central outcomes: Chaves et al., arXiv:2105.05721 (PRX Quantum 2, 040323 (2021)).

**Gap.** Only one family of observational inequalities is known. The binary UC local set has not been characterized. Observational robustness is ~1%.

**Method.**
1. Map the local set: parametrize local models with bounded latent cardinalities and trace the boundary, as da Silva et al. did for the triangle.
2. Outer approximations: inflation LPs (2 copies per source) → polynomial witnesses. Check that the `inflation` package handles observed-to-observed edges; a custom LP is easy otherwise.
3. Quantum seesaw over non-maximally entangled / higher-dimensional sources, B's POVM and the conditioned measurements; maximize the noise tolerance of the best witness.
4. Exact rational certificate.

**Compute.** Tiny: 8 probabilities; LPs of 10^3–10^5 variables; SDPs < 50×50. Very feasible.

**Positive route.** A new inequality with observational v_crit well below 0.9887 (target ≲ 0.95), enabling intervention-free tests. Optionally also a variant where B has 3 or 4 outcomes.

- **Difficulty:** 3.
- **Importance:** 3 (PRA/Quantum; relevant to the Chaves/Sciarrino experiments).
- **Novelty risk:** low-moderate. The arXiv API search "unrelated confounders" returns only the Aug-2026 experiment; "Evans scenario" returns only the two Lauand papers.
- **Probability:** 35%.

---

### S2-05 — Self-testing the maximal OCB violation (a first self-test of indefinite causal order)

**Question.** Liu & Chiribella proved `max p_OCB = (2+√2)/4` over all process matrices and instruments, in any dimension. Is the optimum unique up to local isometries on A_I, A_O, B_I, B_O, junk, and local pre/post-processing? Concretely: does every optimal (W, instruments) contain the qubit OCB process
`W_OCB = ¼[1 + (1/√2)(Z^{A_O}Z^{B_I} + Z^{A_I}X^{B_I}Z^{B_O})]`
with Pauli instruments? The robust version asks that ε-optimality imply O(√ε)-closeness.

**Closest known results.**
- Liu–Chiribella (arXiv:2403.02749) state this explicitly: "establish self-testing results for causal inequalities … determine whether the OCB process is the only quantum process (up to local transformations) that achieves the maximum violation."
- Related but different: network-device-independent certification of causal nonseparability (Dourdent, Abbott, Šupić, Branciard, arXiv:2308.12760).

**Gap.** There is no notion of, and no theorem for, self-testing of process matrices.

**Method.**
1. Fix the equivalence notion: local isometries and junk on each party's input/output spaces, plus classical relabelings.
2. Numerics: in LC's canonical-instrument SDP, verify uniqueness of the optimizer (strict complementarity) and compute a robustness curve.
3. Analytics: from the LC dual certificate (`ηC − M_I ≥ 0`, C ∈ Aff(NoSig)) extract the operator identities any optimal strategy must satisfy. The coincidence of the OCB value with the CHSH Tsirelson bound suggests reducing to CHSH rigidity through the measure-and-prepare structure of Alice's optimal instrument.
4. Fallback: rigidity of the optimal correlation, or self-testing within canonical instruments.

**Compute.** SDPs from 16×16 to 256×256.

**Positive route.** A new theorem (rigidity of ICO correlations) with robustness bounds.

- **Difficulty:** 4.
- **Importance:** 3–4 (Quantum / PRL if clean).
- **Novelty risk:** low. arXiv listings for "self-testing process matrix causal" and "causal inequality self-testing" found nothing.
- **Probability:** 15–20%.

---

### S2-06 — Exact real-QT value of the Renou et al. bilocal functional T

**Question.** Setting: the entanglement-swapping (bilocal) scenario with two independent sources and **real** Hilbert spaces.
- The functional is `T = Σ_b T_b`, where T_b is Bob-outcome-dependent variants of
  `CHSH3 = CHSH(1,2;1,2) + CHSH(1,3;3,4) + CHSH(2,3;5,6)`.
- Alice has 3 settings, Charlie 6, and Bob performs a 4-outcome Bell-state measurement (BSM).
- Complex QT reaches 6√2 ≈ 8.485. Real QT satisfies T ≤ 7.6605, obtained from an NPA-type relaxation at levels n_A = n_C = 2 (App. H of arXiv:2101.10873, Nature 600, 625 (2021)).
- Renou et al.: "**It remains open, whether this upper bound is tight.**"

Determine T_RQT exactly (matching real strategy plus a higher-level certificate). Optionally do the same for the improved functionals: Batle et al. 14.69 vs 18 (arXiv:2405.03013), and Yao et al. arXiv:2312.14547 (PRA 109, 012211).

**Closest known results.**
- Experiments beating 7.66: arXiv:2103.08123, arXiv:2111.15128, arXiv:2201.04177.
- No paper was found that computes the exact real value.
- Context: the falsifiability debate (arXiv:2603.19208) concerns the independence assumption, not this mathematical optimum.

**Gap.** [best real strategy, 7.6605]. The best real strategy still has to be computed. Natural real XZ-plane strategies are expected to land close to 7.66 (the scout's heuristic, unverified), so the gap may be tiny and closable.

**Method.**
1. Real seesaw: real symmetric states and projectors, local dimension up to 4–8.
2. Re-implement the App. H relaxation at level 2 and reproduce 7.6605. Then go to intermediate levels (e.g., "2+AC") or level 3, with symmetry reduction, using SCS/Clarabel.
3. If the bounds meet, extract a rational dual certificate.

**Compute.** Level 2 uses 4 PSD blocks of about 370×370 (monomial sets of size 10 for A and 37 for C): easy. Level 3 uses about 4114×4114 per block: heavy but feasible with symmetry and SCS in 32 GB. Intermediate levels are the practical choice.

**Positive route.** The first exact real-QT network Tsirelson bound, which also lowers the visibility needed in experiments.

- **Difficulty:** 3.
- **Importance:** 2–3 (PRA/Quantum; interest is dampened by the 2026 debate).
- **Novelty risk:** low-moderate. Checked the arXiv listings "real quantum theory" (19 hits) and "real complex entanglement swapping" (4 hits).
- **Probability:** 35%.

---

### S2-07 — Sharp GHZ-fidelity bound for triangle-LOSR states

**Question.** Determine `F* = max ⟨GHZ_3|ρ|GHZ_3⟩` over states ρ preparable in the triangle with bipartite sources, local operations and shared randomness (LOSR), with qubit outputs. The analogous question for the W state is secondary.

**Closest known results.** Neumann, Kondra, Hansenne, Weinbrenner, Kampermann, Gühne, Bruß, Wyderka (arXiv:2503.09473) prove **0.548 < F* < 0.618**:
- With two-qubit sources the optimum is `[5+4cos(2π/7)]/[12+4cos(2π/7)] ≈ 0.517`.
- Fidelity grows with source dimension and converges to ≈ 0.548 (tested up to 10-dimensional sources). Zhou et al. (arXiv:2503.09480, Commun. Phys. 2025) obtain 0.548048.
- The upper bound 0.618 comes from a Finner-inequality / measurement argument. The earlier inflation bound was (1+√3)/4 < 0.684 (Navascués, Wolfe, Rosset, Pozas-Kerstjens, arXiv:2002.02773, PRL 125, 240505 (2020)).

**Gap.** 0.548 to 0.618. The lower bound looks saturated, so decisive progress means a better upper bound (e.g., ≤ 0.56) or the exact value.

**Method.**
1. A fully-quantum-inflation SDP (arXiv:2501.12320), or a symmetric-extension / quantum-marginal relaxation, reduced by permutation and GHZ symmetries.
2. Refine the Neumann et al. analytic argument.
3. Independent inner check of 0.548 for d → ∞.

**Compute.** A naive (2,2,2) inflation on 12 qubits needs a 4096×4096 PSD variable, which is heavy. After symmetry reduction it may fit; uncertain.

- **Difficulty:** 4.
- **Importance:** 3.
- **Novelty risk:** moderate (active groups: Gühne/Bruß/Wyderka; Yu/Xu). Also related: Oleynik et al., arXiv:2606.21500 (multipartite sources, a different setting).
- **Probability:** 15%.

---

### S2-08 — Sharpening the shared-random-bit (SRB) critical visibility in the classical triangle

**Question.** For `p_v(a,b,c) = v·[a=b=c]/2 + (1−v)/8`, find the triangle-local threshold v*.

**Known.** 36.21% ≤ v* < 36.629%.
- The upper bound comes from Gitton & Renner (arXiv:2510.15143): a (3,3,4) inflation with exact certificate, "about one hour on a modern laptop". The previous bound, ≈37.72%, came from Pozas-Kerstjens et al., arXiv:2305.03745.
- The lower bound is an explicit classical model from Gisin et al. 2020, "Constraints on nonlocality in networks from no-signaling and independence" (ID unverified).

**Gap.** About 0.42 percentage points.

**Method.** Run fast-inflation at larger sizes, (3,4,4) and (4,4,4), with richer constraint sets. For the lower bound, optimize explicit local models (neural LHV nets, structured response functions, LPs at fixed latent distributions).

**Compute.** Laptop hours; RAM is the limit at (4,4,4).

- **Difficulty:** 2–3.
- **Importance:** 2 (a benchmark in classical causal inference; best as a methods paper or warm-up).
- **Novelty risk:** low (no 2026 follow-up found).
- **Probability:** 50% for some improvement; about 10% for closure.

---

### S2-09 — Sufficiency of the siblings-on-cycles criterion (Tselentis–Baumeler conjecture)

**Question.** Is every siblings-on-cycles (SOC) digraph the causal structure of some consistent (e.g., unitary) quantum process?

**Known.**
- Necessity is proven; sufficiency is conjectured. It is proven in a restricted setting (chordless SOC graphs) and supported numerically up to 6 nodes (Tselentis & Baumeler, arXiv:2210.12796, PRX Quantum 4, 040307 (2023)).
- The review arXiv:2606.19438 restates it as a conjecture, together with the open problem of characterizing multi-slot unitary processes.
- Related: Baumeler & Wolf, arXiv:2410.18735 (flows of causal structures; chordless ⇒ causal correlations).

**Gap.** SOC graphs with chords.

**Method.** Generalize the explicit model construction; look for chord-removing or graph-substitution gadgets that preserve consistency. Brute-force verification at 7 nodes is probably too large: about 8.8×10^8 unlabeled digraphs before SOC filtering (count from memory). Restrict to minimal chorded classes.

**Positive route.** A constructive proof for a large new class, or the full conjecture.

- **Difficulty:** 5.
- **Importance:** 4.
- **Novelty risk:** low-moderate.
- **Probability:** 10%.

---

### S2-10 — (Moonshot) Are complex numbers needed in the triangle network without inputs?

**Question.** Is there an input-free triangle distribution (e.g., EJM, which is built from complex tetrahedral states) that complex QT achieves but real QT with independent real sources cannot? Put differently: do real-QT quantum-inflation relaxations (real moment matrices invariant under source-wise partial transposition, as in App. H of arXiv:2101.10873) exclude a complex-QT triangle distribution?

**Known.** Every real-vs-complex separation found so far uses measurement inputs: bilocal (arXiv:2101.10873) and star networks (arXiv:2503.09724). No triangle or no-input study was found.

**Method.**
1. A cheap kill test: tester seesaw restricted to real symmetric testers, trying to reproduce EJM (the arXiv:2510.15143 distribution). If this succeeds, abandon the candidate.
2. If it fails, a real quantum inflation (NPA level 1–2 on a (2,2,2) inflation, 4 outcomes) with a custom partial-transpose constraint added to `inflation`. This is heavy: moment matrices of 10³–10⁴.

The positive result would also have to address the Hoffreumon–Woods independence critique.

- **Difficulty:** 5.
- **Importance:** 5 (complex numbers necessary with no measurement choices).
- **Novelty risk:** low.
- **Probability:** 5%.

---

### S2-11 — (Quick win, about 1 day) Minimal rank of process matrices: answers an open question in the June-2026 review

**Question.** Review arXiv:2606.19438 (footnote, Sec. III A): "It is an open question whether (allowing for different local input and output dimensions) there exist rank-one process matrices where all outputs are non-trivial."

**Scout's own derivation (not from the literature; needs careful checking).** Let W be any valid N-partite process on ⊗_i I_i O_i.
- **(a) Tr_I W = 1_O.** Normalization must hold for discard-and-prepare instruments, and product states span all operators.
- **(b) P W = 0, with P = ∏_i (1 − ₍O_i₎).** Here ₍X₎ denotes "trace out X and replace it with 1_X/d_X". To see this, apply P to `W = L_V(W)` and use (1 − ₍O₎)(1 − ₍O₎ + ₍IO₎) = 1 − ₍O₎ and (1 − ₍O₎)·₍IO₎ = 0.
- **Rank bound.** Write `W = Σ_{k≤r} |V_k⟩⟨V_k|` with `V_k = Σ_o |o⟩⊗v^k_o`, and set `M_o = [v^1_o … v^r_o]`.
  - Then (a) gives tr(M_o†M_{o'}) = δ_{oo'}.
  - And (b) gives M_o M_{o'}† = 0 whenever o and o' differ in every party's output coordinate.
  - The outputs o^{(j)} = (j,…,j), for j ≤ min_i d_{O_i}, give nonzero matrices with mutually orthogonal row spaces in C^r.
  - Hence **rank W ≥ min_i d_{O_i}**.
- **Tightness.** The bound is attained, when dimensions allow, by a causally ordered process with pure initial state, isometric links, and the smallest-output party last.
- **Corollary.** A rank-one process exists **iff** some party has a trivial output. This covers all input/output dimensions and answers the question in the negative.
- **Sanity check.** Random causally separable bipartite processes (d_I = 3, d_O = 2) and the OCB process satisfy ||PW|| = 0 and Tr_I W = 1_O numerically.

- **Difficulty:** 1.
- **Importance:** 2 (short note or appendix).
- **Probability** that it is correct, new and writable in a day: about 70%.

This is a no-go-flavoured sharp bound. It is useful as a bankable side result, not as the main target.

---

## 2. AVOID list (solved, closed, contested, or negative-leaning in 2023–2026)

1. **Existence of binary-output triangle quantum nonlocality** (and (2,2,3)/(2,2,4) cardinalities by embedding): solved by Don et al., arXiv:2605.00981 (May 2026).
2. **EJM triangle nonclassicality:** solved by Gitton & Renner, arXiv:2510.15143 (Oct 2025). The noise-robust EJM certificate is open but computationally out of reach on this hardware: the proof itself needed ~5 days × 12 cores × 50 GB at essentially zero noise, and noisy versions need larger inflations.
3. **Henson–Lal–Pusey ≤ 6-node gap classification:** closed by Khanna, Pusey, Colbeck, arXiv:2512.04058.
4. **Evans/UC existence of a gap:** solved by arXiv:2404.12790; experiment arXiv:2608.03552. Only its robustness remains (S2-04).
5. **OCB and LGYNI ICO maxima:** solved exactly in arXiv:2403.02749.
6. **Pure 3-qubit triangle compatibility:** classified by Smith, Wolfe, Spekkens, arXiv:2501.12320.
7. **Four-output triangle violation of the Finner inequality:** done by Girardin & Gisin, arXiv:2306.05922 (PRA 108, 042213 (2023)). **Post-quantum (boxworld) nonlocality in the binary triangle:** done by Pozas-Kerstjens et al., arXiv:2305.03745.
8. **"Minimal" network nonlocality scenario:** settled by arXiv:2605.00981. The UC scenario with interventions has been realized experimentally (arXiv:2608.03552).
9. **GYNI lower bounds by generic seesaw, d ≤ 8:** saturated at 0.6219 (arXiv:2606.20519). Do not repeat.
10. **ICO advantage for two-use unitary discrimination:** conjectured impossible by Bavaresco, Murao, Quintino (arXiv:2105.13369). This would be counterexample hunting, and QC-QCs cannot help for unitary discrimination (Abbott et al. 2024, per the review; ID unverified).
11. **ICO advantage for asymptotic channel discrimination (Stein exponent):** closed negatively by Zhu & Wang, arXiv:2609.30268 (Sep 2026). **ICO for group-action estimation:** no advantage, arXiv:2501.09312.
12. **Device-independent certification of the isolated quantum switch via fixed-order inequalities:** the k-cycle inequalities are unsuitable (Baumann, Baumeler, Tselentis, arXiv:2412.17551). The scout's quick argument (unverified) suggests any such inequality fails when P is non-adaptive and F is the global future. Tracing F out leaves a causally separable A–B process, and F cannot signal, so the correlations lie in "F-last causal" = classical-with-non-adaptive-P. Likely negative.
13. **Real vs complex under indefinite causal order:** the claim in arXiv:2605.30238 is under revision by its authors after they found a normalization issue. In flux; avoid.
14. **RQT falsifiability (foundational):** contested (arXiv:2603.19208, arXiv:2604.19482). An arbitrarily large gap is already shown (arXiv:2503.09724), as are partial independence (arXiv:2502.20102) and efficient tests (arXiv:2405.03013). Do not enter the interpretational debate.
15. **GHZ distribution with multipartite sources in LOSR networks:** optimal values obtained by Oleynik, Tariq, Chatzinotas, arXiv:2606.21500. **Graph-state preparation in LOSR networks:** no-go results already exist (arXiv:2208.12100, arXiv:2503.09473).
16. **Experimental device-independent indefinite causal order via the van der Lugt–Barrett–Chiribella inequality** (arXiv:2208.00719): done (arXiv:2506.16949, which measured 1.8427 vs a classical bound of 1.75; arXiv:2508.04643).
17. **Experimental "genuine" triangle nonlocality:** done with ML and conjectured inequalities (arXiv:2401.15428). Rigorous robust proofs are the open part (S2-02).

---

## 3. Top-3 recommendations

1. **S2-01 (GYNI Tsirelson bound).**
   - The problem is stated as open in a Nat. Commun. paper, a June-2026 review co-authored by Brukner, and a June-2026 follow-up.
   - The target is clean: any dimension-free bound below 0.7592.
   - The SDPs are tiny, so this is ideal for a laptop. The only competitor effort (GPU seesaw) attacks the other side of the gap.
   - Core IQOQI-Vienna topic.
   - Risk: it requires a genuinely new relaxation idea. Budget day 1 for reproduction and days 2–4 for the joint or block-moment relaxations.
2. **S2-02 together with S2-03 (binary-triangle robustness and analytic witness).**
   - A direct follow-up to the headline May-2026 result, with explicitly listed open items: robustness, analytic proof, full network nonlocality.
   - It is computationally feasible with symmetry-reduced level-2/3 inflation (~10^5 orbit variables), the tester seesaw, and exact-arithmetic certificates.
   - A single wider-window example or a first polynomial inequality would be publishable in PRL/Quantum.
   - Main risk: the original authors are active.
3. **S2-05 (self-testing the OCB maximum).**
   - This would be a new theorem type with no prior art found, closing an open problem stated by Liu–Chiribella.
   - The numerics are small. The analytic part is plausible because the OCB optimum coincides with CHSH's Tsirelson structure.
   - If it stalls, fall back to S2-04 (UC robustness, 35%) or S2-06 (exact real-QT bound, 35%). These have higher probability but lower importance.
   - Bank **S2-11** on day 0 as a short-note side result.

---

## 4. Search log (novelty checks)

- **WebSearch** (33 successful queries before the session-wide cap was hit). Topics:
  - binary triangle, Boreiri minimal example, EJM inflation 2025, noise-robust triangle 2026
  - Evans/Lauand, HLP remaining structures
  - Liu–Chiribella hierarchy, causal-inequality maximal violation 2025, GYNI 0.7592, hierarchy second level, block-moment relaxations
  - unitary-discrimination ICO, SOC conjecture (×2)
  - real-vs-complex networks, complex self-testing, real QT without inputs, Renou 7.66 tightness (×2)
  - Tavakoli et al. network review, activation of nonlocality, full network nonlocality
  - GHZ triangle fidelity (×4), fully quantum inflation
  - van der Lugt–Barrett–Chiribella (VBC) / DI switch (×2), quantum-switch channel discrimination 2026
  - QRF open problems, generic "open problem networks 2026"
- **WebFetch of arXiv abstract/HTML pages:**
  - 2605.00981, 2510.15143, 2311.02182, 2512.04058, 2404.12790, 2403.02749 (HTML)
  - 2606.20519 (abstract and HTML), 2605.30238, 2606.19438, 2503.09724, 2512.07160, 2603.19208, 2405.03013, 2604.19482
  - 2401.15428, 2501.08079, 2406.15587, 2503.16654, 2105.13369, 2210.12796, 2605.04981, 2410.18735
  - 2609.22998, 2607.15345, 2606.21500, 2503.09480, 2503.09473, 2002.02773, 2501.12320, 2609.11451, 2503.24213, 2405.08939, 2609.30268, 2312.14547
- **arXiv listing and search pages:** "real quantum theory" (19 hits), "triangle network nonlocality" (21 hits), "triangle network binary outputs", "self-testing process matrix causal", "causal inequality self-testing", "shared random bit triangle", "unitary inversion indefinite causal order", "real complex entanglement swapping", "Causal networks and freedom of choice".
- **arXiv API:** "causal inequality/inequalities" (48 hits, full list inspected), "Evans scenario", "unrelated confounders", id_list for 2412.17551, 2508.17075, 2512.23599. Later queries were rate-limited with HTTP 429.
- **PDFs read in full text:** 2510.15143, 2605.00981, 2606.19438 (review, 90 pp.), 2104.10700 (network review), 2105.13369, 2403.02749, 2404.12790, 2412.17551, 2101.10873, 2002.02773, 2503.09473.
