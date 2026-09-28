# Containment tests of the certified relaxation (independent code)

These scripts test the relaxation that the certificate certifies, **level-8 rows included**. The code is independent of `src/mc2.py` and `src/mc3.py`; `mc3.build` is only read for its row list, objective and basis labels.

1. Generate strategies:
   - random general strategies, with 3–4 Kraus operators per outcome, OCB processes and mixtures, separable, degenerate and unequal-dimension cases;
   - seesaw strategies;
   - the published J=3 and J=4 strategies.
2. Apply our own implementation of Lemma 1 (Lüders normal form).
3. Build the moment matrix and its average over the GYNI group.
4. Check every row of `mc3.build(L, sym=True)`, check PSD, and check that the objective equals I_GYNI, for L = 2..8.

```bash
cd tests
python audit_contain.py --levels 2 3 4 --seeds 1 2     # random general strategies (L=8 also possible, slower)
python audit_jstrat.py                                  # the published J=3 / J=4 strategies at every level
python audit_lemma1_explicit.py                         # explicit W~ = (Phi_A^+ (x) Phi_B^+)(W): validity + statistics
python audit_lueders_direct.py                          # generic Lueders-form processes, incl. degenerate projector pairs
python audit_cert_link.py                               # beta - I = sum_k <Y_k, G_k> for the J=4 strategy
```
Our results are in `logs/`. Every residual is at rounding level: at most 2.1e-14 on rows, and eigenvalues no lower than −9.4e-15 relative to ‖Γ‖. The negative controls all fail as they should: a forbidden term, a wrong symmetry map, idempotent instead of dihedral words, and J† instead of Jᵀ. Summary: `../AUDIT_REPORT.md`. Running these may create a `__pycache__/` folder in `src/`; it is gitignored.
