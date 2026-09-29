import GYNIUpper.LuedersNormalForm

/-!
# Axioms of the Lüders normal form (Lemma 1 of the GYNI upper-bound proof)

Expected output for each theorem: `[propext, Classical.choice, Quot.sound]`.

The last command checks that the statements of the two main theorems, and the definitions that
these statements use, refer only to the standard `Matrix` operations: no constant of the type copy
`CStarMatrix` (whose multiplication is a default instance of `HMul`) occurs. Expected output:
`CStarMatrix constants: #[]`.
-/

#print axioms GYNIUpper.lueders_normal_form
#print axioms GYNIUpper.lueders_normal_form_choi
#print axioms GYNIUpper.luedersProcess_spec
#print axioms GYNIUpper.isInstrument_luedersInstr
#print axioms GYNIUpper.luedersInstr_eq_choiMatrix

open Lean Meta in
#eval show MetaM Unit from do
  let stmts := [``GYNIUpper.lueders_normal_form, ``GYNIUpper.lueders_normal_form_choi]
  let defs := [``GYNIUpper.luedersInstr, ``GYNIUpper.krausChoi, ``GYNIUpper.luedersKraus,
    ``GYNIUpper.IsProjFamily, ``GYNIUpper.choiMatrix, ``GYNIUpper.registerProj,
    ``GYNIProof.IsProcess, ``GYNIProof.IsInstrument, ``GYNIProof.IsCPTP, ``GYNIProof.prob,
    ``GYNIProof.gyniValue, ``GYNIProof.ptraceOut]
  let mut used : Array Name := #[]
  for n in stmts do
    used := used ++ (← getConstInfo n).type.getUsedConstants
  for n in defs do
    let ci ← getConstInfo n
    used := used ++ ci.type.getUsedConstants
    if let some v := ci.value? then
      used := used ++ v.getUsedConstants
  let bad := used.filter fun c => (`CStarMatrix).isPrefixOf c
  logInfo m!"CStarMatrix constants: {bad}"
