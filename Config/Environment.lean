import Lean.Elab.Command

open Lean Elab Command

def simpLems : Array Name := #[
  `ne_eq,
  -- `simp` lemmas which interact confusingly with `field_simp`
  `add_sub_cancel_right, `add_tsub_cancel_right, `sub_add_cancel, `add_sub_add_right_eq_sub,
  `sub_add_cancel_right
  ]

/-- Configure the environment with the right attributes for the geometry lectures: erase some
inconvenient simp lemmas. -/
elab "lftcm_init" : command => liftCoreM do
  let attrState := attributeExtension.getState (← getEnv)
  let some simpAttr := attrState.map.get? `simp | throwError "simp tactic not found"
  for declName in simpLems do
    try
      simpAttr.erase declName
    catch _ =>
      -- This consumes all types of errors, rather than just existence ones,
      -- but there does not appear to be a better general way to achieve this
      pure ()
