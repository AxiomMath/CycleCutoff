/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public meta import Lean

/-!
# The `cycle_cutoff` tag attribute

The attribute `@[cycle_cutoff "TAG"]` labels a declaration with the name `TAG` of the
mathematical statement it realizes. A statement may be realized jointly by several
declarations, each carrying the same label. The attribute has no effect on elaboration.
-/

public meta section

open Lean

/-- `@[cycle_cutoff "TAG"]` labels a declaration with the name of the mathematical statement it
realizes. -/
syntax (name := cycle_cutoff) "cycle_cutoff " str : attr

initialize Lean.registerBuiltinAttribute {
  name  := `cycle_cutoff
  descr := "tag of the mathematical statement realized by this declaration"
  add   := fun _ _ _ => pure ()
}

end
