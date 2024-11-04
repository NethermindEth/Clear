import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.10.0"

package «clear» {
  leanOptions := #[⟨`autoImplicit, false⟩]
}

lean_lib «Clear» {
  -- add any library configuration options here
}

lean_lib «Generated» {
  -- add any library configuration options here
}

lean_lib «All» {
  -- add any library configuration options here
}

@[default_target]
lean_lib «Main» {
  -- add any library configuration options here
}
