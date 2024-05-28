import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"aae9d296f859fb97923157dc9ae60fbaf718af8a"

package «clear» {
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`DautoImplicit, false⟩]
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
