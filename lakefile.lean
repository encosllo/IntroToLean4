import Lake
open Lake DSL

package «lean4» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «a03Quantifiers» {
  srcDir := "Intro"
}
lean_lib «a05Functions» {
  srcDir := "Intro"
}
lean_lib «a06NaturalNumbers» {
  srcDir := "Intro"
}
lean_lib «a07Choice» {
  srcDir := "Intro"
}
lean_lib «a08Subtypes» {
  srcDir := "Intro"
}
lean_lib «a09Relations» {
  srcDir := "Intro"
}
lean_lib «a10Equivalence» {
  srcDir := "Intro"
}
lean_lib «a11Orders» {
  srcDir := "Intro"
}
lean_lib «a12EmptyUnit» {
  srcDir := "Intro"
}

require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"
