import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.update_byte_slice_shift_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

def A_update_byte_slice_shift (result : Identifier) (value toInsert : Literal) (s₀ s₉ : State) : Prop :=
  s₉.isOk ∧

  (--Case 1: No initial collision
    s₀.evm.hash_collision = false →
    (
    -- Case 1.1 : collision in function
      (
        let s := s₀⟦result ↦ toInsert⟧
        s₀.evm = s₉.evm ∧
        s.store = s₉.store
      )
    ∨
    -- Case 1.2 : Collision in function
    s₉.evm.hash_collision = true
    )
  )
  ∧
  (-- Case 2: existing initial collision
     s₀.evm.hash_collision = true →
    s₉.evm.hash_collision = true
  )

lemma update_byte_slice_shift_abs_of_concrete {s₀ s₉ : State} {result value toInsert} :
  Spec (update_byte_slice_shift_concrete_of_code.1 result value toInsert) s₀ s₉ →
  Spec (A_update_byte_slice_shift result value toInsert) s₀ s₉ := by
  unfold update_byte_slice_shift_concrete_of_code A_update_byte_slice_shift
  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs
  clr_varstore,
  rintro hasFuel code
  generalize s_inhabited_all :
  (Ok evm₀
  Inhabited.default⟦"toInsert"↦toInsert⟧⟦"value"↦value⟧⟦"toInsert"↦toInsert⟧⟦"result"↦toInsert⟧)
  = s_inhab at *

  generalize s0_all :
  (Ok evm₀ varstore₀) = s₀ at *

  unfold reviveJump at code
  simp [←s_inhabited_all, ←s0_all] at code
  unfold State.insert at code
  simp at code

  by_cases no_collision : s₀.evm.hash_collision = false

  · split_ands
    · aesop
    · simp [no_collision]
      left
      split_ands
      · rw [←s0_all, ←code]
        aesop
      · aesop
    · aesop
  · aesop

end

end Generated.erc20shim.ERC20Shim
