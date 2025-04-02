import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.panic_error_0x11

import Generated.erc20shim.ERC20Shim.Common.if_2792370840247009933_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_if_2792370840247009933 (s₀ s₉ : State) : Prop :=
  s₉.isOk ∧

  (--Case 1: No initial collision
    s₀.evm.hash_collision = false →
  (
    ( -- Case 1.1 : Reversion
      let s_evm := EVMState.mstore s₀.evm 0 (Fin.shiftLeft 1313373041 224)
      let s'_evm := EVMState.mstore s_evm 4 17
      preservesEvm s₀ s₉ ∧
      s'_evm.evm_revert 0 36  = s₉.evm ∧
      s₀["_1"]!! ≠ 0 ∧
      s₀.store = s₉.store ∧
      s₉.evm.hash_collision = false
    )
    ∨
    ( -- Case 1.2 : No Reversion
      preservesEvm s₀ s₉ ∧
      s₀["_1"]!! = 0 ∧
      s₀.store = s₉.store ∧
      s₉.evm.hash_collision = false
    )
    ∨
      -- Case 1.3 : Collision in function
      s₉.evm.hash_collision = true
  )
  )
  ∧
  (-- Case 2: existing initial collision
     s₀.evm.hash_collision = true →
    s₉.evm.hash_collision = true
  )

lemma if_2792370840247009933_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2792370840247009933_concrete_of_code s₀ s₉ →
  Spec A_if_2792370840247009933 s₀ s₉ := by


  unfold if_2792370840247009933_concrete_of_code A_if_2792370840247009933
  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  rintro hasFuel ⟨s, call_panic, code⟩

  generalize s0_all :
  (Ok evm₀ varstore₀) = s₀ at *

  unfold A_panic_error_0x11 at call_panic

  by_cases reversion : s₀["_1"]!! ≠ 0
  · clr_spec at call_panic

    obtain ⟨s_ok, s0_no_collision, s0_collision⟩ := call_panic
    by_cases collision_s0 : s₀.evm.hash_collision = false

    · split_ands
      · aesop
      · simp[collision_s0]
        simp[collision_s0] at s0_no_collision
        by_cases collision_s : s.evm.hash_collision = false
        · simp[collision_s] at s0_no_collision
          aesop
        · aesop
      · aesop
    · aesop
  · aesop

end

end ERC20Shim.Common
