import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_668760047301878650
import Generated.ERC20simple.ERC20Shim.checked_sub_uint256
import Generated.ERC20simple.ERC20Shim.checked_add_uint256

import Generated.ERC20simple.ERC20Shim.fun_transferFromSimple_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

def A_fun_transferFromSimple (var var_1 var_2 : Identifier) (var_from var_to var_value : Literal) (s₀ s₉ : State) : Prop :=
  let valid := var_value ≤ var_from ∧
               var_to ≤ var_to + var_value ∧
               var_from - var_value ≤ var_from
  ( valid → s₉ = s₀⟦var ↦ 1⟧⟦var_1 ↦ var_from - var_value⟧⟦var_2 ↦ var_to + var_value⟧) ∧
  (¬valid → s₉ = s₀⟦var ↦ 0⟧⟦var_1 ↦ var_from⟧⟦var_2 ↦ var_to⟧)

set_option maxHeartbeats 400000 in
lemma fun_transferFromSimple_abs_of_concrete {s₀ s₉ : State} {var var_1 var_2 var_from var_to var_value} :
  Spec (fun_transferFromSimple_concrete_of_code.1 var var_1 var_2 var_from var_to var_value) s₀ s₉ →
  Spec (A_fun_transferFromSimple var var_1 var_2 var_from var_to var_value) s₀ s₉ := by
  unfold fun_transferFromSimple_concrete_of_code 
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  rintro h ⟨s₁, ⟨ss, h₂⟩⟩
  clr_funargs at ss
  clr_varstore ss,
  rcases h₂ with ⟨s₂, ⟨hs₂, ⟨s₃, ⟨hs₃, rest⟩⟩⟩⟩
  apply Spec_ok_unfold at hs₂
  apply Spec_ok_unfold at ss
  unfold A_if_5295847412656974480 at ss
  clr_varstore ss,
  by_cases eq : (decide (var_from < var_value)).toUInt256 = 0
  · simp [eq] at ss
    have hss : State.isOk s₁ := by aesop
    apply Spec_ok_unfold at hs₃
    clr_varstore hs₂,
    clr_varstore hs₃,
    dsimp [A_checked_sub_uint256] at hs₂
    -- Here we're forced to consider overflow. 
    by_cases eq₁ : s₁["var_from"]!! < s₁["var_from"]!! - (s₁["var_value"]!!)
    · -- Underflow ocurred.
      -- Here I spec'd revert as `s.diverge` (i.e. set out of fuel), prolly not smart.
      sorry
    · -- No underflow.
      simp [eq₁] at hs₂
      have : State.isOk s₂ := by aesop
      dsimp [A_checked_add_uint256] at hs₃
      by_cases eq₂ : s₂["var_to"]!! + (s₂["var_value"]!!) < s₂["var_to"]!!
      · -- Overflow ocurred.
        -- Reverts????
        sorry
      · -- No overflow.
        simp [eq₂] at hs₃
        have : State.isOk s₃ := by aesop
        unfold A_fun_transferFromSimple
        intros valid
        -- The only case where valid. I think `eq` is actually "not". It's late.
        have isValid : valid := sorry
        refine' ⟨_, (absurd isValid ·)⟩
        simp [isValid]
        let s₄ := s₃⟦"expr_component_3"↦s₃["expr_12"]!!⟧⟦"var"↦s₃["expr_6"]!!⟧⟦"var_1"↦s₃["expr_9"]!!⟧⟦"var_2"↦s₃["expr_12"]!!⟧
        have hs₄ : 🧟(s₄) = s₄ := by aesop_spec
        have h₁s₄ : s₄.isOk := by aesop
        rw [hs₄] at rest
        simp [s₄] at rest
        have : ∃ evm varstore, s₃ = .Ok evm varstore := by aesop
        rcases this with ⟨evm, ⟨varstore, hx⟩⟩
        


        


  -- simp at hw₅
  -- clr_varstore hw₅,


  -- rw [←ss] at hw₂
  -- clr_varstore ss,

  
  
  -- clr_varstore hw₂,
  -- apply Spec_ok_unfold at hw₂

  -- -- clr_varstore
  -- clr_spec at ss
  -- clr_varstore
  -- rcases h₂ with ⟨h₃, ⟨h₄, h₅⟩⟩
  -- clr_spec at h₅
  
  sorry

end

end Generated.ERC20simple.ERC20Shim
