import Mathlib.Data.Nat.Basic

namespace Project

class GroupSet (G : Type) where
  unit : G 
  mul : G → G → G 
  inv : G → G 
  power_mul : G → ℕ → G
            --g₀^n = g
             
class Group (G : Type) extends GroupSet G where
  mul_unit : ∀ g, mul g unit = g
  unit_mul : ∀ g, mul unit g = g
  mul_inv : ∀ g, mul g (inv g) = unit
  inv_mul : ∀ g, mul (inv g) g = unit
  powers_add : ∀ (g : G) (a b : ℕ), mul (power_mul g a) (power_mul g b) = power_mul g (a + b) 
                    -- g^a * g^b = g^(a+b)

def power_mul {Gr : Group G} (g : G) (n : ℕ) : G :=
  match n with
  | 0 => Gr.unit
  | n + 1 => Gr.mul g (Gr.power_mul g n)

#check power_mul  
-- both of the above are taken from your code in 'Struct.lean' modified to allow powers

class AbelianGroup (G : Type) extends Group G where
  mul_comm : ∀ g₁ g₂, mul g₁ g₂ = mul g₂ g₁ 
              -- g₁g₂ = g₂g₁

class CyclicGroup (G : Type) extends Group G where
  powerlaw : ∀ g, ∃ n : ℕ, power_mul unit n = g
              -- e^n = g

theorem Cyclic_Implies_Abelian : CyclicGroup G → AbelianGroup G := by
    -- If there's an issue constructing an instance of AbelianGroup G, then I'll just do 
    -- CyclicGroup G → mul_comm or something like it
  intro p
  have h := p.powerlaw
  have mul_comm : ∀ g₁ g₂ : G, p.mul g₁ g₂ = p.mul g₂ g₁ := by 
    intro g₁ g₂
    have h₁ : ∃ n, p.power_mul p.unit n = g₁ := by
      apply h g₁
    have h₂ : ∃ n, p.power_mul p.unit n = g₂ := by
      apply h g₂
    have ⟨n₁,h₁'⟩ := h₁
       -- this is n₁ such that unit^n₁ = g₁, unclear if let or have is better
       -- I believe I want to call this the "witness" of h₁
    have ⟨n₂,h₂'⟩ := h₂ -- this is n₂ such that unit^n₂ = g₂
    calc
      p.mul g₁ g₂ = p.mul (p.power_mul p.unit n₁) g₂ := by rw[h₁']
      _ = p.mul (p.power_mul p.unit n₁) (p.power_mul p.unit n₂) := by rw[h₂']
      _ = p.power_mul p.unit (n₁ + n₂) := by rw[p.powers_add]
      _ = p.power_mul p.unit (n₂ + n₁) := by rw[Nat.add_comm]
      _ = p.mul (p.power_mul p.unit n₂) (p.power_mul p.unit n₁) := by rw [p.powers_add]
      _ = p.mul g₂ g₁ := by rw[h₁',h₂']
  apply AbelianGroup.mk 
    mul_comm
