module OpticsTests

using Test
using Catlab
using Catlab.Theories
using Catlab.Optics

#
# Build a tiny free symmetric monoidal syntax just for testing.
# This gives us concrete ObExpr / HomExpr with ⊗, munit, id, compose, etc.
#
@syntax TestSMC{ObExpr,HomExpr} SymmetricMonoidalCategory begin end

# Some objects in the test SMC
const S   = Ob(TestSMC.Ob, :S)
const A   = Ob(TestSMC.Ob, :A)
const U   = Ob(TestSMC.Ob, :U)
const T₁  = Ob(TestSMC.Ob, :T₁)
const T₂  = Ob(TestSMC.Ob, :T₂)
const B   = Ob(TestSMC.Ob, :B)
const M₁  = Ob(TestSMC.Ob, :M₁)
const M₂  = Ob(TestSMC.Ob, :M₂)

# Some morphisms with the right types
const l₁ = Hom(:l₁, S,  M₁ ⊗ A)      # S  → M₁ ⊗ A
const l₂ = Hom(:l₂, A,  M₂ ⊗ U)      # A  → M₂ ⊗ U
const r₁ = Hom(:r₁, M₁ ⊗ B, T₁)      # M₁ ⊗ B → T₁
const r₂ = Hom(:r₂, M₂ ⊗ B, T₂)      # M₂ ⊗ B → T₂

@testset "Optics: core constructors and category interface" begin
    # --- Basic constructor / field sanity ---
    o₁ = Optic(S, A, T₁, B, M₁, l₁, r₁)
    o₂ = Optic(A, U, T₂, B, M₂, l₂, r₂)

    @test o₁.S === S
    @test o₁.A === A
    @test o₁.T === T₁
    @test o₁.B === B
    @test o₁.M === M₁
    @test o₁.forward === l₁
    @test o₁.backward === r₁

    # --- Identity optic ---
    oid = id_optic(S, T₁)
    I   = munit()

    @test oid.S === S
    @test oid.A === S          # (S,T₁) → (S,T₁)
    @test oid.T === T₁
    @test oid.B === T₁
    @test oid.M === I
    @test oid.forward == id(S)
    @test oid.backward == id(T₁)

    # --- Composition in the optic category ---
    o_comp = compose_optic(o₂, o₁)

    # Domain/codomain objects should behave like a category
    @test dom(o₁) == dom(o_comp)
    @test codom(o₂) == codom(o_comp)

    # Residual should be tensor of residuals
    @test o_comp.M == (M₁ ⊗ M₂)

    # --- Category interface via OpticCategory / OpticObject ---
    OC = OpticCategory(TestSMC)

    X = dom(o₁)
    Y = codom(o₂)

    idX = id(OC, X)
    @test dom(idX) == X
    @test codom(idX) == X

    # compose dispatched through the category interface
    o_comp2 = compose(OC, o₂, o₁)

    @test dom(o_comp2) == dom(o₁)
    @test codom(o_comp2) == codom(o₂)
    @test o_comp2.M == (M₁ ⊗ M₂)
end

end # module
