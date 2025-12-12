module TestOpticsBasic

using Test

using Catlab.Theories
using Catlab.Optics

@testset "Identity optic" begin
  # Use the monoidal unit as a concrete ObExpr so we don't depend
  # on any particular @present-ed theory.
  S = munit()
  T = munit()

  o = id_optic(S, T)

  # Basic shape checks
  @test isa(o, Optic)
  @test dom(o) == OpticObject(S, T)
  @test codom(o) == OpticObject(S, T)

  # Accessor helpers
  @test source(o)   == S
  @test focus(o)    == S   # id_optic(S,T) uses (S,S) → (T,T)
  @test target(o)   == T
  @test update(o)   == T
  @test residual(o) == munit()
end

@testset "Manual optic construction" begin
  # Build an optic with a nontrivial residual object M and check
  # that the type-checked constructor accepts it and the fields
  # are wired as expected.
  M = munit()
  S = munit()
  A = munit()
  B = munit()

  MB = M ⊗ B
  T  = MB

  forward  = id(S)    # S → S
  backward = id(MB)   # M ⊗ B → M ⊗ B

  o = Optic(S, A, T, B, M, forward, backward)

  @test isa(o, Optic)

  # Stored fields
  @test source(o)   == S
  @test focus(o)    == A
  @test target(o)   == T
  @test update(o)   == B
  @test residual(o) == M

  # Domain/codomain in the optic category
  @test dom(o)   == OpticObject(S, T)
  @test codom(o) == OpticObject(A, B)
end

@testset "OpticCategory identity and composition" begin
  # Note: OpticCategory currently ignores the concrete base category
  # in its id/compose definitions, so we can pass `nothing` here.
  OC = OpticCategory(nothing)

  S = munit()
  T = munit()

  o_id = id_optic(S, T)
  X = dom(o_id)

  # Category identity should agree with id_optic
  @test id(OC, X) isa Optic
  @test dom(id(OC, X))   == dom(o_id)
  @test codom(id(OC, X)) == codom(o_id)

  # Compose the identity with itself; shapes should be preserved
  o_comp = compose(OC, o_id, o_id)

  @test dom(o_comp)   == dom(o_id)
  @test codom(o_comp) == codom(o_id)
  @test residual(o_comp) == munit()

  # Direct optic-level composition should match the category-level one
  o_comp2 = compose_optic(o_id, o_id)

  @test dom(o_comp2)   == dom(o_id)
  @test codom(o_comp2) == codom(o_id)
  @test residual(o_comp2) == residual(o_comp)
end

end # module
