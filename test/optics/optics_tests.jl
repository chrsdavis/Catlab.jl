using Test
using Catlab
using Catlab.Optics

@testset "Optics: basic structure" begin

    # Example: construct a trivial optic and check dom/codom types
    # (adapt this to actual constructors)
    S = ...  # some ObExpr from Theories
    A = ...
    T = ...
    B = ...
    M = ...

    # Suppose you have a constructor `optic(S, A, T, B, M, forward, backward)`
    o = optic(S, A, T, B, M, forward, backward)

    @test dom(o) == OpticObject(S, T)
    @test codom(o) == OpticObject(A, B)

    # Identity and composition laws in OpticCategory
    OC = OpticCategory()
    X  = OpticObject(S, T)
    id_o = id(OC, X)
    @test dom(id_o) == X
    @test codom(id_o) == X

    # Check associativity / unit up to whatever equality notion we;re using
    # (e.g. syntactic equality in HomExpr, or a helper `equal_hom`).
end
