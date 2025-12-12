using Test
using Catlab

# TODO: finish this later
@testset "Optics basics" begin
    C = ??? # choose a simple SMC from Catlab, e.g. FinVect or similar
    S = ...
    T = ...
    A = ...
    B = ...
    M = ...
    f = ...  # HomExpr S → M ⊗ A
    g = ...  # HomExpr M ⊗ B → T

    o = Optic(S, A, T, B, M, f, g)

    @test dom(o) == OpticObject(S, T)
    @test codom(o) == OpticObject(A, B)

    idST = id_optic(S, T)
    comp = compose_optic(idST, o)
    # These should be equal up to some notion of equality on HomExpr
    @test comp.S == o.S
    @test comp.A == o.A
    @test comp.forward == o.forward  # or some NormalForm(comp.forward) == ...
end
