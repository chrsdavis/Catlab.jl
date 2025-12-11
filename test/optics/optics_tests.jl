using Catlab, Test
import Catlab.Theories: @present, @program

@testset "Optics" begin

    include("../optics/Optics.jl")
    include("../optics/Lens.jl")
    include("../optics/Prism.jl")
    
    @present TheorySet(FreeCartesianCategory) begin
        X::Ob
        Y::Ob
        Z::Ob
        f::Hom(X, Y)
        g::Hom(Y, Z)
        h::Hom(Z, X)
    end
    
    @testset "Generic Optics" begin
        S = TheorySet[:X]
        T = TheorySet[:Y]
        
        # Identity optic
        id_o = Optics.id_optic(S, T)
        @test dom(id_o) == Optics.OpticObject(S, T)
        @test codom(id_o) == Optics.OpticObject(S, T)
        
        # Simple optic
        M = TheorySet[:Z]
        forward = compose(TheorySet[:h], pair(id(M), TheorySet[:f]))
        backward = compose(proj1(M, T), TheorySet[:g])
        o = Optics.Optic(S, TheorySet[:Y], T, TheorySet[:Z], M, forward, backward)
        
        # Composition
        o2 = Optics.id_optic(T, T)
        o_comp = Optics.compose_optic(o2, o)
        @test o_comp.S == S
        @test o_comp.A == T
    end
    
    @testset "Lenses" begin
        # Create a lens
        view = TheorySet[:f]  # X → Y
        update = compose(pair(TheorySet[:h], id(TheorySet[:Z])), 
                        pair(TheorySet[:f], id(TheorySet[:Z])))  # X×Z → Y×Z
        
        L = Lens.lens(view, update)
        @test view(L) == view
        @test update(L) == update
        
        # Convert to optic
        o_lens = Lens.optic_lens(L)
        @test o_lens.M == TheorySet[:X]
        
        # Lens laws
        laws = Lens.lens_laws(L)
        @test all(values(laws))
    end
    
    @testset "Prisms" begin
        @present TheoryCocart(FreeCocartesianCategory) begin
            A::Ob
            B::Ob
            C::Ob
        end
        
        # In a cocartesian context
        preview = copair(id(TheoryCocart[:A]), id(TheoryCocart[:B]))  # A → A+B
        review = id(TheoryCocart[:B])  # B → B
        
        P = Prism.prism(preview, review)
        @test preview(P) == preview
        @test review(P) == review
        
        # Convert to optic
        o_prism = Prism.optic_prism(P)
        @test o_prism.M == TheoryCocart[:B]
    end
end