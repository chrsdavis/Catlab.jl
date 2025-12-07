module Optics

# Simple monoidal "Set" category for testing

"""
    SimpleMonoidal()

A tiny stand-in for a monoidal category of sets and functions.

- Objects are just Julia types.
- Morphisms are just Julia functions.
- Tensor on objects is `(X, Y) ↦ Tuple{X,Y}`.
- Tensor on morphisms is pointwise product: `(f ⊗ g)(x,y) = (f(x), g(y))`.
- Unit object is `Nothing`, and we cheat by treating unitors as identity.
"""
struct SimpleMonoidal
end

# Tensor on objects and unit
tensor_obj(::SimpleMonoidal, ::Type{X}, ::Type{Y}) where {X,Y} = Tuple{X,Y}
monoidal_unit(::SimpleMonoidal) = Nothing

# Tensor on morphisms: (f : X→X', g : Y→Y') ↦ (x,y) ↦ (f(x), g(y))
tensor(::SimpleMonoidal, f::F, g::G) where {F,G} = (x, y) -> (f(x), g(y))

# Unitors: pretend I⊗X = X and X⊗I = X, so unitors are identity.
right_unitor(::SimpleMonoidal, ::Type{X}) where {X} = (x::X) -> x
left_unitor(::SimpleMonoidal, ::Type{X})  where {X} = (x::X) -> x

# Associators for cartesian product:
# α : X × (Y × Z) → (X × Y) × Z  and α⁻¹ : (X × Y) × Z → X × (Y × Z)
assocr(::SimpleMonoidal) = (x, yz) -> begin
    y, z = yz
    ((x, y), z)
end

assocl(::SimpleMonoidal) = (xy, z) -> begin
    x, y = xy
    (x, (y, z))
end


# Generic optic type
"""
    Optic{C,S,A,T,B,M,F,G}

A generic optic in a (here: Set-like) monoidal category `C`.

In `Set` semantics:

- `S, A, T, B, M` are object types.
- `forward :: F` has type `S → (M, A)`.
- `backward :: G` has type `(M, B) → T`.
"""
struct Optic{C,S,A,T,B,M,F,G}
    C        :: C
    forward  :: F
    backward :: G
end


# id and comp of optics
"""
    id_optic(C, ::Type{S}, ::Type{T}) -> Optic

Identity optic on (S,T).

In Set-like semantics, we take residual M = `Nothing` and:

- forward : S → (Nothing, S)
- backward: (Nothing, T) → T
"""
function id_optic(C::SimpleMonoidal, ::Type{S}, ::Type{T}) where {S,T}
    forward  = (s::S) -> (nothing, s)
    backward = (_m, t::T) -> t

    return Optic{SimpleMonoidal,S,S,T,T,Nothing,
                 typeof(forward),typeof(backward)}(C, forward, backward)
end

"""
    compose_optic(o2, o1)

Compose optics:

- o1 : (S,T) → (A,B)
- o2 : (A,B) → (U,V)

to get:

- o2 ∘ o1 : (S,T) → (U,V)

Set-like semantics:

- residuals: M1, M2
- new residual: (M1, M2)
- forward(s)  = let (m1,a) = o1.forward(s); (m2,u) = o2.forward(a); ((m1,m2), u) end
- backward((m1,m2), v) = let b = o2.backward(m2, v); o1.backward(m1, b) end
"""
function compose_optic(o2::Optic{SimpleMonoidal,A,U,T2,B2,M2,F2,G2},
                       o1::Optic{SimpleMonoidal,S,A,T1,B1,M1,F1,G1}
                      ) where {S,A,U,T1,T2,B1,B2,M1,M2,F1,G1,F2,G2}
    C = o1.C
    @assert C === o2.C "Base categories must match"

    # Type of new residual
    M = Tuple{M1,M2}

    forward = let f1 = o1.forward, f2 = o2.forward
        function (s::S)
            (m1, a) = f1(s)
            (m2, u) = f2(a)
            ((m1, m2), u)
        end
    end

    backward = let b1 = o1.backward, b2 = o2.backward
        function (m, v::B2)
            m1, m2 = m
            b = b2(m2, v)   # :: B1
            b1(m1, b)       # :: T1
        end
    end

    return Optic{SimpleMonoidal,S,U,T1,B2,M,
                 typeof(forward),typeof(backward)}(C, forward, backward)
end


# Lenses
"""
    Lens{S,A,B,T,F,G}

Simple Set-like lens:

- `view   :: S → A`
- `update :: (S, B) → T`
"""
struct Lens{S,A,B,T,F,G}
    view   :: F  # S → A
    update :: G  # (S, B) → T
end

"""
    lens(view, update)

Convenience constructor with type inference (S,A,B,T are inferred from usage).
"""
lens(view::F, update::G) where {F,G} =
    Lens{Any,Any,Any,Any,F,G}(view, update)

"""
    lens_to_optic(C::SimpleMonoidal, L::Lens{S,A,B,T})

Embed a Lens into the generic Optic form, using residual M = S:

- forward(s)    = (s, view(s))      :: (S, A)
- backward(s,b) = update(s, b)      :: T
"""
function lens_to_optic(C::SimpleMonoidal,
                       L::Lens{S,A,B,T,F,G}) where {S,A,B,T,F,G}
    forward  = (s::S) -> (s, L.view(s))
    backward = (m::S, b::B) -> L.update(m, b)

    return Optic{SimpleMonoidal,S,A,T,B,S,
                 typeof(forward),typeof(backward)}(C, forward, backward)
end


# test
"""
    example()

Run a small example demonstrating:

- building a Lens on the first component of a pair (Int, String),
- turning it into an Optic,
- using its forward/backward,
- composing it with itself as an Optic.
"""
function example()
    C = SimpleMonoidal()

    # State type S = (Int, String), focus on A = Int
    S = Tuple{Int,String}
    A = Int
    B = Int    # updates with an Int
    T = S      # put returns a new state of the same type

    # view : (Int, String) → Int
    view = s -> s[1]

    # update : ( (Int, String), Int ) → (Int, String)
    update = (s, b::Int) -> (b, s[2])

    L = Lens{S,A,B,T,typeof(view),typeof(update)}(view, update)

    println("Lens view((1, \"hi\"))       = ", L.view((1, "hi")))
    println("Lens update((1, \"hi\"), 10) = ", L.update((1, "hi"), 10))

    O = lens_to_optic(C, L)

    # Use optic forward/backward
    s0 = (1, "hello")
    (m, a) = O.forward(s0)
    println("\nOptic forward((1, \"hello\")) gives residual M, focus A:")
    println("  M = ", m, ", A = ", a)

    s1 = O.backward(m, 42)
    println("Optic backward(M, 42) gives new state T:")
    println("  T = ", s1)

    # Compose the lens-optic with identity on its focus type A
    idA = id_optic(C, A, A)
    O2  = compose_optic(idA, O)  # id ∘ O, still (S,S) → (A,A)

    (m2, a2) = O2.forward(s0)
    println("\nComposed optic (id ∘ O) forward((1,\"hello\")):")
    println("  M2 = ", m2, ", A2 = ", a2)

    s2 = O2.backward(m2, 100)
    println("Composed optic (id ∘ O) backward(M2, 100):")
    println("  T2 = ", s2)

    return nothing
end

end # module
