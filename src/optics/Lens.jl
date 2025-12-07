# TODO: make Lenses instances of Optics?

# TODO: replace Any with catlab morphism type

struct Lens{C,S,A,T,B}
    C      :: C
    view   :: Any   # S → A
    update :: Any   # S × B → T
end
