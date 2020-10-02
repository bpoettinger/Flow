theory Flow
imports
    Chain
    Alternating
    Endomorphism
    Pigeonhole

    Flow_Graph
    Flow_Interface
    Flow_Base
    Flow_Extensions
    Flow_Footprint

    FF
    Pip_Shared
    Pip_Release
    Pip_Acquire
    Pip_Invariant
    Pip_Example

    Approximations
    Edge_Local
    Nilpotent
    Effectively_Acyclic
    Effectively_Acyclic_Equal_Capacity
    Effectively_Acyclic_Switch_Worlds
    Effectively_Acyclic_Sourced_Path
    Effectively_Acyclic_Approximations
    Effectively_Acyclic_Uniqueness
    (* unfortunatelly there is a sorry in there due to complications with type classes;
       fixing this issue probably requires some refactoring of existing theories,
       e.g. Endomorphisms*)
    (*Effectively_Acyclic_Maintain_Counter_Example*)
    Effectively_Acyclic_Maintain
begin
end
