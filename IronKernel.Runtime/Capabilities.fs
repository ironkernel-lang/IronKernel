namespace IronKernel

module Capabilities =

    open Ast

    let forProfile = function
        | Minimal -> Set.empty
        | Safe -> Set.singleton (GeneratedClr "safe")
        | Unrestricted -> allHostCapabilities

    let ofEnvironment = function
        | Environment record -> record.capabilities
        | _ -> Set.empty

    let has capability environment =
        Set.contains capability (ofEnvironment environment)

    let require capability environment =
        if has capability environment then Choice2Of2 ()
        else Choice1Of2 (CapabilityDenied(sprintf "missing capability %A" capability))

    let intersect sets =
        match sets with
        | [] -> Set.empty
        | first :: rest -> List.fold Set.intersect first rest

    let attenuate allowed capabilities =
        Set.intersect capabilities allowed
